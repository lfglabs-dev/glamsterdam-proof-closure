"""Pinned type declarations feed a binary-only Lean SSZ codec."""
import ctypes
from functools import cache
import json
import re
import tarfile

import snappy
import ssz


@cache
def schema(typ):
    if issubclass(typ, ssz.Boolean):
        return {"kind": "bool"}
    if issubclass(typ, ssz.BaseUint):
        return {"kind": "uint", "n": typ.BITS // 8}
    if issubclass(typ, (ssz.ProgressiveContainer, ssz.Container)):
        return {"kind": "record", "fields": [schema(f.annotation) for f in typ.model_fields.values()],
                "active": getattr(typ, "ACTIVE_FIELDS", None)}
    for family, kind, mode in (
        (ssz.ByteVector, "bytes", "fixed"), (ssz.ByteList, "bytes", "bounded"),
        (ssz.BitVector, "bits", "fixed"), (ssz.BitList, "bits", "bounded"),
        (ssz.ProgressiveBitList, "bits", "progressive"), (ssz.Vector, "seq", "fixed"),
        (ssz.List, "seq", "bounded"), (ssz.ProgressiveList, "seq", "progressive"),
    ):
        if issubclass(typ, family):
            out = {"kind": kind, "mode": mode}
            if mode != "progressive":
                out["n"] = typ.LENGTH if mode == "fixed" else typ.LIMIT
            if kind == "seq":
                out["element"] = schema(typ.ELEMENT_TYPE)
            return out
    raise ValueError(f"unrecognized SSZ schema {typ}")


@cache
def wire_schema(typ):
    return json.dumps(schema(typ), separators=(",", ":")).encode()


def lean_root(lib, desc, data):
    ptr = lib.ssz_vector_root(desc, data, len(data))
    if not ptr:
        raise MemoryError("SSZ adapter allocation failed")
    try:
        return ctypes.string_at(ptr).decode()
    finally:
        lib.release_output(ptr)


def check_static(lib, spec, name, parts):
    _, _, _, typ, _, _ = name.split("/")
    desc = wire_schema(getattr(spec, typ))
    binary = snappy.decompress(parts["serialized.ssz_snappy"])
    # roots.yaml in this pinned format contains one named 32-byte hexadecimal root.
    match = re.fullmatch(rb"""\s*root:\s*['"]?0x([0-9a-fA-F]{64})['"]?\s*""", parts["roots.yaml"])
    if not match:
        raise ValueError("unexpected official roots.yaml")
    expected = match[1].decode().lower()
    actual = lean_root(lib, desc, binary)
    if actual != expected:
        raise ValueError(f"{typ}: expected root {expected}, Lean returned {actual}")
    return {"status": "full_pass", "evidence": "lean_binary_roundtrip_and_tree_root"}


def check_archive(lib, spec, path, selected, results):
    # Keep one SSZ fixture in memory. The release groups member files by case.
    active = None
    parts = {}

    def finish():
        if active is None:
            return
        if active in results:
            raise ValueError(f"noncontiguous SSZ case: {active}")
        try:
            results[active] = check_static(lib, spec, active, parts)
        except Exception as exc:
            results[active] = {"status": "failed", "error": repr(exc)}

    with tarfile.open(path, "r|gz") as tar:
        for member in tar:
            if not member.isfile():
                continue
            name, _, field = member.name.removeprefix("tests/").rpartition("/")
            if name not in selected:
                continue
            if name != active:
                finish()
                active, parts = name, {}
            if field in {"roots.yaml", "serialized.ssz_snappy"}:
                if field in parts:
                    raise ValueError(f"duplicate SSZ output part: {member.name}")
                parts[field] = tar.extractfile(member).read()
        finish()
    if not selected <= results.keys():
        raise ValueError("missing selected SSZ case")


def check_codec_controls(lib):
    # These malformed encodings are local controls; the official static corpus
    # contains valid encodings. They never contribute official case counts.
    malformed = [
        ("nonboolean scalar", {"kind": "bool"}, b"\x02"),
        ("unused bitvector padding", {"kind": "bits", "mode": "fixed", "n": 3}, b"\x08"),
        ("absent bitlist terminator", {"kind": "bits", "mode": "progressive"}, b"\x00"),
        ("offset inside the head", {"kind": "record", "active": None,
         "fields": [{"kind": "bytes", "mode": "bounded", "n": 8}]}, b"\x03\x00\x00\x00"),
    ]
    for name, desc, data in malformed:
        if not lean_root(lib, json.dumps(desc).encode(), data).startswith("error:"):
            raise AssertionError(f"malformed SSZ control accepted: {name}")
    # Equal packed bytes with different logical bit lengths must hash differently.
    desc = b'{"kind":"bits","mode":"progressive"}'
    a = lean_root(lib, desc, b"\x02")
    b = lean_root(lib, desc, b"\x04")
    if a.startswith("error:") or b.startswith("error:") or a == b:
        raise AssertionError("bit length mix-in control failed")
    return [name for name, _, _ in malformed] + ["different bit lengths produce different roots"]
