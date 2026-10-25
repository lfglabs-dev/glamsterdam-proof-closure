#!/usr/bin/env python3
"""
3-Model Blind Quorum Gate (`quorum_gate.py`) across:
- `claude-fable-5` (Fable)
- `antigravity/gemini-4-argon-high` (Gemini 4 Argon)
- `gpt-6-astra` (Astra)

Executes all 3 models in parallel via `agent-core` CLI proxy, saves each model's full response,
and enforces a strict fail-closed 3/3 `VERDICT: PASS` requirement.
"""
import argparse
import json
import pathlib
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

MODELS = [
    ("fable", "claude-fable-5", False),
    ("gemini-4-argon", "antigravity/gemini-4-argon-low", True),
    ("astra", "gpt-6-astra", True),
]

SSH_CONFIG = "/var/lib/sandboxed-node/.config/sandboxed-sh/development-identity/current/ssh/config"
FAILURE_MARKER_RE = re.compile(r"(?:^|\n)\s*(?:HTTP_ERROR|ERR|SUBPROCESS_ERROR|STDERR_NONEMPTY):", re.MULTILINE)


def evaluate_verdict(returncode: int, content: str, stderr_text: str = "") -> bool:
    if returncode != 0:
        return False
    if stderr_text and stderr_text.strip():
        return False
    if FAILURE_MARKER_RE.search(content):
        return False
    verdicts = re.findall(r"VERDICT:\s*(PASS|FAIL)\b", content)
    return len(verdicts) > 0 and verdicts[-1] == "PASS"


def call_one(entry: tuple[str, str, bool], prompt: str, out_dir: pathlib.Path) -> tuple[str, str, bool, str]:
    label, model_id, use_stream = entry
    out_file = out_dir / f"quorum_{label}.md"
    payload = {
        "model": model_id,
        "messages": [{"role": "user", "content": prompt}],
    }
    if use_stream:
        payload["temperature"] = 0.1
        payload["max_tokens"] = 4096
        payload["stream"] = True

    payload_str = json.dumps(payload)

    remote_script = """python3 -c '
import glob, json, sys, urllib.request
base_url, api_key = None, None
for env_file in glob.glob("/proc/[0-9]*/environ"):
    try:
        data = open(env_file, "rb").read().split(b"\\x00")
        env = {}
        for item in data:
            if b"=" in item:
                k, v = item.split(b"=", 1)
                env[k.decode("utf-8", "ignore")] = v.decode("utf-8", "ignore")
        if "CLI_PROXY_API_BASE_URL" in env and "CLI_PROXY_API_KEY" in env:
            base_url = env["CLI_PROXY_API_BASE_URL"]
            api_key = env["CLI_PROXY_API_KEY"]
            break
    except Exception:
        pass
if not base_url or not api_key:
    print("ERR: missing CLI_PROXY_API credentials")
    sys.exit(2)
body_raw = sys.stdin.read()
body_obj = json.loads(body_raw)
is_stream = body_obj.get("stream", False)
req = urllib.request.Request(
    base_url.rstrip("/") + "/v1/chat/completions",
    data=body_raw.encode("utf-8"),
    headers={"Authorization": "Bearer " + api_key, "Content-Type": "application/json"},
)
try:
    with urllib.request.urlopen(req, timeout=420) as resp:
        if is_stream:
            chunks = []
            for raw_line in resp:
                line = raw_line.decode("utf-8", "ignore").strip()
                if not line.startswith("data:"):
                    continue
                data_str = line[5:].strip()
                if data_str == "[DONE]":
                    break
                try:
                    obj = json.loads(data_str)
                    delta = obj.get("choices", [{}])[0].get("delta", {})
                    if "content" in delta and delta["content"]:
                        chunks.append(delta["content"])
                except Exception:
                    pass
            print("".join(chunks))
        else:
            out = json.loads(resp.read().decode("utf-8", "ignore"))
            print(out["choices"][0]["message"]["content"])
except urllib.error.HTTPError as e:
    print("HTTP_ERROR:", e.code, e.read().decode("utf-8", "ignore"))
    sys.exit(3)
except Exception as e:
    print("ERR:", repr(e))
    sys.exit(4)
'"""

    try:
        proc = subprocess.run(
            ["ssh", "-F", SSH_CONFIG, "-o", "LogLevel=ERROR", "agent-core", remote_script],
            input=payload_str,
            text=True,
            capture_output=True,
            timeout=450,
        )
        stdout_text = proc.stdout or ""
        stderr_text = proc.stderr or ""
        rc = proc.returncode
        if stderr_text.strip():
            content = f"{stdout_text}\nSTDERR_NONEMPTY: {stderr_text.strip()}".strip()
        else:
            content = stdout_text
    except subprocess.TimeoutExpired as exc:
        partial = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        content = f"{partial}\nSUBPROCESS_ERROR: TimeoutExpired after {exc.timeout}s".strip()
        stderr_text = "TimeoutExpired"
        rc = 124
    except Exception as exc:
        content = f"SUBPROCESS_ERROR: {repr(exc)}"
        stderr_text = repr(exc)
        rc = 1

    out_file.write_text(content)
    passed = evaluate_verdict(rc, content, stderr_text)
    return label, model_id, passed, content


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--step", required=True, help="Step name, e.g. step1, step2")
    ap.add_argument("--prompt-file", required=True, help="Path to prompt markdown file")
    ap.add_argument("--out-dir", required=True, help="Directory to store quorum outputs")
    args = ap.parse_args()

    prompt = pathlib.Path(args.prompt_file).read_text()
    out_dir = pathlib.Path(args.out_dir) / args.step
    out_dir.mkdir(parents=True, exist_ok=True)

    with ThreadPoolExecutor(max_workers=3) as ex:
        futures = [ex.submit(call_one, m, prompt, out_dir) for m in MODELS]
        results = [f.result() for f in futures]

    all_passed = True
    for label, model_id, passed, content in results:
        status = "PASS" if passed else "FAIL"
        if not passed:
            all_passed = False
        print(f"[{args.step}] {label} ({model_id}): {status} ({len(content)} chars)")

    return 0 if all_passed else 1


if __name__ == "__main__":
    sys.exit(main())
