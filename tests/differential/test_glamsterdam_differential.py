#!/usr/bin/env python3
"""
Differential Test Suite ("Double Checks de Secours") for the Glamsterdam Formal Audit.

Directly loads and executes the canonical vendored upstream implementations from `vendor/upstreams/`
against the compiled Lean 4.31 C-ABI shared library (`.lake/build/libglamsterdam_cabi.so`):
1. `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`
   (`src/ethereum/forks/amsterdam/vm/gas.py`, `vm/instructions/storage.py`, `vm/instructions/system.py`)
2. `ethereum/consensus-specs` @ `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`,
   `specs/gloas/beacon-chain.md`)

Can be run via `pytest tests/differential/test_glamsterdam_differential.py` or directly via
`python3 tests/differential/test_glamsterdam_differential.py`.
"""
from __future__ import annotations

import ast
import ctypes
import dataclasses
import pathlib
import random
import re
import subprocess
from typing import Any, Callable, Final, List, Sequence, Tuple, final

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
SO_PATH = ROOT / ".lake" / "build" / "libglamsterdam_cabi.so"
VENDOR_EXEC = ROOT / "vendor" / "upstreams" / "execution_specs" / "src" / "ethereum" / "forks" / "amsterdam"
VENDOR_BEACON_MD = ROOT / "vendor" / "upstreams" / "consensus_specs" / "specs" / "gloas" / "beacon-chain.md"


def ensure_shared_lib() -> ctypes.CDLL:
    ir_dir = ROOT / ".lake" / "build" / "ir" / "Glamsterdam"
    c_files = sorted(ir_dir.rglob("*.c"))
    assert c_files, f"No generated Lean C IR files found under {ir_dir}; run `lake build` first."
    needs_build = not SO_PATH.exists() or any(
        c.stat().st_mtime > SO_PATH.stat().st_mtime for c in c_files
    )
    if needs_build:
        lean_prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        cmd = [
            "gcc",
            "-shared",
            "-fPIC",
            "-O3",
            f"-I{lean_prefix}/include",
            *[str(p) for p in c_files],
            f"-L{lean_prefix}/lib/lean",
            "-lleanshared",
            f"-Wl,-rpath,{lean_prefix}/lib/lean",
            "-o",
            str(SO_PATH),
        ]
        subprocess.run(cmd, check=True)
    lib = ctypes.CDLL(str(SO_PATH))

    # Configure signatures
    lib.glamsterdam_charge_gas_ok_cabi.argtypes = [ctypes.c_uint64] * 4
    lib.glamsterdam_charge_gas_ok_cabi.restype = ctypes.c_uint8

    lib.glamsterdam_charge_gas_left_cabi.argtypes = [ctypes.c_uint64] * 4
    lib.glamsterdam_charge_gas_left_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_charge_gas_reservoir_cabi.argtypes = [ctypes.c_uint64] * 4
    lib.glamsterdam_charge_gas_reservoir_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_eip8246_eth_conservation_cabi.argtypes = [ctypes.c_uint64] * 4
    lib.glamsterdam_eip8246_eth_conservation_cabi.restype = ctypes.c_uint8

    lib.glamsterdam_eip8246_selfdestruct_exec_gas_cabi.argtypes = [ctypes.c_uint64] * 3
    lib.glamsterdam_eip8246_selfdestruct_exec_gas_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_eip8246_selfdestruct_state_gas_cabi.argtypes = [ctypes.c_uint64] * 3
    lib.glamsterdam_eip8246_selfdestruct_state_gas_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_settle_gas_used_cabi.argtypes = [ctypes.c_uint64] * 6
    lib.glamsterdam_settle_gas_used_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_settle_exec_gas_used_cabi.argtypes = [ctypes.c_uint64] * 6
    lib.glamsterdam_settle_exec_gas_used_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_allocate_exec_gas_cabi.argtypes = [ctypes.c_uint64] * 2
    lib.glamsterdam_allocate_exec_gas_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_allocate_reservoir_cabi.argtypes = [ctypes.c_uint64] * 2
    lib.glamsterdam_allocate_reservoir_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_sstore_exec_cost_cabi.argtypes = [ctypes.c_uint64] * 4
    lib.glamsterdam_sstore_exec_cost_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_sstore_state_cost_cabi.argtypes = [ctypes.c_uint64] * 4
    lib.glamsterdam_sstore_state_cost_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_sstore_state_refund_cabi.argtypes = [ctypes.c_uint64] * 4
    lib.glamsterdam_sstore_state_refund_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_eip7732_can_cover_bid_cabi.argtypes = [ctypes.c_uint64] * 3
    lib.glamsterdam_eip7732_can_cover_bid_cabi.restype = ctypes.c_uint8

    lib.glamsterdam_eip7732_quorum_threshold_cabi.argtypes = [ctypes.c_uint64] * 2
    lib.glamsterdam_eip7732_quorum_threshold_cabi.restype = ctypes.c_uint64

    lib.glamsterdam_eip7732_can_builder_exit_cabi.argtypes = [ctypes.c_uint64] * 2
    lib.glamsterdam_eip7732_can_builder_exit_cabi.restype = ctypes.c_uint8

    return lib


# ---------------------------------------------------------------------------
# Direct AST Loader from `vendor/upstreams/execution_specs/` and `consensus_specs/`
# ---------------------------------------------------------------------------

class OutOfGasError(Exception):
    pass


class WriteInStaticContext(Exception):
    pass


def _extract_ast_nodes(py_path: pathlib.Path, target_names: set[str]) -> ast.Module:
    source = py_path.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(py_path))
    selected = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name in target_names
    ]
    missing = target_names - {n.name for n in selected}
    assert not missing, f"Missing AST nodes {missing} in {py_path}"
    mod = ast.Module(body=selected, type_ignores=[])
    ast.fix_missing_locations(mod)
    return mod


def load_vendored_execution_specs() -> dict[str, Any]:
    """
    Loads the exact AST definitions of `StateGasCosts`, `GasCosts`, `GasMeter`,
    `check_gas`, `charge_gas_from_meter`, `charge_gas`, `charge_state_gas_from_meter`,
    `charge_state_gas`, `commit_state_gas`, `restore_state_gas`, `restore_state_gas_to_entry`,
    `credit_state_gas_refund`, `repay_state_gas_spill`, `EvmGasAllocation`, `allocate_evm_gas`,
    `TransactionGasSettlement`, `settle_transaction_gas` from `vm/gas.py`, `sstore` from
    `vm/instructions/storage.py`, and `selfdestruct` from `vm/instructions/system.py`.
    """

    class _U256Int(int):
        def to_be_bytes32(self) -> bytes:
            return int(self).to_bytes(32, "big")

    @dataclasses.dataclass
    class IntrinsicGasCost:
        execution: int
        state: int = 0

    env: dict[str, Any] = {
        "dataclass": dataclasses.dataclass,
        "Final": Final,
        "List": List,
        "Tuple": Tuple,
        "final": final,
        "U64": int,
        "U256": _U256Int,
        "Uint": int,
        "ExecutionGas": int,
        "StateGas": int,
        "StateGasPerByte": int,
        "IntrinsicGasCost": IntrinsicGasCost,
        "OutOfGasError": OutOfGasError,
        "WriteInStaticContext": WriteInStaticContext,
        "GasAndRefund": lambda x: x,
        "StateGasAndRefund": lambda x: x,
        "evm_trace": lambda *args, **kwargs: None,
    }

    gas_targets = {
        "StateGasCosts",
        "GasCosts",
        "GasMeter",
        "check_gas",
        "charge_gas_from_meter",
        "charge_gas",
        "charge_state_gas_from_meter",
        "charge_state_gas",
        "commit_state_gas",
        "restore_state_gas",
        "restore_state_gas_to_entry",
        "credit_state_gas_refund",
        "repay_state_gas_spill",
        "EvmGasAllocation",
        "allocate_evm_gas",
        "TransactionGasSettlement",
        "settle_transaction_gas",
    }
    gas_mod = _extract_ast_nodes(VENDOR_EXEC / "vm" / "gas.py", gas_targets)
    exec(compile(gas_mod, str(VENDOR_EXEC / "vm" / "gas.py"), "exec"), env)

    # Load `sstore` (`vm/instructions/storage.py:68-162`), `selfdestruct` (`vm/instructions/system.py:706-779`),
    # and `move_ether` (`state_tracker.py:606-638`)
    storage_mod = _extract_ast_nodes(VENDOR_EXEC / "vm" / "instructions" / "storage.py", {"sstore"})
    system_mod = _extract_ast_nodes(VENDOR_EXEC / "vm" / "instructions" / "system.py", {"selfdestruct"})
    tracker_mod = _extract_ast_nodes(VENDOR_EXEC / "state_tracker.py", {"move_ether"})
    exec(compile(storage_mod, str(VENDOR_EXEC / "vm" / "instructions" / "storage.py"), "exec"), env)
    exec(compile(system_mod, str(VENDOR_EXEC / "vm" / "instructions" / "system.py"), "exec"), env)
    exec(compile(tracker_mod, str(VENDOR_EXEC / "state_tracker.py"), "exec"), env)
    return env


def load_vendored_gloas_specs() -> dict[str, Any]:
    """
    Extracts and executes the fenced Python definitions directly from
    `vendor/upstreams/consensus_specs/specs/gloas/beacon-chain.md`.
    """
    md_text = VENDOR_BEACON_MD.read_text(encoding="utf-8")
    code_blocks = re.findall(r"```python\n(.*?)```", md_text, flags=re.DOTALL)

    target_defs = (
        "def is_active_builder(",
        "def get_pending_balance_to_withdraw_for_builder(",
        "def can_builder_cover_bid(",
        "def get_builder_payment_quorum_threshold(",
        "def settle_builder_payment(",
        "def slash_validator(",
        "def process_builder_pending_payments(",
        "def apply_parent_execution_payload(",
    )

    @dataclasses.dataclass
    class BuilderPendingWithdrawal:
        fee_recipient: int = 0
        amount: int = 0
        builder_index: int = 0

    @dataclasses.dataclass
    class BuilderPendingPayment:
        weight: int = 0
        withdrawal: BuilderPendingWithdrawal = dataclasses.field(
            default_factory=BuilderPendingWithdrawal
        )
        proposer_index: int = 0

        @classmethod
        def empty(cls) -> "BuilderPendingPayment":
            return cls()

    env: dict[str, Any] = {
        "Any": Any,
        "Callable": Callable,
        "Sequence": Sequence,
        "Gwei": int,
        "Uint64": int,
        "Slot": int,
        "Epoch": int,
        "BuilderIndex": int,
        "ValidatorIndex": int,
        "Boolean": bool,
        "MIN_DEPOSIT_AMOUNT": 1_000_000_000,
        "FAR_FUTURE_EPOCH": (1 << 64) - 1,
        "BUILDER_PAYMENT_THRESHOLD_NUMERATOR": 6,
        "BUILDER_PAYMENT_THRESHOLD_DENOMINATOR": 10,
        "SLOTS_PER_EPOCH": 8,
        "SLOTS_PER_HISTORICAL_ROOT": 64,
        "EPOCHS_PER_SLASHINGS_VECTOR": 64,
        "MIN_SLASHING_PENALTY_QUOTIENT_ELECTRA": 4096,
        "WHISTLEBLOWER_REWARD_QUOTIENT_ELECTRA": 512,
        "PROPOSER_WEIGHT": 8,
        "WEIGHT_DENOMINATOR": 64,
        "MAX_WITHDRAWAL_REQUESTS_PER_PAYLOAD": 16,
        "MAX_CONSOLIDATION_REQUESTS_PER_PAYLOAD": 2,
        "MAX_BUILDER_DEPOSIT_REQUESTS_PER_PAYLOAD": 64,
        "MAX_BUILDER_EXIT_REQUESTS_PER_PAYLOAD": 16,
        "BuilderPendingWithdrawal": BuilderPendingWithdrawal,
        "BuilderPendingPayment": BuilderPendingPayment,
    }

    extracted_count = 0
    for block in code_blocks:
        if any(block.lstrip().startswith(prefix) for prefix in target_defs):
            exec(compile(block, str(VENDOR_BEACON_MD), "exec"), env)
            extracted_count += 1
    assert extracted_count == len(target_defs), (
        f"Expected {len(target_defs)} Gloas functions from {VENDOR_BEACON_MD}, got {extracted_count}"
    )
    return env


VENDORED_EL = load_vendored_execution_specs()
VENDORED_CL = load_vendored_gloas_specs()


# ---------------------------------------------------------------------------
# Wrappers Driving the Vendored Upstream Functions
# ---------------------------------------------------------------------------

def vendored_charge_gas_and_state_gas(gas_left: int, state_gas_left: int, reg: int, st: int):
    GasMeter = VENDORED_EL["GasMeter"]
    charge_gas_from_meter = VENDORED_EL["charge_gas_from_meter"]
    charge_state_gas_from_meter = VENDORED_EL["charge_state_gas_from_meter"]
    meter = GasMeter(
        gas_left=gas_left,
        state_gas_left=state_gas_left,
        state_gas_baseline=state_gas_left,
    )
    try:
        charge_gas_from_meter(meter, reg)
        charge_state_gas_from_meter(meter, st)
        return True, int(meter.gas_left), int(meter.state_gas_left)
    except OutOfGasError:
        return False, 0, 0


def vendored_allocate_evm_gas(tx_gas: int, intrinsic_exec: int):
    allocate_evm_gas = VENDORED_EL["allocate_evm_gas"]
    IntrinsicGasCost = VENDORED_EL["IntrinsicGasCost"]
    alloc = allocate_evm_gas(tx_gas, IntrinsicGasCost(execution=intrinsic_exec, state=0))
    return int(alloc.execution_gas), int(alloc.state_gas_reservoir)


def vendored_settle_transaction_gas(
    tx_gas: int,
    calldata_floor: int,
    gas_left: int,
    state_gas_left: int,
    refund_counter: int,
    state_gas_used: int,
):
    settle_transaction_gas = VENDORED_EL["settle_transaction_gas"]
    res = settle_transaction_gas(
        tx_gas, calldata_floor, gas_left, state_gas_left, refund_counter, state_gas_used
    )
    return int(res.gas_used), int(res.execution_gas_used)


def vendored_sstore_pricing(is_cold: bool, orig_val: int, curr_val: int, new_val: int):
    """
    Executes the vendored `sstore(evm)` function from `vm/instructions/storage.py:68-162`
    on a mock EVM frame and extracts `(exec_gas_charged, state_gas_charged, state_gas_refunded)`.
    """
    GasMeter = VENDORED_EL["GasMeter"]
    U256 = VENDORED_EL["U256"]
    sstore_fn = VENDORED_EL["sstore"]

    initial_exec = 1_000_000
    initial_state = 1_000_000
    target = b"\x11" * 20
    key_bytes = (0).to_bytes(32, "big")

    class _MockEvm:
        def __init__(self):
            self.is_static = False
            # `sstore` pops `key` first, then `new_value`
            self.stack = [U256(new_val), U256(0)]
            self.current_target = target
            self.accessed_storage_keys = set() if is_cold else {(target, key_bytes)}
            self.gas_meter = GasMeter(
                gas_left=initial_exec,
                state_gas_left=initial_state,
                state_gas_baseline=initial_state,
            )
            self.tx_env = type("TxEnv", (), {"state": None})()
            self.pc = 0

    evm = _MockEvm()
    VENDORED_EL["pop"] = lambda stack: stack.pop()
    VENDORED_EL["get_storage_original"] = lambda _st, _addr, _k: U256(orig_val)
    VENDORED_EL["get_storage"] = lambda _st, _addr, _k: U256(curr_val)
    VENDORED_EL["set_storage"] = lambda _st, _addr, _k, _v: None

    sstore_fn(evm)

    exec_charged = initial_exec - int(evm.gas_meter.gas_left)
    net_state_delta = int(evm.gas_meter.state_gas_left) - initial_state
    if net_state_delta <= 0:
        state_charged = -net_state_delta
        state_refund = 0
    else:
        state_charged = 0
        state_refund = net_state_delta
    return exec_charged, state_charged, state_refund


def vendored_selfdestruct_pricing(orig_bal: int, ben_alive: bool, ben_cold: bool):
    """
    Executes the vendored `selfdestruct(evm)` function from `vm/instructions/system.py:706-779`
    on a mock EVM frame and extracts `(exec_gas_charged, state_gas_charged)`.
    """
    GasMeter = VENDORED_EL["GasMeter"]
    U256 = VENDORED_EL["U256"]
    selfdestruct_fn = VENDORED_EL["selfdestruct"]

    initial_exec = 1_000_000
    initial_state = 1_000_000
    originator = b"\xaa" * 20
    beneficiary = b"\xbb" * 20

    class _MockEvm:
        def __init__(self):
            self.is_static = False
            self.stack = [U256(1)]
            self.current_target = originator
            self.accessed_addresses = set() if ben_cold else {beneficiary}
            self.gas_meter = GasMeter(
                gas_left=initial_exec,
                state_gas_left=initial_state,
                state_gas_baseline=initial_state,
            )
            self.tx_env = type(
                "TxEnv",
                (),
                {"state": type("TxState", (), {"created_accounts": set()})()},
            )()
            self.accounts_to_delete = set()
            self.running = True

    evm = _MockEvm()
    VENDORED_EL["pop"] = lambda stack: stack.pop()
    VENDORED_EL["to_address_masked"] = lambda _v: beneficiary
    VENDORED_EL["is_account_alive"] = lambda _st, _addr: ben_alive
    VENDORED_EL["get_account"] = lambda _st, _addr: type("Acc", (), {"balance": orig_bal})()
    VENDORED_EL["move_ether"] = lambda _st, _o, _b, _amt: None
    VENDORED_EL["emit_transfer_log"] = lambda _evm, _o, _b, _amt: None

    selfdestruct_fn(evm)

    exec_charged = initial_exec - int(evm.gas_meter.gas_left)
    state_charged = initial_state - int(evm.gas_meter.state_gas_left)
    return exec_charged, state_charged


def vendored_can_builder_cover_bid(
    builder_balance: int, pending_to_withdraw: int, bid_amount: int
) -> bool:
    can_builder_cover_bid = VENDORED_CL["can_builder_cover_bid"]
    BuilderPendingWithdrawal = VENDORED_CL["BuilderPendingWithdrawal"]
    state = type(
        "BeaconState",
        (),
        {
            "builders": [type("Builder", (), {"balance": builder_balance})()],
            "builder_pending_withdrawals": [
                BuilderPendingWithdrawal(fee_recipient=0, amount=pending_to_withdraw, builder_index=0)
            ],
            "builder_pending_payments": [],
        },
    )()
    return bool(can_builder_cover_bid(state, 0, bid_amount))


def vendored_get_builder_payment_quorum_threshold(
    total_active_balance: int, slots_per_epoch: int
) -> int:
    get_builder_payment_quorum_threshold = VENDORED_CL["get_builder_payment_quorum_threshold"]
    VENDORED_CL["get_total_active_balance"] = lambda _st: total_active_balance
    VENDORED_CL["SLOTS_PER_EPOCH"] = slots_per_epoch
    return int(get_builder_payment_quorum_threshold(object()))


# ---------------------------------------------------------------------------
# Differential Test Cases (Unit + 1,000-Iteration Randomized Fuzzing)
# ---------------------------------------------------------------------------

def test_differential_charge_gas():
    lib = ensure_shared_lib()
    rng = random.Random(8037)
    for _ in range(1000):
        gl = rng.randint(0, 500_000)
        res = rng.randint(0, 500_000)
        reg = rng.randint(0, 300_000)
        st = rng.randint(0, 300_000)
        py_ok, py_gl, py_res = vendored_charge_gas_and_state_gas(gl, res, reg, st)
        c_ok = bool(lib.glamsterdam_charge_gas_ok_cabi(gl, res, reg, st))
        c_gl = lib.glamsterdam_charge_gas_left_cabi(gl, res, reg, st)
        c_res = lib.glamsterdam_charge_gas_reservoir_cabi(gl, res, reg, st)
        assert c_ok == py_ok
        assert c_gl == py_gl
        assert c_res == py_res


def test_differential_allocate_and_settle_gas():
    lib = ensure_shared_lib()
    rng = random.Random(7778)
    for _ in range(1000):
        intrinsic = rng.randint(12_000, 16_777_216)
        tx_gas = rng.randint(intrinsic, 60_000_000)
        py_exec, py_res = vendored_allocate_evm_gas(tx_gas, intrinsic)
        c_exec = lib.glamsterdam_allocate_exec_gas_cabi(tx_gas, intrinsic)
        c_res = lib.glamsterdam_allocate_reservoir_cabi(tx_gas, intrinsic)
        assert c_exec == py_exec
        assert c_res == py_res

        floor = rng.randint(12_000, intrinsic)
        gl = rng.randint(0, py_exec)
        sl = rng.randint(0, py_res)
        used_before = tx_gas - gl - sl
        st_used = rng.randint(0, used_before)
        refund = rng.randint(0, 200_000)
        py_gu, py_egu = vendored_settle_transaction_gas(tx_gas, floor, gl, sl, refund, st_used)
        c_gu = lib.glamsterdam_settle_gas_used_cabi(tx_gas, floor, gl, sl, refund, st_used)
        c_egu = lib.glamsterdam_settle_exec_gas_used_cabi(tx_gas, floor, gl, sl, refund, st_used)
        assert c_gu == py_gu
        assert c_egu == py_egu


def test_differential_sstore_and_selfdestruct():
    lib = ensure_shared_lib()
    vals = [0, 1, 42, 99]
    for is_cold in (0, 1):
        for o in vals:
            for c in vals:
                for n in vals:
                    py_e, py_s, py_sr = vendored_sstore_pricing(bool(is_cold), o, c, n)
                    assert lib.glamsterdam_sstore_exec_cost_cabi(is_cold, o, c, n) == py_e
                    assert lib.glamsterdam_sstore_state_cost_cabi(is_cold, o, c, n) == py_s
                    assert lib.glamsterdam_sstore_state_refund_cabi(is_cold, o, c, n) == py_sr

    for orig_bal in (0, 1, 1000):
        for ben_alive in (0, 1):
            for ben_cold in (0, 1):
                py_eg, py_sg = vendored_selfdestruct_pricing(orig_bal, bool(ben_alive), bool(ben_cold))
                assert lib.glamsterdam_eip8246_selfdestruct_exec_gas_cabi(orig_bal, ben_alive, ben_cold) == py_eg
                assert lib.glamsterdam_eip8246_selfdestruct_state_gas_cabi(orig_bal, ben_alive, ben_cold) == py_sg

    # Also test `glamsterdam_eip8246_eth_conservation_cabi` against vendored `move_ether` (`state_tracker.py:606-638`)
    move_ether_fn = VENDORED_EL["move_ether"]
    for orig_addr, ben_addr in ((0xAA, 0xBB), (0xAA, 0xAA)):
        for orig_bal in (0, 250, 1000):
            for ben_bal in (0, 500):
                init_b = orig_bal if orig_addr == ben_addr else ben_bal
                accts = {
                    orig_addr: type("Acc", (), {"balance": orig_bal})(),
                    ben_addr: type("Acc", (), {"balance": init_b})(),
                }
                VENDORED_EL["modify_state"] = lambda _st, addr, fn: fn(accts[addr])
                pre_sum = orig_bal if orig_addr == ben_addr else orig_bal + ben_bal
                move_ether_fn(None, orig_addr, ben_addr, orig_bal)
                post_sum = (
                    accts[orig_addr].balance
                    if orig_addr == ben_addr
                    else accts[orig_addr].balance + accts[ben_addr].balance
                )
                c_conserved = bool(
                    lib.glamsterdam_eip8246_eth_conservation_cabi(pre_sum, 0, 0, post_sum)
                )
                assert c_conserved is True and post_sum == pre_sum


def test_differential_gloas7732():
    lib = ensure_shared_lib()
    rng = random.Random(7732)
    for _ in range(1000):
        bal = rng.randint(0, 10**10)
        pend = rng.randint(0, 5_000_000_000)
        bid = rng.randint(0, 5_000_000_000)
        assert bool(
            lib.glamsterdam_eip7732_can_cover_bid_cabi(bal, pend, bid)
        ) == vendored_can_builder_cover_bid(bal, pend, bid)
        total_active = rng.randint(32_000_000_000, 32_000_000_000_000)
        for spe in (8, 32):
            assert lib.glamsterdam_eip7732_quorum_threshold_cabi(
                total_active, spe
            ) == vendored_get_builder_payment_quorum_threshold(total_active, spe)
        for is_act in (0, 1):
            assert bool(lib.glamsterdam_eip7732_can_builder_exit_cabi(is_act, pend)) == (
                bool(is_act) and pend == 0
            )


def test_vendored_gloas_slashed_payment_resurrection_trace():
    """
    Executes the actual markdown-extracted `slash_validator`, `process_builder_pending_payments`,
    and `apply_parent_execution_payload` functions from `vendor/upstreams/consensus_specs/specs/gloas/beacon-chain.md`
    to confirm `F-7732-SLASHED-PAYMENT-RESURRECTION` on `v1.7.0-beta.4` (`aa16bb4c`).
    """
    BuilderPendingPayment = VENDORED_CL["BuilderPendingPayment"]
    BuilderPendingWithdrawal = VENDORED_CL["BuilderPendingWithdrawal"]
    slash_validator = VENDORED_CL["slash_validator"]
    process_builder_pending_payments = VENDORED_CL["process_builder_pending_payments"]
    apply_parent_execution_payload = VENDORED_CL["apply_parent_execution_payload"]

    spe = 8
    VENDORED_CL["SLOTS_PER_EPOCH"] = spe
    VENDORED_CL["compute_epoch_at_slot"] = lambda slot: slot // spe
    VENDORED_CL["get_current_epoch"] = lambda st: st.slot // spe
    VENDORED_CL["get_previous_epoch"] = lambda st: max(0, (st.slot // spe) - 1)
    VENDORED_CL["get_total_active_balance"] = lambda _st: 32_000_000_000_000
    VENDORED_CL["initiate_validator_exit"] = lambda _st, _idx: None
    VENDORED_CL["decrease_balance"] = lambda _st, _idx, _amt: None
    VENDORED_CL["increase_balance"] = lambda _st, _idx, _amt: None
    VENDORED_CL["get_beacon_proposer_index"] = lambda st: st.latest_block_header.proposer_index
    for req_fn in (
        "process_deposit_request",
        "process_withdrawal_request",
        "process_consolidation_request",
        "process_builder_deposit_request",
        "process_builder_exit_request",
    ):
        VENDORED_CL[req_fn] = lambda _st, _op: None

    parent_slot = 4 * spe + 3
    proposer_idx = 42
    bid_value = 1_000_000
    fee_recipient = 0xAB

    payments = [BuilderPendingPayment.empty() for _ in range(2 * spe)]
    payments[spe + (parent_slot % spe)] = BuilderPendingPayment(
        weight=0,
        withdrawal=BuilderPendingWithdrawal(
            fee_recipient=fee_recipient, amount=bid_value, builder_index=0
        ),
        proposer_index=proposer_idx,
    )

    state = type(
        "BeaconState",
        (),
        {
            "slot": parent_slot,
            "validators": {
                proposer_idx: type(
                    "Validator",
                    (),
                    {"slashed": False, "withdrawable_epoch": 0, "effective_balance": 32_000_000_000},
                )()
            },
            "slashings": [0] * 64,
            "builder_pending_payments": payments,
            "builder_pending_withdrawals": [],
            "latest_block_header": type(
                "Header", (), {"slot": parent_slot, "proposer_index": proposer_idx}
            )(),
            "latest_execution_payload_bid": type(
                "Bid",
                (),
                {
                    "value": bid_value,
                    "fee_recipient": fee_recipient,
                    "builder_index": 0,
                    "block_hash": 0x1234,
                },
            )(),
            "execution_payload_availability": [False] * 64,
            "latest_block_hash": 0,
        },
    )()

    # 1. `slash_validator` clears `builder_pending_payments[payment_idx]`
    slash_validator(state, proposer_idx)
    assert state.validators[proposer_idx].slashed is True
    assert state.builder_pending_payments[spe + (parent_slot % spe)] == BuilderPendingPayment.empty()
    assert state.latest_execution_payload_bid.value == bid_value

    # 2. Two epoch boundaries pass without a block
    process_builder_pending_payments(state)
    process_builder_pending_payments(state)
    assert state.builder_pending_withdrawals == []

    # 3. Child block arrives at epoch 6 (`parent_epoch = 4 < previous_epoch = 5`)
    state.slot = 6 * spe + 1
    empty_requests = type(
        "ExecutionRequests",
        (),
        {
            "deposits": [],
            "withdrawals": [],
            "consolidations": [],
            "builder_deposits": [],
            "builder_exits": [],
        },
    )()
    apply_parent_execution_payload(state, empty_requests)

    # Unpatched v1.7.0-beta.4 resurrects the slashed proposer's payment from `parent_bid.value`
    assert state.builder_pending_withdrawals == [
        BuilderPendingWithdrawal(fee_recipient=fee_recipient, amount=bid_value, builder_index=0)
    ]


if __name__ == "__main__":
    test_differential_charge_gas()
    test_differential_allocate_and_settle_gas()
    test_differential_sstore_and_selfdestruct()
    test_differential_gloas7732()
    test_vendored_gloas_slashed_payment_resurrection_trace()
    print(
        "differential-tests ok: 100% agreement between Lean 4.31 C-ABI and vendored upstream specs."
    )
