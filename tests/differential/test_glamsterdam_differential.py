#!/usr/bin/env python3
"""
Differential Test Suite ("Double Checks de Secours") for the Glamsterdam Formal Audit.

Compares the compiled Lean 4.31 C-ABI shared library (`.lake/build/libglamsterdam_cabi.so`)
against the pinned upstream Python implementations from:
1. `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`
   (`src/ethereum/forks/amsterdam/vm/gas.py`, `vm/instructions/storage.py`, `vm/instructions/system.py`)
2. `ethereum/consensus-specs` @ `aa16bb4c156184e9548a997d53efaf2a228a6304` (`v1.7.0-beta.4`,
   `specs/gloas/beacon-chain.md`)

Can be run via `pytest tests/differential/test_glamsterdam_differential.py` or directly via
`python3 tests/differential/test_glamsterdam_differential.py`.
"""
import ctypes
import pathlib
import random
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
SO_PATH = ROOT / ".lake" / "build" / "libglamsterdam_cabi.so"


def ensure_shared_lib() -> ctypes.CDLL:
    if not SO_PATH.exists():
        lean_prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        c_files = [
            ROOT / ".lake/build/ir/Glamsterdam/Common/Prelude.c",
            ROOT / ".lake/build/ir/Glamsterdam/Common/MetaSpec.c",
            ROOT / ".lake/build/ir/Glamsterdam/Common/ElCore.c",
            ROOT / ".lake/build/ir/Glamsterdam/Eip8246/Spec.c",
            ROOT / ".lake/build/ir/Glamsterdam/Gas/Spec.c",
            ROOT / ".lake/build/ir/Glamsterdam/Gloas7732/Spec.c",
        ]
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
# Exact Python Reference Implementations from `16898000` and `aa16bb4c`
# ---------------------------------------------------------------------------

def py_charge_gas_and_state_gas(gas_left: int, state_gas_left: int, reg: int, st: int):
    # `charge_gas_from_meter` (`vm/gas.py:379-394`) + `charge_state_gas_from_meter` (`vm/gas.py:413-436`)
    if gas_left < reg:
        return False, 0, 0
    gas_left -= reg
    if state_gas_left >= st:
        state_gas_left -= st
        return True, gas_left, state_gas_left
    elif state_gas_left + gas_left >= st:
        remainder = st - state_gas_left
        state_gas_left = 0
        gas_left -= remainder
        return True, gas_left, state_gas_left
    else:
        return False, 0, 0


def py_allocate_evm_gas(tx_gas: int, intrinsic_exec: int):
    # `allocate_evm_gas` (`vm/gas.py:1105-1138`)
    tx_max_gas_limit = 16_777_216
    evm_gas = tx_gas - intrinsic_exec
    execution_gas_budget = tx_max_gas_limit - intrinsic_exec
    execution_gas = min(execution_gas_budget, evm_gas)
    state_gas_reservoir = evm_gas - execution_gas
    return execution_gas, state_gas_reservoir


def py_settle_transaction_gas(
    tx_gas: int,
    calldata_floor: int,
    gas_left: int,
    state_gas_left: int,
    refund_counter: int,
    state_gas_used: int,
):
    # `settle_transaction_gas` (`vm/gas.py:1163-1228`)
    gas_used_before_refund = tx_gas - gas_left - state_gas_left
    gas_refund = min(gas_used_before_refund // 5, refund_counter)
    gas_used_after_refund = gas_used_before_refund - gas_refund
    gas_used = max(gas_used_after_refund, calldata_floor)
    settled_state_gas_used = max(0, state_gas_used)
    execution_gas_used = max(gas_used_before_refund - settled_state_gas_used, calldata_floor)
    return gas_used, execution_gas_used


def py_sstore_pricing(is_cold: bool, orig_val: int, curr_val: int, new_val: int):
    # `sstore` (`vm/instructions/storage.py:88-157`)
    gas_cost = 2100 if is_cold else 100
    if orig_val == curr_val and curr_val != new_val:
        gas_cost += 10000
    state_gas = 97920 if (orig_val == curr_val and curr_val != new_val and orig_val == 0) else 0
    state_refund = 97920 if (curr_val != new_val and orig_val == new_val and orig_val == 0) else 0
    return gas_cost, state_gas, state_refund


def py_selfdestruct_pricing(orig_bal: int, ben_alive: bool, ben_cold: bool):
    # `selfdestruct` (`vm/instructions/system.py:725-758`)
    gas_cost = 5000 + (3000 if ben_cold else 0)
    state_gas = 0
    account_write_gas = 0
    if not ben_alive and orig_bal != 0:
        state_gas = 183600
        account_write_gas = 9000
    return gas_cost + account_write_gas, state_gas


def py_can_builder_cover_bid(builder_balance: int, pending_to_withdraw: int, bid_amount: int) -> bool:
    # `can_builder_cover_bid` (`specs/gloas/beacon-chain.md:1184-1193`)
    min_balance = 1_000_000_000 + pending_to_withdraw
    if builder_balance < min_balance:
        return False
    return builder_balance - min_balance >= bid_amount


def py_get_builder_payment_quorum_threshold(total_active_balance: int, slots_per_epoch: int) -> int:
    # `get_builder_payment_quorum_threshold` (`specs/gloas/beacon-chain.md:1433-1440`)
    per_slot_balance = total_active_balance // slots_per_epoch
    quorum = per_slot_balance * 6
    return quorum // 10


# ---------------------------------------------------------------------------
# Differential Test Cases (Unit + 1,000-Iteration Randomized Fuzzing)
# ---------------------------------------------------------------------------

def test_differential_charge_gas():
    lib = ensure_shared_lib()
    rng = random.Random(8037)
    for _ in range(500):
        gl = rng.randint(0, 500_000)
        res = rng.randint(0, 500_000)
        reg = rng.randint(0, 300_000)
        st = rng.randint(0, 300_000)
        py_ok, py_gl, py_res = py_charge_gas_and_state_gas(gl, res, reg, st)
        c_ok = bool(lib.glamsterdam_charge_gas_ok_cabi(gl, res, reg, st))
        c_gl = lib.glamsterdam_charge_gas_left_cabi(gl, res, reg, st)
        c_res = lib.glamsterdam_charge_gas_reservoir_cabi(gl, res, reg, st)
        assert c_ok == py_ok
        assert c_gl == py_gl
        assert c_res == py_res


def test_differential_allocate_and_settle_gas():
    lib = ensure_shared_lib()
    rng = random.Random(7778)
    for _ in range(500):
        intrinsic = rng.randint(12_000, 16_777_216)
        tx_gas = rng.randint(intrinsic, 60_000_000)
        py_exec, py_res = py_allocate_evm_gas(tx_gas, intrinsic)
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
        py_gu, py_egu = py_settle_transaction_gas(tx_gas, floor, gl, sl, refund, st_used)
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
                    py_e, py_s, py_sr = py_sstore_pricing(bool(is_cold), o, c, n)
                    assert lib.glamsterdam_sstore_exec_cost_cabi(is_cold, o, c, n) == py_e
                    assert lib.glamsterdam_sstore_state_cost_cabi(is_cold, o, c, n) == py_s
                    assert lib.glamsterdam_sstore_state_refund_cabi(is_cold, o, c, n) == py_sr

    for orig_bal in (0, 1, 1000):
        for ben_alive in (0, 1):
            for ben_cold in (0, 1):
                py_eg, py_sg = py_selfdestruct_pricing(orig_bal, bool(ben_alive), bool(ben_cold))
                assert lib.glamsterdam_eip8246_selfdestruct_exec_gas_cabi(orig_bal, ben_alive, ben_cold) == py_eg
                assert lib.glamsterdam_eip8246_selfdestruct_state_gas_cabi(orig_bal, ben_alive, ben_cold) == py_sg


def test_differential_gloas7732():
    lib = ensure_shared_lib()
    rng = random.Random(7732)
    for _ in range(500):
        bal = rng.randint(0, 10_000_000_000)
        pend = rng.randint(0, 5_000_000_000)
        bid = rng.randint(0, 5_000_000_000)
        assert bool(lib.glamsterdam_eip7732_can_cover_bid_cabi(bal, pend, bid)) == py_can_builder_cover_bid(
            bal, pend, bid
        )
        total_active = rng.randint(32_000_000_000, 32_000_000_000_000)
        for spe in (8, 32):
            assert lib.glamsterdam_eip7732_quorum_threshold_cabi(
                total_active, spe
            ) == py_get_builder_payment_quorum_threshold(total_active, spe)
        for is_act in (0, 1):
            assert bool(lib.glamsterdam_eip7732_can_builder_exit_cabi(is_act, pend)) == (
                bool(is_act) and pend == 0
            )


if __name__ == "__main__":
    test_differential_charge_gas()
    test_differential_allocate_and_settle_gas()
    test_differential_sstore_and_selfdestruct()
    test_differential_gloas7732()
    print("differential-tests ok: 100% agreement between Lean 4.31 C-ABI and Python reference specs.")
