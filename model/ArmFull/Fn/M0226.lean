import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0041
import ArmFull.Fn.M0087
import ArmFull.Fn.M0112
import ArmFull.Fn.M0114
import ArmFull.Fn.M0124
import ArmFull.Fn.M0141
import ArmFull.Fn.M0144
import ArmFull.Fn.M0150
import ArmFull.Fn.M0159
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0169
import ArmFull.Fn.M0175
import ArmFull.Fn.M0200
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace ArmFull

variable {real : Type} [Sail.SailReal real]

open ConcurrencyInterfaceV1

namespace Functions

open signal
open option
open exception
open arm_acc_type
open __InstrEnc
open WFxType
open VFPNegMul
open VCGTtype
open VCGEType
open VBitOps
open VBitOp
open VARange
open Unpredictable
open TranslationStage
open TimeStamp
open TMFailure
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open SystemHintOp
open Signal
open ShiftType
open Shareability
open SecurityState
open SVECmp
open SRType
open SMEExceptionType
open SDFType
open RestrictType
open Register
open Regime
open ReduceOp
open PrivilegeLevel
open PrefetchHint
open PSTATEField
open PGSe
open PASpace
open PARTIDspaceType
open OpType
open MoveWideOp
open MemType
open MemTagType
open MemOp
open MemAtomicOp
open MOPSStage
open MBReqTypes
open MBReqDomain
open LogicalOp
open InterruptID
open InstrSet
open ImmediateOp
open GPCF
open GCSInstruction
open Feature
open Fault
open FPUnaryOp
open FPType
open FPRounding
open FPMaxMinOp
open FPExc
open FPConvOp
open ExtendType
open ExceptionalOccurrenceTargetState
open Exception
open ErrorState
open DeviceType
open DescriptorType
open DSBAlias
open CrossTriggerIn
open CountOp
open Constraint
open CompareOp
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open BranchType
open BarrierExt
open Barrier
open ArchVersion
open AccessType
open ATAccess

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 31 16)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 0)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__5 ← (( do (UnsignedSat sum 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 w__5))
  let w__6 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do (UnsignedSat diff 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__6 31 16 w__7))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__5 ← (( do (UnsignedSat diff1 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 w__5))
  let w__6 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do (UnsignedSat diff2 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__6 31 16 w__7))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 15 8)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff3 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__4 23 16)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff4 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__6 31 24)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__7 31 24)))
  let w__8 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__9 ← (( do (UnsignedSat diff1 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 w__9))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__11 ← (( do (UnsignedSat diff2 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__10 15 8 w__11))
  let w__12 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__13 ← (( do (UnsignedSat diff3 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__12 23 16 w__13))
  let w__14 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__15 ← (( do (UnsignedSat diff4 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__14 31 24 w__15))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USAD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let absdiff1 : Nat :=
    (Int.natAbs
      ((BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0)) -i (BitVec.toNat
          (Sail.BitVec.extractLsb w__1 7 0))))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let absdiff2 : Nat :=
    (Int.natAbs
      ((BitVec.toNat (Sail.BitVec.extractLsb w__2 15 8)) -i (BitVec.toNat
          (Sail.BitVec.extractLsb w__3 15 8))))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let absdiff3 : Nat :=
    (Int.natAbs
      ((BitVec.toNat (Sail.BitVec.extractLsb w__4 23 16)) -i (BitVec.toNat
          (Sail.BitVec.extractLsb w__5 23 16))))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let absdiff4 : Nat :=
    (Int.natAbs
      ((BitVec.toNat (Sail.BitVec.extractLsb w__6 31 24)) -i (BitVec.toNat
          (Sail.BitVec.extractLsb w__7 31 24))))
  let result : Int := (((absdiff1 +i absdiff2) +i absdiff3) +i absdiff4)
  (R_set d (integer_subrange result 31 0))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_USADA8_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let absdiff1 : Nat :=
    (Int.natAbs
      ((BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0)) -i (BitVec.toNat
          (Sail.BitVec.extractLsb w__1 7 0))))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let absdiff2 : Nat :=
    (Int.natAbs
      ((BitVec.toNat (Sail.BitVec.extractLsb w__2 15 8)) -i (BitVec.toNat
          (Sail.BitVec.extractLsb w__3 15 8))))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let absdiff3 : Nat :=
    (Int.natAbs
      ((BitVec.toNat (Sail.BitVec.extractLsb w__4 23 16)) -i (BitVec.toNat
          (Sail.BitVec.extractLsb w__5 23 16))))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let absdiff4 : Nat :=
    (Int.natAbs
      ((BitVec.toNat (Sail.BitVec.extractLsb w__6 31 24)) -i (BitVec.toNat
          (Sail.BitVec.extractLsb w__7 31 24))))
  let w__8 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let result : Int := (((((BitVec.toNat w__8) +i absdiff1) +i absdiff2) +i absdiff3) +i absdiff4)
  (R_set d (integer_subrange result 31 0))


/-- Type quantifiers: d : Nat, n : Nat, saturate_to : Nat, 0 ≤ saturate_to ∧
  saturate_to ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USAT16_Op_A_txt (d : Nat) (n : Nat) (saturate_to : Nat) : SailM Unit := do
  let result1 ← (( do (undefined_bitvector_at (← occLabel 3324) 16) ) : SailM (BitVec 16) )
  let result2 ← (( do (undefined_bitvector_at (← occLabel 3325) 16) ) : SailM (BitVec 16) )
  let sat1 ← (( do (undefined_bool_at (← occLabel 3326) ()) ) : SailM Bool )
  let sat2 ← (( do (undefined_bool_at (← occLabel 3327) ()) ) : SailM Bool )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do
    (ZeroUnsignedSatQ (BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) saturate_to 16) ) : SailM
    ((BitVec 16) × Bool) )
  let (tup__0, tup__1) := (w__1 : ((BitVec 16) × Bool))
  let result1 : (BitVec 16) := tup__0
  let sat1 : Bool := tup__1
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do
    (ZeroUnsignedSatQ (BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) saturate_to 16) ) : SailM
    ((BitVec 16) × Bool) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 16) × Bool))
  let result2 : (BitVec 16) := tup__0
  let sat2 : Bool := tup__1
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 result1))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 result2))
  if ((sat1 || sat2) : Bool)
  then
    (do
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, saturate_to : Nat, shift_n : Int, 0 ≤ saturate_to ∧
  saturate_to ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USAT_Op_A_txt (d : Nat) (n : Nat) (saturate_to : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let result ← (( do (undefined_bitvector_at (← occLabel 3328) 32) ) : SailM (BitVec 32) )
  let sat ← (( do (undefined_bool_at (← occLabel 3329) ()) ) : SailM Bool )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let operand ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (ZeroUnsignedSatQ (BitVec.toInt operand) saturate_to 32) ) : SailM
    ((BitVec 32) × Bool) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × Bool))
  let result : (BitVec 32) := tup__0
  let sat : Bool := tup__1
  (R_set d result)
  if (sat : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 31 16)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 0)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange sum 15 0)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange diff 15 0)))
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with GE := (Sail.BitVec.updateSubrange w__7.GE 1 0
      (if ((sum ≥b (BitVec.toNat 0x10000#20)) : Bool)
      then 0b11#2
      else 0b00#2)) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with GE := (Sail.BitVec.updateSubrange w__9.GE 3 2
      (if ((diff ≥b 0) : Bool)
      then 0b11#2
      else 0b00#2)) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange diff1 15 0)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange diff2 15 0)))
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with GE := (Sail.BitVec.updateSubrange w__7.GE 1 0
      (if ((diff1 ≥b 0) : Bool)
      then 0b11#2
      else 0b00#2)) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with GE := (Sail.BitVec.updateSubrange w__9.GE 3 2
      (if ((diff2 ≥b 0) : Bool)
      then 0b11#2
      else 0b00#2)) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_USUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 15 8)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff3 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__4 23 16)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff4 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__6 31 24)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__7 31 24)))
  let w__8 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 (integer_subrange diff1 7 0)))
  let w__9 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__9 15 8 (integer_subrange diff2 7 0)))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__10 23 16 (integer_subrange diff3 7 0)))
  let w__11 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__11 31 24 (integer_subrange diff4 7 0)))
  let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__12 with GE := (BitVec.update w__13.GE 0
      (Bit
        (if ((diff1 ≥b 0) : Bool)
        then 1#1
        else 0#1))) }
  let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__14 with GE := (BitVec.update w__15.GE 1
      (Bit
        (if ((diff2 ≥b 0) : Bool)
        then 1#1
        else 0#1))) }
  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__16 with GE := (BitVec.update w__17.GE 2
      (Bit
        (if ((diff3 ≥b 0) : Bool)
        then 1#1
        else 0#1))) }
  let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__18 with GE := (BitVec.update w__19.GE 3
      (Bit
        (if ((diff4 ≥b 0) : Bool)
        then 1#1
        else 0#1))) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTAB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  let w__1 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange w__1 15 0
      ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb w__2 15 0)) + (Sail.BitVec.castWidth (m := 16) (Sail.BitVec.zeroExtend
          (Sail.BitVec.extractLsb rotated 7 0) 16)))))
  let w__3 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange w__3 31 16
      ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb w__4 31 16)) + (Sail.BitVec.castWidth (m := 16) (Sail.BitVec.zeroExtend
          (Sail.BitVec.extractLsb rotated 23 16) 16)))))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTAB_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (w__1 + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.zeroExtend
        (Sail.BitVec.extractLsb rotated 7 0) 32))))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTAH_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (w__1 + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.zeroExtend
        (Sail.BitVec.extractLsb rotated 15 0) 32))))


/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTB16_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  let w__1 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange w__1 15 0
      (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 7 0) 16)))
  let w__2 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange w__2 31 16
      (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 23 16) 16)))


/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTB_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  (R_set d (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 7 0) 32))


/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UXTH_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  (R_set d (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb rotated 15 0) 32))


/-- Type quantifiers: d : Nat, k_read_spsr : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MRS_Op_AS_txt (d : Nat) (read_spsr : Bool) : SailM Unit := do
  let psr_val ← (( do (undefined_bitvector_at (← occLabel 3782) 32) ) : SailM (BitVec 32) )
  if (read_spsr : Bool)
  then
    (do
      let w__2 ← (( do
        if ((← do
             let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__0.M == M32_User) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__1.M == M32_System) : Bool)))) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          let w__3 ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
          (R_set d w__3)))
  else
    (do
      let mask : (BitVec 32) := 0b11111000111011110000001111011111#32
      let w__4 ← (( do (GetPSRFromPSTATE AArch32_NonDebugState 32) ) : SailM (BitVec 32) )
      let psr_val : (BitVec 32) := ((w__4 &&& mask) : (BitVec 32))
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      let psr_val ← (( do
        if ((w__5.EL == EL0) : Bool)
        then
          (do
            let w__6 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
            let psr_val := ((BitVec.update psr_val 22 (Bit w__6)) : (BitVec 32))
            let w__7 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
            let psr_val := ((Sail.BitVec.updateSubrange psr_val 9 6 w__7) : (BitVec 32))
            let w__8 ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
            let psr_val := ((Sail.BitVec.updateSubrange psr_val 4 0 w__8) : (BitVec 32))
            (pure (psr_val)))
        else (pure (psr_val)) ) : SailM (BitVec 32) )
      (R_set d psr_val))


def decode_aarch32_instrs_MSR_i_A1enc_AS_txt (cond : (BitVec 4)) (R : (BitVec 1)) (mask : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:41463.29-41463.30"
      if (((mask == 0b0000#4) && (R == 0#1)) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      let write_spsr : Bool := (R == 1#1)
      if ((mask == 0b0000#4) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_MSR_i_Op_AS_txt imm32 mask write_spsr))
  else (pure (()))


/-- Type quantifiers: n : Nat, k_write_spsr : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_MSR_r_Op_AS_txt (mask : (BitVec 4)) (n : Nat) (write_spsr : Bool) : SailM Unit := do
  if (write_spsr : Bool)
  then
    (do
      let w__2 ← (( do
        if ((← do
             let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__0.M == M32_User) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__1.M == M32_System) : Bool)))) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
          (SPSRWriteByInstr w__3 mask)))
  else
    (do
      let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
      (CPSRWriteByInstr w__4 mask))


/-- Type quantifiers: k_crc32c : Bool, d : Nat, m : Nat, n : Nat, size : Nat, List.elem size
  [8, 16, 32, 64] ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_CRC32_Op_A_txt (crc32c : Bool) (d : Nat) (m : Nat) (n : Nat) (size : Nat) : SailM Unit := do
  let acc ← (( do (R_read n) ) : SailM (BitVec 32) )
  ArmFull.assert ((size -i 1) <b 32) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:42465.37-42465.38"
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let val_name : (BitVec (0 + (size - 1 - 0 + 1))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((size -i 1))) 0))
  let poly : (BitVec 32) :=
    (integer_subrange
      (if (crc32c : Bool)
      then (BitVec.toNat 0x1EDC6F41#32)
      else (BitVec.toNat 0x04C11DB7#32)) 31 0)
  let w__1 ← (( do (BitReverse acc) ) : SailM (BitVec 32) )
  let tempacc : (BitVec (32 + size)) := (Sail.BitVec.castWidth (w__1 +++ (Zeros (n := size))))
  let w__2 ← (( do (BitReverse val_name) ) : SailM (BitVec (0 + (size - 1 - 0 + 1))) )
  let tempval : (BitVec (0 + (size - 1 - 0 + 1) + 32)) :=
    (Sail.BitVec.castWidth (w__2 +++ (Zeros (n := 32))))
  let w__3 ← (( do (Poly32Mod2 (tempacc ^^^ (Sail.BitVec.castWidth tempval)) poly) ) : SailM
    (BitVec 32) )
  let w__4 ← (( do (BitReverse w__3) ) : SailM (BitVec 32) )
  (R_set d w__4)


def PMUEvent (pmuevent : (BitVec 16)) : SailM Unit := do
  (PMUEvent__1 pmuevent 1)


/-- Type quantifiers: pl : Nat, vl : Nat, (is_VL vl) ∧ (is_PL pl) -/
def RestoreTransactionCheckpointParameterised (vl : Nat) (pl : Nat) : SailM Unit := do
  ArmFull.assert ((((((((((((((((vl == 128) || (vl == 256)) || (vl == 384)) || (vl == 512)) || (vl == 640)) || (vl == 768)) || (vl == 896)) || (vl == 1024)) || (vl == 1152)) || (vl == 1280)) || (vl == 1408)) || (vl == 1536)) || (vl == 1664)) || (vl == 1792)) || (vl == 1920)) || (vl == 2048)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:7461.237-7461.238"
  let w__0 ← (( do readReg TSTATE ) : SailM TMState )
  (SP_set w__0.SP)
  let w__1 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg ICC_PMR_EL1 (Mk_ICC_PMR_EL1_Type w__1.ICC_PMR_EL1)
  let w__2 ← (( do readReg TSTATE ) : SailM TMState )
  let split_vec := w__2.nzcv
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  let w__7 ← (( do readReg TSTATE ) : SailM TMState )
  let w__8 ← (( do readReg TSTATE ) : SailM TMState )
  let w__9 ← (( do readReg TSTATE ) : SailM TMState )
  let w__10 ← (( do readReg TSTATE ) : SailM TMState )
  let split_vec := (w__7.D +++ (w__8.A +++ (w__9.I +++ w__10.F)))
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__11 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__12 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__13 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__14 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
  let loop_n_lower : Nat := 0
  let loop_n_upper : Nat := 30
  (do
    let mut loop_vars := ()
    for n in [loop_n_lower:loop_n_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__15 ← (( do readReg TSTATE ) : SailM TMState )
        (X_set n 64 (GetElem?.getElem! w__15.X (Sail.Int.toNatChecked (n))))
    (pure loop_vars))
  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__17 ← (( do (IsFPEnabled w__16.EL) ) : SailM Bool )
  if (w__17 : Bool)
  then
    (do
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__19 ← (( do (IsSVEEnabled w__18.EL) ) : SailM Bool )
      if (w__19 : Bool)
      then
        (do
          let loop_n_lower : Nat := 0
          let loop_n_upper : Nat := 31
          (do
            let mut loop_vars := ()
            for n in [loop_n_lower:loop_n_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__20 ← (( do readReg TSTATE ) : SailM TMState )
                (Z_set n vl
                  (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                    (GetElem?.getElem! w__20.Z (Sail.Int.toNatChecked (n)))
                    (Sail.Int.toNatChecked ((vl -i 1))) 0)))
            (pure loop_vars))
          let loop_n_lower : Nat := 0
          let loop_n_upper : Nat := 15
          (do
            let mut loop_vars := ()
            for n in [loop_n_lower:loop_n_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__21 ← (( do readReg TSTATE ) : SailM TMState )
                (P_set n pl
                  (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                    (GetElem?.getElem! w__21.P (Sail.Int.toNatChecked (n)))
                    (Sail.Int.toNatChecked ((pl -i 1))) 0)))
            (pure loop_vars))
          let w__22 ← (( do readReg TSTATE ) : SailM TMState )
          (FFR_set pl
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__22.FFR
              (Sail.Int.toNatChecked ((pl -i 1))) 0))))
      else
        (do
          let loop_n_lower : Nat := 0
          let loop_n_upper : Nat := 31
          (do
            let mut loop_vars := ()
            for n in [loop_n_lower:loop_n_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                let w__23 ← (( do readReg TSTATE ) : SailM TMState )
                (V_set n 128
                  (Sail.BitVec.extractLsb (GetElem?.getElem! w__23.Z (Sail.Int.toNatChecked (n)))
                    127 0))
            (pure loop_vars)))
      let w__24 ← (( do readReg TSTATE ) : SailM TMState )
      writeReg FPCR (Mk_FPCR_Type w__24.FPCR)
      let w__25 ← (( do readReg TSTATE ) : SailM TMState )
      writeReg FPSR (Mk_FPSR_Type w__25.FPSR))
  else (pure (()))
  let w__26 ← (( do (HaveGCS ()) ) : SailM Bool )
  if (w__26 : Bool)
  then
    (do
      let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
      let questionMark := w__27.EL
      if ((questionMark == EL0) : Bool)
      then
        (do
          let w__28 ← (( do readReg TSTATE ) : SailM TMState )
          writeReg GCSPR_EL0 (Mk_GCSPR_EL0_Type w__28.GCSPR_ELx))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              let w__29 ← (( do readReg TSTATE ) : SailM TMState )
              writeReg GCSPR_EL1 (Mk_GCSPR_EL1_Type w__29.GCSPR_ELx))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  let w__30 ← (( do readReg TSTATE ) : SailM TMState )
                  writeReg GCSPR_EL2 (Mk_GCSPR_EL2_Type w__30.GCSPR_ELx))
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      let w__31 ← (( do readReg TSTATE ) : SailM TMState )
                      writeReg GCSPR_EL3 (Mk_GCSPR_EL3_Type w__31.GCSPR_ELx))
                  else (pure (()))))))
  else (pure (()))


end ArmFull.Functions
