import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0115
import ArmFull.Fn.M0150
import ArmFull.Fn.M0159
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203

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

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SUB_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3286) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3287) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__1 shift_t shift_n w__2.C) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__3 (Complement.complement shifted) 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTAB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  let w__1 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange w__1 15 0
      ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb w__2 15 0)) + (Sail.BitVec.castWidth (m := 16) (sign_extend
          (Sail.BitVec.extractLsb rotated 7 0) 16)))))
  let w__3 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange w__3 31 16
      ((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb w__4 31 16)) + (Sail.BitVec.castWidth (m := 16) (sign_extend
          (Sail.BitVec.extractLsb rotated 23 16) 16)))))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTAB_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (w__1 + (Sail.BitVec.castWidth (m := 32) (sign_extend (Sail.BitVec.extractLsb rotated 7 0) 32))))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTAH_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (w__1 + (Sail.BitVec.castWidth (m := 32) (sign_extend (Sail.BitVec.extractLsb rotated 15 0) 32))))


/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTB16_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  let w__1 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange w__1 15 0 (sign_extend (Sail.BitVec.extractLsb rotated 7 0) 16)))
  let w__2 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.updateSubrange w__2 31 16 (sign_extend (Sail.BitVec.extractLsb rotated 23 16) 16)))


/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTB_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  (R_set d (sign_extend (Sail.BitVec.extractLsb rotated 7 0) 32))


/-- Type quantifiers: d : Nat, m : Nat, rotation : Nat, 0 ≤ rotation ∧
  rotation ≤ 31 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SXTH_Op_A_txt (d : Nat) (m : Nat) (rotation : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let rotated : (BitVec 32) := (ROR w__0 rotation)
  (R_set d (sign_extend (Sail.BitVec.extractLsb rotated 15 0) 32))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_TEQ_i_Op_A_txt (carry : (BitVec 1)) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__0 ^^^ imm32)
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with Z := (IsZeroBit result) }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with C := carry }


/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TEQ_r_Op_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3301) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3302) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__3 ^^^ shifted)
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with C := carry }


/-- Type quantifiers: m : Nat, n : Nat, s : Nat, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TEQ_rr_Op_A_txt (m : Nat) (n : Nat) (s : Nat) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3307) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3308) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 shift_t shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__4 ^^^ shifted)
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (IsZeroBit result) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := carry }


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_TST_i_Op_A_txt (carry : (BitVec 1)) (imm32 : (BitVec 32)) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__0 &&& imm32)
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with Z := (IsZeroBit result) }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with C := carry }


/-- Type quantifiers: m : Nat, n : Nat, shift_n : Int, 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TST_r_Op_A_txt (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3313) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3314) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__3 &&& shifted)
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with C := carry }


/-- Type quantifiers: m : Nat, n : Nat, s : Nat, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_TST_rr_Op_A_txt (m : Nat) (n : Nat) (s : Nat) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3321) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3322) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 shift_t shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__4 &&& shifted)
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (IsZeroBit result) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := carry }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange sum1 15 0)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange sum2 15 0)))
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with GE := (Sail.BitVec.updateSubrange w__7.GE 1 0
      (if ((sum1 ≥b (BitVec.toNat 0x10000#20)) : Bool)
      then 0b11#2
      else 0b00#2)) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with GE := (Sail.BitVec.updateSubrange w__9.GE 3 2
      (if ((sum2 ≥b (BitVec.toNat 0x10000#20)) : Bool)
      then 0b11#2
      else 0b00#2)) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 15 8)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum3 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__4 23 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum4 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__6 31 24)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__7 31 24)))
  let w__8 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 (integer_subrange sum1 7 0)))
  let w__9 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__9 15 8 (integer_subrange sum2 7 0)))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__10 23 16 (integer_subrange sum3 7 0)))
  let w__11 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__11 31 24 (integer_subrange sum4 7 0)))
  let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__12 with GE := (BitVec.update w__13.GE 0
      (Bit
        (if ((sum1 ≥b (BitVec.toNat 0x100#12)) : Bool)
        then 1#1
        else 0#1))) }
  let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__14 with GE := (BitVec.update w__15.GE 1
      (Bit
        (if ((sum2 ≥b (BitVec.toNat 0x100#12)) : Bool)
        then 1#1
        else 0#1))) }
  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__16 with GE := (BitVec.update w__17.GE 2
      (Bit
        (if ((sum3 ≥b (BitVec.toNat 0x100#12)) : Bool)
        then 1#1
        else 0#1))) }
  let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__18 with GE := (BitVec.update w__19.GE 3
      (Bit
        (if ((sum4 ≥b (BitVec.toNat 0x100#12)) : Bool)
        then 1#1
        else 0#1))) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 31 16)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 0)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange diff 15 0)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange sum 15 0)))
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with GE := (Sail.BitVec.updateSubrange w__7.GE 1 0
      (if ((diff ≥b 0) : Bool)
      then 0b11#2
      else 0b00#2)) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with GE := (Sail.BitVec.updateSubrange w__9.GE 3 2
      (if ((sum ≥b (BitVec.toNat 0x10000#20)) : Bool)
      then 0b11#2
      else 0b00#2)) }


/-- Type quantifiers: d : Nat, lsbit : Nat, msbit : Int, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ lsbit ∧ lsbit ≤ 31 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UBFX_Op_A_txt (d : Nat) (lsbit : Nat) (msbit : Int) (n : Nat) : SailM Unit := do
  ArmFull.assert ((lsbit ≤b msbit) && (msbit <b 32)) "sail-arm/instrs32.sail:17195.55-17195.56"
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d
    (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked (msbit)) lsbit) 32))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UDIV_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let result ← (( do (undefined_int_at (← occLabel 3323) ()) ) : SailM Int )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result ← (( do
    if (((BitVec.toNat w__0) == 0) : Bool)
    then (pure (0))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
        let result : Int :=
          ((RoundTowardsZero (div_real (to_real (BitVec.toNat w__1)) (to_real (BitVec.toNat w__2)))) : Int)
        (pure (result))) ) : SailM Int )
  let result : Int := result
  (R_set d (integer_subrange result 31 0))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange sum1 16 1)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange sum2 16 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 15 8)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum3 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__4 23 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum4 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__6 31 24)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__7 31 24)))
  let w__8 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 (integer_subrange sum1 8 1)))
  let w__9 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__9 15 8 (integer_subrange sum2 8 1)))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__10 23 16 (integer_subrange sum3 8 1)))
  let w__11 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__11 31 24 (integer_subrange sum4 8 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 31 16)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 0)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange diff 16 1)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange sum 16 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange sum 16 1)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange diff 16 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange diff1 16 1)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange diff2 16 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UHSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 (integer_subrange diff1 8 1)))
  let w__9 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__9 15 8 (integer_subrange diff2 8 1)))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__10 23 16 (integer_subrange diff3 8 1)))
  let w__11 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__11 31 24 (integer_subrange diff4 8 1)))


/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_UMAAL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read dHi) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read dLo) ) : SailM (BitVec 32) )
  let result : Int :=
    ((((BitVec.toNat w__0) *i (BitVec.toNat w__1)) +i (BitVec.toNat w__2)) +i (BitVec.toNat w__3))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))


/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_UMLAL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read dHi) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read dLo) ) : SailM (BitVec 32) )
  let result : Int :=
    (((BitVec.toNat w__0) *i (BitVec.toNat w__1)) +i (BitVec.toNat (w__2 +++ w__3)))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(integer_access result 63)])) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (IsZeroBit (integer_subrange result 63 0)) })
  else (pure (()))


/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_UMULL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result : Int := ((BitVec.toNat w__0) *i (BitVec.toNat w__1))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))
  if (setflags : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with N := (BitVec.setWidth 1 (BitVec.join1 [(integer_access result 63)])) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Z := (IsZeroBit (integer_subrange result 63 0)) })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__5 ← (( do (UnsignedSat sum1 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 w__5))
  let w__6 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do (UnsignedSat sum2 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__6 31 16 w__7))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 15 8)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum3 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__4 23 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum4 : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__6 31 24)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__7 31 24)))
  let w__8 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__9 ← (( do (UnsignedSat sum1 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 w__9))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__11 ← (( do (UnsignedSat sum2 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__10 15 8 w__11))
  let w__12 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__13 ← (( do (UnsignedSat sum3 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__12 23 16 w__13))
  let w__14 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__15 ← (( do (UnsignedSat sum4 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__14 31 24 w__15))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_UQASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__0 15 0)) -i (BitVec.toNat
        (Sail.BitVec.extractLsb w__1 31 16)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum : Int :=
    ((BitVec.toNat (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toNat
        (Sail.BitVec.extractLsb w__3 15 0)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__5 ← (( do (UnsignedSat diff 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 w__5))
  let w__6 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do (UnsignedSat sum 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__6 31 16 w__7))


end ArmFull.Functions
