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

/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QADD_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sat ← (( do (undefined_bool_at (← occLabel 3174) ()) ) : SailM Bool )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (__tup_0, __tup_1) ← (( do (SignedSatQ ((BitVec.toInt w__0) +i (BitVec.toInt w__1)) 32) ) :
    SailM ((BitVec 32) × Bool) )
  (R_set d __tup_0)
  let sat : Bool := __tup_1
  if (sat : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 31 16)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 15 0)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__5 ← (( do (SignedSat diff 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 w__5))
  let w__6 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do (SignedSat sum 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__6 31 16 w__7))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QDADD_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let doubled ← (( do (undefined_bitvector_at (← occLabel 3175) 32) ) : SailM (BitVec 32) )
  let sat1 ← (( do (undefined_bool_at (← occLabel 3176) ()) ) : SailM Bool )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (SignedSatQ (2 *i (BitVec.toInt w__0)) 32) ) : SailM ((BitVec 32) × Bool) )
  let (tup__0, tup__1) := (w__1 : ((BitVec 32) × Bool))
  let doubled : (BitVec 32) := tup__0
  let sat1 : Bool := tup__1
  let sat2 ← (( do (undefined_bool_at (← occLabel 3177) ()) ) : SailM Bool )
  let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let (__tup_0, __tup_1) ← (( do (SignedSatQ ((BitVec.toInt w__2) +i (BitVec.toInt doubled)) 32) )
    : SailM ((BitVec 32) × Bool) )
  (R_set d __tup_0)
  let sat2 : Bool := __tup_1
  if ((sat1 || sat2) : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QDSUB_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let doubled ← (( do (undefined_bitvector_at (← occLabel 3178) 32) ) : SailM (BitVec 32) )
  let sat1 ← (( do (undefined_bool_at (← occLabel 3179) ()) ) : SailM Bool )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (SignedSatQ (2 *i (BitVec.toInt w__0)) 32) ) : SailM ((BitVec 32) × Bool) )
  let (tup__0, tup__1) := (w__1 : ((BitVec 32) × Bool))
  let doubled : (BitVec 32) := tup__0
  let sat1 : Bool := tup__1
  let sat2 ← (( do (undefined_bool_at (← occLabel 3180) ()) ) : SailM Bool )
  let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let (__tup_0, __tup_1) ← (( do (SignedSatQ ((BitVec.toInt w__2) -i (BitVec.toInt doubled)) 32) )
    : SailM ((BitVec 32) × Bool) )
  (R_set d __tup_0)
  let sat2 : Bool := __tup_1
  if ((sat1 || sat2) : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 31 16)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 15 0)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__5 ← (( do (SignedSat sum 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 w__5))
  let w__6 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do (SignedSat diff 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__6 31 16 w__7))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__5 ← (( do (SignedSat diff1 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 w__5))
  let w__6 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__7 ← (( do (SignedSat diff2 16) ) : SailM (BitVec 16) )
  (R_set d (Sail.BitVec.updateSubrange w__6 31 16 w__7))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 7 0)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 8)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff3 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__4 23 16)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff4 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__6 31 24)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__7 31 24)))
  let w__8 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__9 ← (( do (SignedSat diff1 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 w__9))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__11 ← (( do (SignedSat diff2 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__10 15 8 w__11))
  let w__12 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__13 ← (( do (SignedSat diff3 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__12 23 16 w__13))
  let w__14 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__15 ← (( do (SignedSat diff4 8) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__14 31 24 w__15))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_QSUB_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let sat ← (( do (undefined_bool_at (← occLabel 3181) ()) ) : SailM Bool )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (__tup_0, __tup_1) ← (( do (SignedSatQ ((BitVec.toInt w__0) -i (BitVec.toInt w__1)) 32) ) :
    SailM ((BitVec 32) × Bool) )
  (R_set d __tup_0)
  let sat : Bool := __tup_1
  if (sat : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RBIT_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector_at (← occLabel 3182) 32) ) : SailM (BitVec 32) )
  let result ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 31
    (do
      let mut loop_vars := result
      for i in [loop_i_lower:loop_i_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
          let result :=
            ((BitVec.update result (Sail.Int.toNatChecked ((31 -i i)))
              (Bit
                (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__0 (Sail.Int.toNatChecked (i)))])))) : (BitVec 32))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  (R_set d result)


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_REV16_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector_at (← occLabel 3183) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 31 24 (Sail.BitVec.extractLsb w__0 23 16)) : (BitVec 32))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 23 16 (Sail.BitVec.extractLsb w__1 31 24)) : (BitVec 32))
  let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 15 8 (Sail.BitVec.extractLsb w__2 7 0)) : (BitVec 32))
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 7 0 (Sail.BitVec.extractLsb w__3 15 8)) : (BitVec 32))
  (R_set d result)


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_REV_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector_at (← occLabel 3184) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 31 24 (Sail.BitVec.extractLsb w__0 7 0)) : (BitVec 32))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 23 16 (Sail.BitVec.extractLsb w__1 15 8)) : (BitVec 32))
  let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 15 8 (Sail.BitVec.extractLsb w__2 23 16)) : (BitVec 32))
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 7 0 (Sail.BitVec.extractLsb w__3 31 24)) : (BitVec 32))
  (R_set d result)


/-- Type quantifiers: d : Nat, m : Nat, 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_REVSH_Op_A_txt (d : Nat) (m : Nat) : SailM Unit := do
  let result ← (( do (undefined_bitvector_at (← occLabel 3185) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 31 8 (sign_extend (Sail.BitVec.extractLsb w__0 7 0) 24)) : (BitVec 32))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result :=
    ((Sail.BitVec.updateSubrange result 7 0 (Sail.BitVec.extractLsb w__1 15 8)) : (BitVec 32))
  (R_set d result)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, List.elem n
  [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_ROR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3186) 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3187) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 SRType_ROR shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1))
    )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let result : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSB_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3196) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3197) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__1 shift_t shift_n w__2.C) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry (Complement.complement w__3) shifted 1#1) : ((BitVec 32) × (BitVec 4)))
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


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSC_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3204) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3205) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__1 shift_t shift_n w__2.C) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) :=
    ((AddWithCarry (Complement.complement w__3) shifted w__4.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange sum1 15 0)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange sum2 15 0)))
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with GE := (Sail.BitVec.updateSubrange w__7.GE 1 0
      (if ((sum1 ≥b 0) : Bool)
      then 0b11#2
      else 0b00#2)) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with GE := (Sail.BitVec.updateSubrange w__9.GE 3 2
      (if ((sum2 ≥b 0) : Bool)
      then 0b11#2
      else 0b00#2)) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 7 0)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 8)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum3 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__4 23 16)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum4 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__6 31 24)) +i (BitVec.toInt
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
        (if ((sum1 ≥b 0) : Bool)
        then 1#1
        else 0#1))) }
  let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__14 with GE := (BitVec.update w__15.GE 1
      (Bit
        (if ((sum2 ≥b 0) : Bool)
        then 1#1
        else 0#1))) }
  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__16 with GE := (BitVec.update w__17.GE 2
      (Bit
        (if ((sum3 ≥b 0) : Bool)
        then 1#1
        else 0#1))) }
  let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__18 with GE := (BitVec.update w__19.GE 3
      (Bit
        (if ((sum4 ≥b 0) : Bool)
        then 1#1
        else 0#1))) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let diff : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) -i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 31 16)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toInt
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
      (if ((sum ≥b 0) : Bool)
      then 0b11#2
      else 0b00#2)) }


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SBC_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3216) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3217) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__1 shift_t shift_n w__2.C) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__3 (Complement.complement shifted) w__4.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


/-- Type quantifiers: d : Nat, lsbit : Nat, msbit : Int, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ lsbit ∧ lsbit ≤ 31 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SBFX_Op_A_txt (d : Nat) (lsbit : Nat) (msbit : Int) (n : Nat) : SailM Unit := do
  ArmFull.assert ((lsbit ≤b msbit) && (msbit <b 32)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:11111.55-11111.56"
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  (R_set d (sign_extend (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked (msbit)) lsbit) 32))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SDIV_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let result ← (( do (undefined_int_at (← occLabel 3218) ()) ) : SailM Int )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result ← (( do
    if (((BitVec.toInt w__0) == 0) : Bool)
    then (pure (0))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
        let result : Int :=
          ((RoundTowardsZero (div_real (to_real (BitVec.toInt w__1)) (to_real (BitVec.toInt w__2)))) : Int)
        (pure (result))) ) : SailM Int )
  let result : Int := result
  (R_set d (integer_subrange result 31 0))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SEL_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__4 ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__1.GE 0)])) == 1#1) : Bool)
    then
      (do
        let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__2 7 0))))
    else
      (do
        let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__3 7 0)))) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__0 7 0 w__4))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__9 ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__6.GE 1)])) == 1#1) : Bool)
    then
      (do
        let w__7 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__7 15 8))))
    else
      (do
        let w__8 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__8 15 8)))) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__5 15 8 w__9))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__14 ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__11.GE 2)])) == 1#1) : Bool)
    then
      (do
        let w__12 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__12 23 16))))
    else
      (do
        let w__13 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__13 23 16)))) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__10 23 16 w__14))
  let w__15 ← (( do (R_read d) ) : SailM (BitVec 32) )
  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__19 ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__16.GE 3)])) == 1#1) : Bool)
    then
      (do
        let w__17 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__17 31 24))))
    else
      (do
        let w__18 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__18 31 24)))) ) : SailM (BitVec 8) )
  (R_set d (Sail.BitVec.updateSubrange w__15 31 24 w__19))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHADD16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 15 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 31 16)))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange sum1 16 1)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange sum2 16 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHADD8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__0 7 0)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__1 7 0)))
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 8)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__3 15 8)))
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum3 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__4 23 16)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__5 23 16)))
  let w__6 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__7 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let sum4 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__6 31 24)) +i (BitVec.toInt
        (Sail.BitVec.extractLsb w__7 31 24)))
  let w__8 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 (integer_subrange sum1 8 1)))
  let w__9 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__9 15 8 (integer_subrange sum2 8 1)))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__10 23 16 (integer_subrange sum3 8 1)))
  let w__11 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__11 31 24 (integer_subrange sum4 8 1)))


end ArmFull.Functions
