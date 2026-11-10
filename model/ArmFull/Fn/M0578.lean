import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0087
import ArmFull.Fn.M0115
import ArmFull.Fn.M0150
import ArmFull.Fn.M0159
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0244
import ArmFull.Fn.M0255

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

/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ m ∧
  m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_SP_r_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2938) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2939) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read 13) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__2 shifted 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_AND_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__0 &&& imm32)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (IsZeroBit result) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_AND_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 2952) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 2953) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__3 &&& shifted)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BIC_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__0 &&& (Complement.complement imm32))
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (IsZeroBit result) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_BIC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 2971) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 2972) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__3 &&& (Complement.complement shifted))
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_EOR_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__0 ^^^ imm32)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (IsZeroBit result) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_EOR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3018) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3019) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__3 ^^^ shifted)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, k_setflags : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MOV_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (setflags : Bool) : SailM Unit := do
  let result : (BitVec 32) := imm32
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__0 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with Z := (IsZeroBit result) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ m ∧
  m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MOV_r_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3116) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3117) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let result : (BitVec 32) := shifted
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with Z := (IsZeroBit result) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, k_setflags : Bool, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MVN_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (setflags : Bool) : SailM Unit := do
  let result : (BitVec 32) := (Complement.complement imm32)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__0 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with Z := (IsZeroBit result) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ m ∧
  m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_MVN_r_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3132) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3133) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let result : (BitVec 32) := (Complement.complement shifted)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with Z := (IsZeroBit result) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORR_i_Op_A_txt (carry : (BitVec 1)) (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__0 ||| imm32)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (IsZeroBit result) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ORR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 3152) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 3153) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 shift_t shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__3 ||| shifted)
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                31)])) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with C := carry })
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSB_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3188) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3189) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry (Complement.complement w__0) imm32 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSB_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3190) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3191) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) :=
    ((AddWithCarry (Complement.complement w__2) shifted 1#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSC_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3198) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3199) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) :=
    ((AddWithCarry (Complement.complement w__0) imm32 w__1.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_n : Int, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_RSC_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3200) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3201) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) :=
    ((AddWithCarry (Complement.complement w__2) shifted w__3.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
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
      else (pure (())))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SBC_i_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3206) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 3207) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) :=
    ((AddWithCarry w__0 (Complement.complement imm32) w__1.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if ((d == 15) : Bool)
  then
    (do
      if (setflags : Bool)
      then
        (do
          (ALUExceptionReturn result))
      else
        (do
          (ALUWritePC result)))
  else
    (do
      (R_set d result)
      if (setflags : Bool)
      then
        (do
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__2 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__3 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__4 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__5 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
      else (pure (())))


end ArmFull.Functions
