import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0115
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
def execute_aarch32_instrs_SHASX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange diff 16 1)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange sum 16 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange sum 16 1)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange diff 16 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange diff1 16 1)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange diff2 16 1)))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SHSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
  (R_set d (Sail.BitVec.updateSubrange w__8 7 0 (integer_subrange diff1 8 1)))
  let w__9 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__9 15 8 (integer_subrange diff2 8 1)))
  let w__10 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__10 23 16 (integer_subrange diff3 8 1)))
  let w__11 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__11 31 24 (integer_subrange diff4 8 1)))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, k_m_high : Bool, n : Nat, k_n_high : Bool, 0 ≤ n
  ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMLABB_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (m_high : Bool) (n : Nat) (n_high : Bool) : SailM Unit := do
  let operand1 ← (( do
    if (n_high : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__0 31 16))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__1 15 0)))) ) : SailM (BitVec 16) )
  let operand2 ← (( do
    if (m_high : Bool)
    then
      (do
        let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__2 31 16))))
    else
      (do
        let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__3 15 0)))) ) : SailM (BitVec 16) )
  let w__4 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let result : Int := (((BitVec.toInt operand1) *i (BitVec.toInt operand2)) +i (BitVec.toInt w__4))
  (R_set d (integer_subrange result 31 0))
  if ((result != (BitVec.toInt (integer_subrange result 31 0))) : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMLAD_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then
      (do
        let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((ROR w__0 16))))
    else
      (do
        (R_read m)) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 0)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 15 0)))
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__3 31 16)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 31 16)))
  let w__4 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let result : Int := ((product1 +i product2) +i (BitVec.toInt w__4))
  (R_set d (integer_subrange result 31 0))
  if ((result != (BitVec.toInt (integer_subrange result 31 0))) : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMLAL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read dHi) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read dLo) ) : SailM (BitVec 32) )
  let result : Int :=
    (((BitVec.toInt w__0) *i (BitVec.toInt w__1)) +i (BitVec.toInt (w__2 +++ w__3)))
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


/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, k_m_high : Bool, n : Nat, k_n_high : Bool, 0
  ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMLALBB_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (m_high : Bool) (n : Nat) (n_high : Bool) : SailM Unit := do
  let operand1 ← (( do
    if (n_high : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__0 31 16))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__1 15 0)))) ) : SailM (BitVec 16) )
  let operand2 ← (( do
    if (m_high : Bool)
    then
      (do
        let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__2 31 16))))
    else
      (do
        let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__3 15 0)))) ) : SailM (BitVec 16) )
  let w__4 ← (( do (R_read dHi) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read dLo) ) : SailM (BitVec 32) )
  let result : Int :=
    (((BitVec.toInt operand1) *i (BitVec.toInt operand2)) +i (BitVec.toInt (w__4 +++ w__5)))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))


/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMLALD_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then
      (do
        let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((ROR w__0 16))))
    else
      (do
        (R_read m)) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 0)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 15 0)))
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__3 31 16)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 31 16)))
  let w__4 ← (( do (R_read dHi) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read dLo) ) : SailM (BitVec 32) )
  let result : Int := ((product1 +i product2) +i (BitVec.toInt (w__4 +++ w__5)))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, k_m_high : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMLAWB_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (m_high : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_high : Bool)
    then
      (do
        let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__0 31 16))))
    else
      (do
        let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__1 15 0)))) ) : SailM (BitVec 16) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let result : Int :=
    (((BitVec.toInt w__2) *i (BitVec.toInt operand2)) +i (Int.shiftl (BitVec.toInt w__3) 16))
  (R_set d (integer_subrange result 47 16))
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  if (((Int.shiftr result 16) != (BitVec.toInt w__4)) : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMLSD_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then
      (do
        let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((ROR w__0 16))))
    else
      (do
        (R_read m)) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 0)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 15 0)))
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__3 31 16)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 31 16)))
  let w__4 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let result : Int := ((product1 -i product2) +i (BitVec.toInt w__4))
  (R_set d (integer_subrange result 31 0))
  if ((result != (BitVec.toInt (integer_subrange result 31 0))) : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMLSLD_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then
      (do
        let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((ROR w__0 16))))
    else
      (do
        (R_read m)) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 0)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 15 0)))
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__3 31 16)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 31 16)))
  let w__4 ← (( do (R_read dHi) ) : SailM (BitVec 32) )
  let w__5 ← (( do (R_read dLo) ) : SailM (BitVec 32) )
  let result : Int := ((product1 -i product2) +i (BitVec.toInt (w__4 +++ w__5)))
  (R_set dHi (integer_subrange result 63 32))
  (R_set dLo (integer_subrange result 31 0))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, k_round : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMMLA_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) (round : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result : Int :=
    ((Int.shiftl (BitVec.toInt w__0) 32) +i ((BitVec.toInt w__1) *i (BitVec.toInt w__2)))
  let result : Int :=
    if (round : Bool)
    then (result +i (BitVec.toNat 0x80000000#32))
    else result
  let result : Int := result
  (R_set d (integer_subrange result 63 32))


/-- Type quantifiers: a : Nat, d : Nat, m : Nat, n : Nat, k_round : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ 0 ≤ a ∧ a ≤ 15 -/
def execute_aarch32_instrs_SMMLS_Op_A_txt (a : Nat) (d : Nat) (m : Nat) (n : Nat) (round : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read a) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result : Int :=
    ((Int.shiftl (BitVec.toInt w__0) 32) -i ((BitVec.toInt w__1) *i (BitVec.toInt w__2)))
  let result : Int :=
    if (round : Bool)
    then (result +i (BitVec.toNat 0x80000000#32))
    else result
  let result : Int := result
  (R_set d (integer_subrange result 63 32))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_round : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMMUL_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (round : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result : Int := ((BitVec.toInt w__0) *i (BitVec.toInt w__1))
  let result : Int :=
    if (round : Bool)
    then (result +i (BitVec.toNat 0x80000000#32))
    else result
  let result : Int := result
  (R_set d (integer_subrange result 63 32))


/-- Type quantifiers: d : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMUAD_Op_A_txt (d : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then
      (do
        let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((ROR w__0 16))))
    else
      (do
        (R_read m)) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 0)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 15 0)))
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__3 31 16)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 31 16)))
  let result : Int := (product1 +i product2)
  (R_set d (integer_subrange result 31 0))
  if ((result != (BitVec.toInt (integer_subrange result 31 0))) : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, k_m_high : Bool, n : Nat, k_n_high : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMULBB_Op_A_txt (d : Nat) (m : Nat) (m_high : Bool) (n : Nat) (n_high : Bool) : SailM Unit := do
  let operand1 ← (( do
    if (n_high : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__0 31 16))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__1 15 0)))) ) : SailM (BitVec 16) )
  let operand2 ← (( do
    if (m_high : Bool)
    then
      (do
        let w__2 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__2 31 16))))
    else
      (do
        let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__3 15 0)))) ) : SailM (BitVec 16) )
  let result : Int := ((BitVec.toInt operand1) *i (BitVec.toInt operand2))
  (R_set d (integer_subrange result 31 0))


/-- Type quantifiers: dHi : Nat, dLo : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ dLo ∧ dLo ≤ 15 ∧ 0 ≤ dHi ∧ dHi ≤ 15 -/
def execute_aarch32_instrs_SMULL_Op_A_txt (dHi : Nat) (dLo : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let result : Int := ((BitVec.toInt w__0) *i (BitVec.toInt w__1))
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


/-- Type quantifiers: d : Nat, m : Nat, k_m_high : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMULWB_Op_A_txt (d : Nat) (m : Nat) (m_high : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_high : Bool)
    then
      (do
        let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__0 31 16))))
    else
      (do
        let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((Sail.BitVec.extractLsb w__1 15 0)))) ) : SailM (BitVec 16) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product : Int := ((BitVec.toInt w__2) *i (BitVec.toInt operand2))
  (R_set d (integer_subrange product 47 16))


/-- Type quantifiers: d : Nat, m : Nat, k_m_swap : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SMUSD_Op_A_txt (d : Nat) (m : Nat) (m_swap : Bool) (n : Nat) : SailM Unit := do
  let operand2 ← (( do
    if (m_swap : Bool)
    then
      (do
        let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((ROR w__0 16))))
    else
      (do
        (R_read m)) ) : SailM (BitVec 32) )
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product1 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__2 15 0)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 15 0)))
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let product2 : Int :=
    ((BitVec.toInt (Sail.BitVec.extractLsb w__3 31 16)) *i (BitVec.toInt
        (Sail.BitVec.extractLsb operand2 31 16)))
  let result : Int := (product1 -i product2)
  (R_set d (integer_subrange result 31 0))


/-- Type quantifiers: d : Nat, n : Nat, saturate_to : Nat, 1 ≤ saturate_to ∧
  saturate_to ≤ 16 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SSAT16_Op_A_txt (d : Nat) (n : Nat) (saturate_to : Nat) : SailM Unit := do
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3219)
      (Sail.Int.toNatChecked (saturate_to)))) ) : SailM (BitVec saturate_to) )
  let result2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3220)
      (Sail.Int.toNatChecked (saturate_to)))) ) : SailM (BitVec saturate_to) )
  let sat1 ← (( do (undefined_bool_at (← occLabel 3221) ()) ) : SailM Bool )
  let sat2 ← (( do (undefined_bool_at (← occLabel 3222) ()) ) : SailM Bool )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ
      (BitVec.toInt (Sail.BitVec.extractLsb w__0 15 0)) saturate_to)) ) : SailM
    ((BitVec saturate_to) × Bool) )
  let (tup__0, tup__1) := (w__1 : ((BitVec saturate_to) × Bool))
  let result1 : (BitVec saturate_to) := tup__0
  let sat1 : Bool := tup__1
  let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__3 ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ
      (BitVec.toInt (Sail.BitVec.extractLsb w__2 31 16)) saturate_to)) ) : SailM
    ((BitVec saturate_to) × Bool) )
  let (tup__0, tup__1) := (w__3 : ((BitVec saturate_to) × Bool))
  let result2 : (BitVec saturate_to) := tup__0
  let sat2 : Bool := tup__1
  let w__4 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (sign_extend result1 16)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (sign_extend result2 16)))
  if ((sat1 || sat2) : Bool)
  then
    (do
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, saturate_to : Nat, shift_n : Int, 1 ≤ saturate_to ∧
  saturate_to ≤ 32 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SSAT_Op_A_txt (d : Nat) (n : Nat) (saturate_to : Nat) (shift_n : Int) (shift_t : SRType) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3223)
      (Sail.Int.toNatChecked (saturate_to)))) ) : SailM (BitVec saturate_to) )
  let sat ← (( do (undefined_bool_at (← occLabel 3224) ()) ) : SailM Bool )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let operand ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let w__2 ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ (BitVec.toInt operand)
      saturate_to)) ) : SailM ((BitVec saturate_to) × Bool) )
  let (tup__0, tup__1) := (w__2 : ((BitVec saturate_to) × Bool))
  let result : (BitVec saturate_to) := tup__0
  let sat : Bool := tup__1
  (R_set d (sign_extend result 32))
  if (sat : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Q := 1#1 })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_SSAX_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
  (R_set d (Sail.BitVec.updateSubrange w__4 15 0 (integer_subrange sum 15 0)))
  let w__5 ← (( do (R_read d) ) : SailM (BitVec 32) )
  (R_set d (Sail.BitVec.updateSubrange w__5 31 16 (integer_subrange diff 15 0)))
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with GE := (Sail.BitVec.updateSubrange w__7.GE 1 0
      (if ((sum ≥b 0) : Bool)
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
def execute_aarch32_instrs_SSUB16_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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
def execute_aarch32_instrs_SSUB8_Op_A_txt (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
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


end ArmFull.Functions
