import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0016
import ArmFull.Fn.M0086
import ArmFull.Fn.M0154
import ArmFull.Fn.M0159
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0216
import ArmFull.Fn.M0228
import ArmFull.Fn.M1003
import ArmFull.Fn.M1142

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

/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRB_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_set address 1 (Sail.BitVec.extractLsb w__3 7 0))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRB_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_set address 1 (Sail.BitVec.extractLsb w__3 7 0))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback
  : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_STRB_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let offset ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__2 + offset))))
    else
      (do
        let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__3 - offset)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_set address 1 (Sail.BitVec.extractLsb w__5 7 0))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, shift_n
  : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRBT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (shift_n : Int) (shift_t : SRType) (t : Nat) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let offset ← (( do
    if (register_form : Bool)
    then
      (do
        let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (Shift w__1 shift_t shift_n w__2.C))
    else (pure (imm32)) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__4 + offset))))
    else
      (do
        let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__5 - offset)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then
      (do
        (R_read n))
    else (pure (offset_addr)) ) : SailM (BitVec 32) )
  let w__8 ← (( do
    if ((((! postindex) && (t != 15)) : Bool) : Bool)
    then
      (do
        let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__7.T == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let _ : Unit :=
    if (w__8 : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  let w__9 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_unpriv_set address 1 (Sail.BitVec.extractLsb w__9 7 0))
  if (postindex : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, t2 : Nat, k_wback : Bool, 0
  ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRD_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (t2 : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  if ((IsAligned__1 address 8) : Bool)
  then
    (do
      let data ← (( do (undefined_bitvector_at (← occLabel 3244) 64) ) : SailM (BitVec 64) )
      let w__3 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
      let data ← (( do
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do (R_read t) ) : SailM (BitVec 32) )
            let data := ((Sail.BitVec.updateSubrange data 63 32 w__4) : (BitVec 64))
            let w__5 ← (( do (R_read t2) ) : SailM (BitVec 32) )
            let data := ((Sail.BitVec.updateSubrange data 31 0 w__5) : (BitVec 64))
            (pure (data)))
        else
          (do
            let w__6 ← (( do (R_read t) ) : SailM (BitVec 32) )
            let data := ((Sail.BitVec.updateSubrange data 31 0 w__6) : (BitVec 64))
            let w__7 ← (( do (R_read t2) ) : SailM (BitVec 32) )
            let data := ((Sail.BitVec.updateSubrange data 63 32 w__7) : (BitVec 64))
            (pure (data))) ) : SailM (BitVec 64) )
      (MemA_set address 8 data))
  else
    (do
      let w__8 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (MemA_set address 4 w__8)
      let w__9 ← (( do (R_read t2) ) : SailM (BitVec 32) )
      (MemA_set (BitVec.addInt address 4) 4 w__9))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, t : Nat, t2 : Nat, k_wback :
  Bool, 1 ≤ t2 ∧
  t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_STRD_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (t : Nat) (t2 : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((w__0 + w__1))))
    else
      (do
        let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
        let w__3 ← (( do (R_read m) ) : SailM (BitVec 32) )
        (pure ((w__2 - w__3)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  if ((IsAligned__1 address 8) : Bool)
  then
    (do
      let data ← (( do (undefined_bitvector_at (← occLabel 3245) 64) ) : SailM (BitVec 64) )
      let w__5 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
      let data ← (( do
        if (w__5 : Bool)
        then
          (do
            let w__6 ← (( do (R_read t) ) : SailM (BitVec 32) )
            let data := ((Sail.BitVec.updateSubrange data 63 32 w__6) : (BitVec 64))
            let w__7 ← (( do (R_read t2) ) : SailM (BitVec 32) )
            let data := ((Sail.BitVec.updateSubrange data 31 0 w__7) : (BitVec 64))
            (pure (data)))
        else
          (do
            let w__8 ← (( do (R_read t) ) : SailM (BitVec 32) )
            let data := ((Sail.BitVec.updateSubrange data 31 0 w__8) : (BitVec 64))
            let w__9 ← (( do (R_read t2) ) : SailM (BitVec 32) )
            let data := ((Sail.BitVec.updateSubrange data 63 32 w__9) : (BitVec 64))
            (pure (data))) ) : SailM (BitVec 64) )
      (MemA_set address 8 data))
  else
    (do
      let w__10 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (MemA_set address 4 w__10)
      let w__11 ← (( do (R_read t2) ) : SailM (BitVec 32) )
      (MemA_set (BitVec.addInt address 4) 4 w__11))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STREX_Op_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let address : (BitVec 32) := (w__0 + imm32)
  let w__1 ← (( do (AArch32_ExclusiveMonitorsPass address 4) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (MemA_set address 4 w__2)
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else
    (do
      (R_set d (Sail.BitVec.zeroExtend 1#1 32)))


/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STREXB_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (AArch32_ExclusiveMonitorsPass address 1) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (MemA_set address 1 (Sail.BitVec.extractLsb w__1 7 0))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else
    (do
      (R_set d (Sail.BitVec.zeroExtend 1#1 32)))


/-- Type quantifiers: d : Nat, n : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧
  t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STREXD_Op_A_txt (d : Nat) (n : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
  let value_name ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
        let w__2 ← (( do (R_read t2) ) : SailM (BitVec 32) )
        (pure ((w__1 +++ w__2))))
    else
      (do
        let w__3 ← (( do (R_read t2) ) : SailM (BitVec 32) )
        let w__4 ← (( do (R_read t) ) : SailM (BitVec 32) )
        (pure ((w__3 +++ w__4)))) ) : SailM (BitVec 64) )
  let w__5 ← (( do (AArch32_ExclusiveMonitorsPass address 8) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      (MemA_set address 8 value_name)
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else
    (do
      (R_set d (Sail.BitVec.zeroExtend 1#1 32)))


/-- Type quantifiers: d : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_STREXH_Op_A_txt (d : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__0 ← (( do (AArch32_ExclusiveMonitorsPass address 2) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (MemA_set address 2 (Sail.BitVec.extractLsb w__1 15 0))
      (R_set d (Sail.BitVec.zeroExtend 0#1 32)))
  else
    (do
      (R_set d (Sail.BitVec.zeroExtend 1#1 32)))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRH_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_set address 2 (Sail.BitVec.extractLsb w__3 15 0))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRH_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_set address 2 (Sail.BitVec.extractLsb w__3 15 0))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback
  : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_STRH_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let offset ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__2 + offset))))
    else
      (do
        let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__3 - offset)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let w__5 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_set address 2 (Sail.BitVec.extractLsb w__5 15 0))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, t
  : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRHT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (t : Nat) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let offset ← (( do
    if (register_form : Bool)
    then
      (do
        (R_read m))
    else (pure (imm32)) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__2 + offset))))
    else
      (do
        let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__3 - offset)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then
      (do
        (R_read n))
    else (pure (offset_addr)) ) : SailM (BitVec 32) )
  let w__6 ← (( do
    if (((t != 15) : Bool) : Bool)
    then
      (do
        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__5.T == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let _ : Unit :=
    if (w__6 : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let w__7 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_unpriv_set address 2 (Sail.BitVec.extractLsb w__7 15 0))
  if (postindex : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STR_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let w__5 ← (( do
    if ((t == 15) : Bool)
    then
      (do
        (PCStoreValue ()))
    else
      (do
        (R_read t)) ) : SailM (BitVec (8 * 4)) )
  (MemU_set address 4 w__5)
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STR_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (MemU_set address 4 w__3)
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback
  : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_STR_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let offset ← (( do (Shift w__0 shift_t shift_n w__1.C) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__2 + offset))))
    else
      (do
        let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__3 - offset)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let data ← (( do (undefined_bitvector_at (← occLabel 3259) 32) ) : SailM (BitVec 32) )
  let data ← (( do
    if ((t == 15) : Bool)
    then
      (do
        (PCStoreValue ()))
    else
      (do
        (R_read t)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  (MemU_set address 4 data)
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, shift_n
  : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_STRT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (shift_n : Int) (shift_t : SRType) (t : Nat) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let offset ← (( do
    if (register_form : Bool)
    then
      (do
        let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (Shift w__1 shift_t shift_n w__2.C))
    else (pure (imm32)) ) : SailM (BitVec 32) )
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__4 + offset))))
    else
      (do
        let w__5 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__5 - offset)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (postindex : Bool)
    then
      (do
        (R_read n))
    else (pure (offset_addr)) ) : SailM (BitVec 32) )
  let data ← (( do (undefined_bitvector_at (← occLabel 3266) 32) ) : SailM (BitVec 32) )
  let data ← (( do
    if ((t == 15) : Bool)
    then
      (do
        (PCStoreValue ()))
    else
      (do
        (R_read t)) ) : SailM (BitVec 32) )
  let w__10 ← (( do
    if ((((! postindex) && (t != 15)) : Bool) : Bool)
    then
      (do
        let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__9.T == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let _ : Unit :=
    if (w__10 : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  (MemU_unpriv_set address 4 data)
  if (postindex : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


end ArmFull.Functions
