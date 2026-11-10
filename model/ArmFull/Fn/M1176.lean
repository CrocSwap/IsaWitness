import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0016
import ArmFull.Fn.M0086
import ArmFull.Fn.M0144
import ArmFull.Fn.M0154
import ArmFull.Fn.M0159
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0244
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
def execute_aarch32_instrs_LDRB_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
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
  let w__3 ← (( do (MemU_read address 1) ) : SailM (BitVec (8 * 1)) )
  (R_set t (Sail.BitVec.zeroExtend w__3 32))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDRB_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
  let base : (BitVec 32) := (Align_bits w__0 4)
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  let w__1 ← (( do (MemU_read address 1) ) : SailM (BitVec (8 * 1)) )
  (R_set t (Sail.BitVec.zeroExtend w__1 32))


/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback
  : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDRB_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
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
  let w__5 ← (( do (MemU_read address 1) ) : SailM (BitVec (8 * 1)) )
  (R_set t (Sail.BitVec.zeroExtend w__5 32))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, shift_n
  : Int, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRBT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (shift_n : Int) (shift_t : SRType) (t : Nat) : SailM Unit := do
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
  let w__9 ← (( do (MemU_unpriv_read address 1) ) : SailM (BitVec (8 * 1)) )
  (R_set t (Sail.BitVec.zeroExtend w__9 32))
  if (postindex : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, t2 : Nat, k_wback : Bool, 0
  ≤ t2 ∧ t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRD_i_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (t2 : Nat) (wback : Bool) : SailM Unit := do
  let data ← (( do (undefined_bitvector_at (← occLabel 3043) 64) ) : SailM (BitVec 64) )
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
      let data ← (( do (MemA_read address 8) ) : SailM (BitVec 64) )
      let w__3 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (R_set t (Sail.BitVec.extractLsb data 63 32))
          (R_set t2 (Sail.BitVec.extractLsb data 31 0)))
      else
        (do
          (R_set t (Sail.BitVec.extractLsb data 31 0))
          (R_set t2 (Sail.BitVec.extractLsb data 63 32))))
  else
    (do
      let w__4 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
      (R_set t w__4)
      let w__5 ← (( do (MemA_read (BitVec.addInt address 4) 4) ) : SailM (BitVec (8 * 4)) )
      (R_set t2 w__5))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, t : Nat, t2 : Nat, 0 ≤ t2 ∧
  t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDRD_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) (t2 : Nat) : SailM Unit := do
  let data ← (( do (undefined_bitvector_at (← occLabel 3044) 64) ) : SailM (BitVec 64) )
  let address ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure (((Align_bits w__0 4) + imm32))))
    else
      (do
        let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure (((Align_bits w__1 4) - imm32)))) ) : SailM (BitVec 32) )
  if ((IsAligned__1 address 8) : Bool)
  then
    (do
      let data ← (( do (MemA_read address 8) ) : SailM (BitVec 64) )
      let w__2 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          (R_set t (Sail.BitVec.extractLsb data 63 32))
          (R_set t2 (Sail.BitVec.extractLsb data 31 0)))
      else
        (do
          (R_set t (Sail.BitVec.extractLsb data 31 0))
          (R_set t2 (Sail.BitVec.extractLsb data 63 32))))
  else
    (do
      let w__3 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
      (R_set t w__3)
      let w__4 ← (( do (MemA_read (BitVec.addInt address 4) 4) ) : SailM (BitVec (8 * 4)) )
      (R_set t2 w__4))


/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, t : Nat, t2 : Nat, k_wback :
  Bool, 1 ≤ t2 ∧
  t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDRD_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (t : Nat) (t2 : Nat) (wback : Bool) : SailM Unit := do
  let data ← (( do (undefined_bitvector_at (← occLabel 3045) 64) ) : SailM (BitVec 64) )
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
      let data ← (( do (MemA_read address 8) ) : SailM (BitVec 64) )
      let w__5 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          (R_set t (Sail.BitVec.extractLsb data 63 32))
          (R_set t2 (Sail.BitVec.extractLsb data 31 0)))
      else
        (do
          (R_set t (Sail.BitVec.extractLsb data 31 0))
          (R_set t2 (Sail.BitVec.extractLsb data 63 32))))
  else
    (do
      let w__6 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
      (R_set t w__6)
      let w__7 ← (( do (MemA_read (BitVec.addInt address 4) 4) ) : SailM (BitVec (8 * 4)) )
      (R_set t2 w__7))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDREX_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let address : (BitVec 32) := (w__0 + imm32)
  (AArch32_SetExclusiveMonitors address 4)
  let w__1 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
  (R_set t w__1)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDREXB_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 1)
  let w__0 ← (( do (MemA_read address 1) ) : SailM (BitVec (8 * 1)) )
  (R_set t (Sail.BitVec.zeroExtend w__0 32))


/-- Type quantifiers: n : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧
  t2 ≤ 16 ∧ 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDREXD_Op_A_txt (n : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 8)
  let value_name ← (( do (MemA_read address 8) ) : SailM (BitVec 64) )
  let w__0 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
  let w__1 : (BitVec 32) :=
    if (w__0 : Bool)
    then (Sail.BitVec.extractLsb value_name 63 32)
    else (Sail.BitVec.extractLsb value_name 31 0)
  (R_set t w__1)
  let w__2 ← (( do (BigEndian AccessType_GPR) ) : SailM Bool )
  let w__3 : (BitVec 32) :=
    if (w__2 : Bool)
    then (Sail.BitVec.extractLsb value_name 31 0)
    else (Sail.BitVec.extractLsb value_name 63 32)
  (R_set t2 w__3)


/-- Type quantifiers: n : Nat, t : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDREXH_Op_A_txt (n : Nat) (t : Nat) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  (AArch32_SetExclusiveMonitors address 2)
  let w__0 ← (( do (MemA_read address 2) ) : SailM (BitVec (8 * 2)) )
  (R_set t (Sail.BitVec.zeroExtend w__0 32))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRH_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
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
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))
  (R_set t (Sail.BitVec.zeroExtend data 32))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRH_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
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
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))
  (R_set t (Sail.BitVec.zeroExtend data 32))


/-- Type quantifiers: k_add : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDRH_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
  let base : (BitVec 32) := (Align_bits w__0 4)
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  (R_set t (Sail.BitVec.zeroExtend data 32))


/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback
  : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDRH_r_Op_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
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
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let data ← (( do (MemU_read address 2) ) : SailM (BitVec 16) )
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))
  (R_set t (Sail.BitVec.zeroExtend data 32))


/-- Type quantifiers: k_add : Bool, m : Int, n : Nat, k_postindex : Bool, k_register_form : Bool, t
  : Nat, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRHT_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (m : Int) (n : Nat) (postindex : Bool) (register_form : Bool) (t : Nat) : SailM Unit := do
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
    if ((((! postindex) && (t != 15)) : Bool) : Bool)
    then
      (do
        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__5.T == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let _ : Unit :=
    if (w__6 : Bool)
    then (AArch32_SetLSInstructionSyndrome 2 false t false)
    else ()
  let data ← (( do (MemU_unpriv_read address 2) ) : SailM (BitVec 16) )
  if (postindex : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))
  (R_set t (Sail.BitVec.zeroExtend data 32))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDR_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
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
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb address 1 0)) == 0b00#2) : Bool)
      then
        (do
          (LoadWritePC data))
      else sailThrow ((Error_Unpredictable ())))
  else
    (do
      (R_set t data))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDR_i_OpT_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
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
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb address 1 0)) == 0b00#2) : Bool)
      then
        (do
          (LoadWritePC data))
      else sailThrow ((Error_Unpredictable ())))
  else
    (do
      (R_set t data))


/-- Type quantifiers: k_add : Bool, t : Nat, 0 ≤ t ∧ t ≤ 15 -/
def execute_aarch32_instrs_LDR_l_Op_A_txt (add : Bool) (imm32 : (BitVec 32)) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
  let base : (BitVec 32) := (Align_bits w__0 4)
  let address : (BitVec 32) :=
    if (add : Bool)
    then (base + imm32)
    else (base - imm32)
  let _ : Unit :=
    if ((t != 15) : Bool)
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb address 1 0)) == 0b00#2) : Bool)
      then
        (do
          (LoadWritePC data))
      else sailThrow ((Error_Unpredictable ())))
  else
    (do
      (R_set t data))


/-- Type quantifiers: k_add : Bool, k_index : Bool, m : Nat, n : Nat, shift_n : Int, t : Nat, k_wback
  : Bool, 0 ≤ t ∧ t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_LDR_r_OpA_A_txt (add : Bool) (index : Bool) (m : Nat) (n : Nat) (shift_n : Int) (shift_t : SRType) (t : Nat) (wback : Bool) : SailM Unit := do
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
    then (AArch32_SetLSInstructionSyndrome 4 false t false)
    else ()
  let data ← (( do (MemU_read address 4) ) : SailM (BitVec 32) )
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))
  if ((t == 15) : Bool)
  then
    (do
      if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb address 1 0)) == 0b00#2) : Bool)
      then
        (do
          (LoadWritePC data))
      else sailThrow ((Error_Unpredictable ())))
  else
    (do
      (R_set t data))


end ArmFull.Functions
