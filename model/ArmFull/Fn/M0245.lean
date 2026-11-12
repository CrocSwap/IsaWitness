import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0100
import ArmFull.Fn.M0113
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0180
import ArmFull.Fn.M0183
import ArmFull.Fn.M0185
import ArmFull.Fn.M0186
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0227
import ArmFull.Fn.M0238
import ArmFull.Fn.M0243
import ArmFull.Fn.M0244

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

/-- Type quantifiers: m : Nat, 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_BX_Op_A_txt (m : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  (BXWritePC w__0 BranchType_INDIR)


/-- Type quantifiers: m : Nat, 0 ≤ m ∧ m ≤ 15 -/
def execute_aarch32_instrs_BXJ_Op_A_txt (m : Nat) : SailM Unit := do
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  (BXWritePC w__0 BranchType_INDIR)


/-- Type quantifiers: n : Nat, k_nonzero : Bool, List.elem n [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_CBNZ_Op_A_txt (imm32 : (BitVec 32)) (n : Nat) (nonzero : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  if ((neq_bool nonzero (IsZero w__0)) : Bool)
  then
    (do
      let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
      (CBWritePC (w__1 + imm32)))
  else (pure (()))


def decode_b_cond_aarch64_instrs_branch_conditional_cond (cond : (BitVec 4)) (imm19 : (BitVec 19)) : SailM Unit := do
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let condition : (BitVec 4) := cond
  (execute_aarch64_instrs_branch_conditional_cond condition offset)


def decode_bc_cond_aarch64_instrs_branch_conditional_hinted (cond : (BitVec 4)) (imm19 : (BitVec 19)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatHBC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let condition : (BitVec 4) := cond
  (execute_aarch64_instrs_branch_conditional_hinted condition offset)


def decode_cbnz_aarch64_instrs_branch_conditional_compare (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let iszero : Bool := (op == 0#1)
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_conditional_compare (Sail.Int.toNatChecked (datasize)) iszero
    offset (Sail.Int.toNatChecked (t)))


def decode_cbz_aarch64_instrs_branch_conditional_compare (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let iszero : Bool := (op == 0#1)
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_conditional_compare (Sail.Int.toNatChecked (datasize)) iszero
    offset (Sail.Int.toNatChecked (t)))


def decode_drps_aarch64_instrs_branch_unconditional_dret (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Halted ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL0) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_branch_unconditional_dret ())


def decode_isb_aarch64_instrs_system_barriers_isb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  (execute_aarch64_instrs_system_barriers_isb ())


def decode_tbnz_aarch64_instrs_branch_conditional_test (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let datasize : Int :=
    if ((b5 == 1#1) : Bool)
    then 64
    else 32
  let bit_pos : Int := (BitVec.toNat (b5 +++ b40))
  let bit_val : (BitVec 1) := op
  let offset : (BitVec 64) := (sign_extend (imm14 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_conditional_test (Sail.Int.toNatChecked (bit_pos)) bit_val
    (Sail.Int.toNatChecked (datasize)) offset (Sail.Int.toNatChecked (t)))


def decode_tbz_aarch64_instrs_branch_conditional_test (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let datasize : Int :=
    if ((b5 == 1#1) : Bool)
    then 64
    else 32
  let bit_pos : Int := (BitVec.toNat (b5 +++ b40))
  let bit_val : (BitVec 1) := op
  let offset : (BitVec 64) := (sign_extend (imm14 +++ 0b00#2) 64)
  (execute_aarch64_instrs_branch_conditional_test (Sail.Int.toNatChecked (bit_pos)) bit_val
    (Sail.Int.toNatChecked (datasize)) offset (Sail.Int.toNatChecked (t)))


/-- Type quantifiers: k_retry : Bool -/
def execute_aarch64_instrs_system_tme_tcancel (reason : (BitVec 15)) (retry : Bool) : SailM Unit := do
  let w__0 ← (( do (IsTMEEnabled ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do readReg TSTATE ) : SailM TMState )
  if ((w__1.depth >b 0) : Bool)
  then
    (do
      (FailTransaction__1 TMFailure_CNCL retry false reason))
  else (pure (()))


def decode_xpac_aarch64_instrs_integer_pac_strip_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let data : Bool := (D == 1#1)
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((n != 31) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_integer_pac_strip_dp_1src (Sail.Int.toNatChecked (d)) data)


def decode_xpac_aarch64_instrs_integer_pac_strip_hint (_ : Unit) : SailM Unit := do
  let d : Nat := 30
  let data : Bool := false
  (execute_aarch64_instrs_integer_pac_strip_dp_1src d data)


/-- Type quantifiers: k_is_async : Bool -/
def Halt__1 (reason : (BitVec 6)) (is_async : Bool) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (FailTransaction TMFailure_DBG false))
  else (pure (()))
  let _ : Unit := (CTI_SignalEvent CrossTriggerIn_CrossHalt)
  let preferred_restart_address ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let spsr ← (( do (GetPSRFromPSTATE DebugState 64) ) : SailM (BitVec 64) )
  let w__7 ← (( do
    if ((← do
         (pure ((← do
               (pure ((← do
                     (HaveBTIExt ())) && ((! is_async) : Bool)))) && ((! ((reason == DebugHalt_Step_Normal) || ((reason == DebugHalt_Step_Exclusive) || ((reason == DebugHalt_Step_NoSyndrome) || ((reason == DebugHalt_Breakpoint) || (reason == DebugHalt_HaltInstruction)))))) : Bool)))) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_ZEROBTYPE))
    else (pure false) ) : SailM Bool )
  let spsr : (BitVec 64) :=
    if (w__7 : Bool)
    then (Sail.BitVec.updateSubrange spsr 11 10 0b00#2)
    else spsr
  let w__8 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (DLR_write (Sail.BitVec.extractLsb preferred_restart_address 31 0))
      (DSPSR_write (Mk_DSPSR_Type (Sail.BitVec.extractLsb spsr 31 0)))
      let w__9 ← (( do (Havev8p9Debug ()) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (DSPSR2_write (Mk_DSPSR2_Type (Sail.BitVec.extractLsb spsr 63 32))))
      else (pure (())))
  else
    (do
      writeReg DLR_EL0 preferred_restart_address
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type spsr))
  let w__10 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ITE w__10 1#1))
  let w__11 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ITO w__11 0#1))
  let w__12 ← (( do (HaveRME ()) ) : SailM Bool )
  if (w__12 : Bool)
  then
    (do
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__13.EL == EL3) : Bool)
      then
        (do
          let w__14 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          (EDSCR_write (_update_EDSCR_Type_SDD w__14 0#1)))
      else
        (do
          let w__15 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          let w__16 ← (( do (ExternalRootInvasiveDebugEnabled ()) ) : SailM Bool )
          let w__17 : (BitVec 1) :=
            if (w__16 : Bool)
            then 0#1
            else 1#1
          (EDSCR_write (_update_EDSCR_Type_SDD w__15 w__17))))
  else
    (do
      let w__18 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      if ((BEq.beq w__18 SS_Secure) : Bool)
      then
        (do
          let w__19 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
          (EDSCR_write (_update_EDSCR_Type_SDD w__19 0#1)))
      else
        (do
          if ((HaveEL EL3) : Bool)
          then
            (do
              let w__20 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
              let w__21 ← (( do (ExternalSecureInvasiveDebugEnabled ()) ) : SailM Bool )
              let w__22 : (BitVec 1) :=
                if (w__21 : Bool)
                then 0#1
                else 1#1
              (EDSCR_write (_update_EDSCR_Type_SDD w__20 w__22)))
          else
            (do
              let w__23 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
              (EDSCR_write (_update_EDSCR_Type_SDD w__23 1#1)))))
  let w__24 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_MA w__24 0#1))
  let w__25 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__25 : Bool)
  then
    (do
      let split_vec ← (( do (__UNKNOWN_bits 14) ) : SailM (BitVec 14) )
      let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__26 with IT := (Sail.BitVec.extractLsb split_vec 13 6) }
      let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__27 with SS := (Sail.BitVec.extractLsb split_vec 5 5) }
      let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__28 with SSBS := (Sail.BitVec.extractLsb split_vec 4 4) }
      let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__29 with A := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__30 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__30 with I := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__31 with F := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__32 with T := (Sail.BitVec.extractLsb split_vec 0 0) })
  else
    (do
      let split_vec ← (( do (__UNKNOWN_bits 6) ) : SailM (BitVec 6) )
      let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__33 with SS := (Sail.BitVec.extractLsb split_vec 5 5) }
      let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__34 with SSBS := (Sail.BitVec.extractLsb split_vec 4 4) }
      let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__35 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__36 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__37 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__37 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__38 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__38 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
      let w__39 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__39 with TCO := 1#1 }
      let w__40 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__40 with BTYPE := 0b00#2 })
  let w__41 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__41 with IL := 0#1 }
  let _ : Unit := (StopInstructionPrefetchAndEnableITR ())
  let w__42 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_STATUS w__42 reason))
  (UpdateEDSCRFields ())
  if ((! is_async) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))


def AArch64_TakeExceptionInDebugState (target_el : (BitVec 2)) (exception_in : ExceptionRecord) : SailM Unit := do
  let w__3 ← (( do
    if ((← do
         if (((HaveEL target_el) : Bool) : Bool)
         then
           (do
             let w__0 ← (( do (ELUsingAArch32 target_el) ) : SailM Bool )
             (pure (((! w__0) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__2.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__3 "sail-arm/v8_base.sail:9865.105-9865.106"
  let w__5 ← (( do
    if (((target_el != EL3) : Bool) : Bool)
    then (pure true)
    else
      (do
        let w__4 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_EDSCR_Type_SDD w__4) == 0#1) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__5 "sail-arm/v8_base.sail:9866.54-9866.55"
  let except : ExceptionRecord := exception_in
  let sync_errors ← (( do (undefined_bool_at (← occLabel 693) ()) ) : SailM Bool )
  let w__6 ← (( do (HaveIESB ()) ) : SailM Bool )
  let sync_errors ← (( do
    if (w__6 : Bool)
    then
      (do
        let w__7 ← (( do (SCTLR_read target_el) ) : SailM (BitVec 64) )
        let sync_errors := (((_get_SCTLRType_IESB w__7) == 1#1) : Bool)
        let w__8 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
        let sync_errors ← (( do
          if (w__8 : Bool)
          then
            (do
              if ((sync_errors : Bool) : Bool)
              then (pure true)
              else
                (do
                  (pure ((← do
                        let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure (((((_get_SCR_EL3_Type_EA w__9) +++ (_get_SCR_EL3_Type_NMEA w__10)) == 0b11#2) : Bool)))) && ((target_el == EL3) : Bool)))))
          else (pure (sync_errors)) ) : SailM Bool )
        let w__13 ← (( do (ConstrainUnpredictableBool Unpredictable_IESBinDebug) ) : SailM Bool )
        let sync_errors : Bool :=
          if ((! w__13) : Bool)
          then false
          else sync_errors
        (pure (sync_errors)))
    else (pure (false)) ) : SailM Bool )
  let w__16 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__15 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__15.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__16 : Bool)
  then
    (do
      let cause ← (( do (undefined_TMFailure (← occLabel 694) ()) ) : SailM TMFailure )
      let cause : TMFailure :=
        match except.exceptype with
        | .Exception_SoftwareBreakpoint => TMFailure_DBG
        | .Exception_Breakpoint => TMFailure_DBG
        | .Exception_Watchpoint => TMFailure_DBG
        | .Exception_SoftwareStep => TMFailure_DBG
        | _ => TMFailure_ERR
      let cause := cause
      (FailTransaction cause false))
  else (pure (()))
  let _ : Unit := (SynchronizeContext ())
  let from_32 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (from_32 : Bool)
  then
    (do
      (AArch64_MaybeZeroRegisterUppers ()))
  else (pure (()))
  let w__20 ← (( do
    if ((← if (from_32 : Bool)
         then
           (do
             (HaveSME ()))
         else (pure false)) : Bool)
    then
      (do
        let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__19.SM == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__20 : Bool)
  then
    (do
      (ResetSVEState ()))
  else
    (do
      (MaybeZeroSVEUppers target_el))
  (AArch64_ReportException except target_el)
  let w__21 ← (( do (HaveGCS ()) ) : SailM Bool )
  if (w__21 : Bool)
  then
    (do
      let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__22 with EXLOCK := 0#1 })
  else (pure (()))
  let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__23 with EL := target_el }
  let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__24 with nRW := 0#1 }
  let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__25 with SP := 1#1 }
  let w__26 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  (SPSR_set (N := 64) w__26)
  let w__27 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  (ELR_set__1 w__27)
  let split_vec ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
  let w__28 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__28 with SS := (Sail.BitVec.extractLsb split_vec 4 4) }
  let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__29 with D := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__30 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__30 with A := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__31 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__32 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__32 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
  let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__33 with IL := 0#1 }
  if (from_32 : Bool)
  then
    (do
      let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__34 with IT := 0b00000000#8 }
      let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__35 with T := 0#1 })
  else (pure (()))
  let w__44 ← (( do
    if ((← do
         if ((← do
              (HavePANExt ())) : Bool)
         then
           (do
             if ((← do
                  let w__37 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__37.EL == EL1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      let w__38 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__38.EL == EL2) : Bool)))) : Bool)
                 then
                   (do
                     (ELIsInHost EL0))
                 else (pure false)))
         else (pure false)) : Bool)
    then
      (do
        let w__43 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        (pure ((((_get_SCTLRType_SPAN w__43) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__44 : Bool)
  then
    (do
      let w__45 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__45 with PAN := 1#1 })
  else (pure (()))
  let w__46 ← (( do (HaveUAOExt ()) ) : SailM Bool )
  if (w__46 : Bool)
  then
    (do
      let w__47 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__47 with UAO := 0#1 })
  else (pure (()))
  let w__48 ← (( do (HaveBTIExt ()) ) : SailM Bool )
  if (w__48 : Bool)
  then
    (do
      let w__49 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__49 with BTYPE := 0b00#2 })
  else (pure (()))
  let w__50 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
  if (w__50 : Bool)
  then
    (do
      let w__51 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__52 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
      writeReg PSTATE { w__51 with SSBS := w__52 })
  else (pure (()))
  let w__53 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if (w__53 : Bool)
  then
    (do
      let w__54 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__54 with TCO := 1#1 })
  else (pure (()))
  let w__55 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg DLR_EL0 w__55
  let w__56 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__56)
  let w__57 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (_update_EDSCR_Type_ERR w__57 1#1))
  (UpdateEDSCRFields ())
  let _ : Unit :=
    if (sync_errors : Bool)
    then (SynchronizeErrors ())
    else ()
  (EndOfInstruction ())


def GPTWalk (pa : (BitVec 56)) (accdesc : AccessDescriptor) : SailM (GPCFRecord × GPTEntry) := SailME.run do
  let gpi_index ← (( do (undefined_int_at (← occLabel 1233) ()) ) : SailME
    (GPCFRecord × GPTEntry) Int )
  let gpttlbline ← (( do (undefined_GPTTLBLine (← occLabel 1234) ()) ) : SailME
    (GPCFRecord × GPTEntry) GPTTLBLine )
  let w__0 ← (( do readReg GPCCR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let pgs ← (( do (DecodePGS (_get_GPCCR_EL3_Type_PGS w__0)) ) : SailME (GPCFRecord × GPTEntry)
    PGSe )
  let w__1 ← (( do readReg __tlb_enabled ) : SailME (GPCFRecord × GPTEntry) Bool )
  if (w__1 : Bool)
  then
    (do
      let gpttlbline ← (( do (GPTTLBLookup pa pgs) ) : SailME (GPCFRecord × GPTEntry) GPTTLBLine
        )
      if (gpttlbline.valid_name : Bool)
      then
        (do
          let w__2 ← (( do (GPCNoFault ()) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
          SailME.throw ((w__2, gpttlbline.gpt_entry) : (GPCFRecord × GPTEntry)))
      else (pure (())))
  else (pure (()))
  let w__3 ← (( do readReg GPTBR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let base : (BitVec 56) :=
    (Sail.BitVec.zeroExtend ((_get_GPTBR_EL3_Type_BADDR w__3) +++ (Zeros (n := 12))) 56)
  let pps ← (( do (DecodePPS ()) ) : SailME (GPCFRecord × GPTEntry) Int )
  let l0sz ← (( do (GPTL0Size ()) ) : SailME (GPCFRecord × GPTEntry) Int )
  let alignment : Int := (Max.max ((pps -i l0sz) +i 3) 12)
  ArmFull.assert (56 ≥b alignment) "sail-arm/v8_base.sail:19809.39-19809.40"
  let base : (BitVec 56) :=
    (base &&& (Sail.BitVec.castWidth (m := 56) (Complement.complement
        (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked (alignment)))) 56))))
  let gptaccdesc ← (( do (CreateAccDescGPTW accdesc) ) : SailME (GPCFRecord × GPTEntry)
    AccessDescriptor )
  let gptaddrdesc ← (( do (undefined_AddressDescriptor (← occLabel 1235) ()) ) : SailME
    (GPCFRecord × GPTEntry) AddressDescriptor )
  let w__4 ← (( do readReg GPCCR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let w__5 ← (( do readReg GPCCR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let w__6 ← (( do readReg GPCCR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let w__7 ← (( do
    (WalkMemAttrs (_get_GPCCR_EL3_Type_SH w__4) (_get_GPCCR_EL3_Type_ORGN w__5)
      (_get_GPCCR_EL3_Type_IRGN w__6)) ) : SailME (GPCFRecord × GPTEntry) MemoryAttributes )
  let gptaddrdesc := ({ gptaddrdesc with memattrs := w__7 } : AddressDescriptor)
  let w__8 ← (( do (NoFault__1 gptaccdesc) ) : SailME (GPCFRecord × GPTEntry) FaultRecord )
  let gptaddrdesc := ({ gptaddrdesc with fault := w__8 } : AddressDescriptor)
  let gptaddrdesc : AddressDescriptor :=
    { gptaddrdesc with paddress := { gptaddrdesc.paddress with paspace := PAS_Root } }
  let w__9 ← (( do (GPTLevel0Index pa) ) : SailME (GPCFRecord × GPTEntry) Int )
  let gptaddrdesc :=
    ({ gptaddrdesc with paddress := { gptaddrdesc.paddress with address := (BitVec.addInt base
          (w__9 *i 8)) } } : AddressDescriptor)
  let level_0_entry ← (( do (undefined_bitvector_at (← occLabel 1236) 64) ) : SailME
    (GPCFRecord × GPTEntry) (BitVec 64) )
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1237) ()) ) : SailME
    (GPCFRecord × GPTEntry) PhysMemRetStatus )
  let w__10 ← (( do (PhysMemRead gptaddrdesc 8 gptaccdesc none) ) : SailME
    (GPCFRecord × GPTEntry) (PhysMemRetStatus × (BitVec (8 * 8))) )
  let (tup__0, tup__1) := (w__10 : (PhysMemRetStatus × (BitVec (8 * 8))))
  let memstatus : PhysMemRetStatus := tup__0
  let level_0_entry : (BitVec 64) := tup__1
  if ((IsFault__2 memstatus) : Bool)
  then
    (do
      let w__11 ← (( do (GPCFault GPCF_EABT 0) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
      let w__12 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCFRecord × GPTEntry) GPTEntry )
      (pure ((w__11, w__12))))
  else
    (do
      let result ← (( do (undefined_GPTEntry (← occLabel 1238) ()) ) : SailME
        (GPCFRecord × GPTEntry) GPTEntry )
      let table ← (( do (undefined_GPTTable (← occLabel 1239) ()) ) : SailME
        (GPCFRecord × GPTEntry) GPTTable )
      let gpf ← (( do (undefined_GPCF (← occLabel 1240) ()) ) : SailME (GPCFRecord × GPTEntry)
        GPCF )
      let questionMark := (Sail.BitVec.extractLsb level_0_entry 3 0)
      let (gpf, result, table) ← (( do
        if ((questionMark == GPT_Block) : Bool)
        then
          (do
            let w__13 ← (( do (DecodeGPTBlock pgs level_0_entry) ) : SailME
              (GPCFRecord × GPTEntry) (GPCF × GPTEntry) )
            let (tup__0, tup__1) := (w__13 : (GPCF × GPTEntry))
            let gpf : GPCF := tup__0
            let result : GPTEntry := tup__1
            let result : GPTEntry := { result with pa := pa }
            let w__15 ← (( do
              (pure ((← do
                    readReg __tlb_enabled) && ((BEq.beq gpf GPCF_None) : Bool))) ) : SailME
              (GPCFRecord × GPTEntry) Bool )
            let _ : Unit :=
              if (w__15 : Bool)
              then (GPTTLBCache pgs result)
              else ()
            let w__16 ← (( do (GPCFault gpf 0) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
            SailME.throw ((w__16, result) : (GPCFRecord × GPTEntry))
            (pure ((gpf, result, table))))
        else
          (do
            let (gpf, table) ← (( do
              if ((questionMark == GPT_Table) : Bool)
              then
                (do
                  let w__17 ← (( do (DecodeGPTTable pgs level_0_entry) ) : SailME
                    (GPCFRecord × GPTEntry) (GPCF × GPTTable) )
                  let (tup__0, tup__1) := (w__17 : (GPCF × GPTTable))
                  let gpf : GPCF := tup__0
                  let table : GPTTable := tup__1
                  if ((bne gpf GPCF_None) : Bool)
                  then
                    (do
                      let w__18 ← (( do (GPCFault gpf 0) ) : SailME (GPCFRecord × GPTEntry)
                        GPCFRecord )
                      let w__19 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME
                        (GPCFRecord × GPTEntry) GPTEntry )
                      SailME.throw ((w__18, w__19) : (GPCFRecord × GPTEntry)))
                  else (pure (()))
                  (pure ((gpf, table))))
              else
                (do
                  let w__20 ← (( do (GPCFault GPCF_Walk 0) ) : SailME (GPCFRecord × GPTEntry)
                    GPCFRecord )
                  let w__21 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCFRecord × GPTEntry)
                    GPTEntry )
                  SailME.throw ((w__20, w__21) : (GPCFRecord × GPTEntry))
                  (pure ((gpf, table)))) ) : SailME (GPCFRecord × GPTEntry) (GPCF × GPTTable) )
            (pure ((gpf, result, table)))) ) : SailME (GPCFRecord × GPTEntry)
        (GPCF × GPTEntry × GPTTable) )
      ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb level_0_entry 3 0)) == GPT_Table) "sail-arm/v8_base.sail:19846.45-19846.46"
      let w__22 ← (( do (GPTLevel1Index pa) ) : SailME (GPCFRecord × GPTEntry) Int )
      let offset : Int := (w__22 *i 8)
      let gptaddrdesc : AddressDescriptor :=
        { gptaddrdesc with paddress := { gptaddrdesc.paddress with address := (BitVec.addInt
              table.address offset) } }
      let level_1_entry ← (( do (undefined_bitvector_at (← occLabel 1241) 64) ) : SailME
        (GPCFRecord × GPTEntry) (BitVec 64) )
      let w__23 ← (( do (PhysMemRead gptaddrdesc 8 gptaccdesc none) ) : SailME
        (GPCFRecord × GPTEntry) (PhysMemRetStatus × (BitVec (8 * 8))) )
      let (tup__0, tup__1) := (w__23 : (PhysMemRetStatus × (BitVec (8 * 8))))
      let memstatus : PhysMemRetStatus := tup__0
      let level_1_entry : (BitVec 64) := tup__1
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          let w__24 ← (( do (GPCFault GPCF_EABT 1) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord
            )
          let w__25 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCFRecord × GPTEntry) GPTEntry )
          (pure ((w__24, w__25))))
      else
        (do
          let questionMark := (Sail.BitVec.extractLsb level_1_entry 3 0)
          let (gpf, result) ← (( do
            if ((questionMark == GPT_Contig) : Bool)
            then
              (do
                let w__26 ← (( do (DecodeGPTContiguous pgs level_1_entry) ) : SailME
                  (GPCFRecord × GPTEntry) (GPCF × GPTEntry) )
                let (tup__0, tup__1) := (w__26 : (GPCF × GPTEntry))
                let gpf : GPCF := tup__0
                let result : GPTEntry := tup__1
                (pure ((gpf, result))))
            else
              (do
                let gpi_index ← (( do (GPIIndex pa) ) : SailME (GPCFRecord × GPTEntry) Int )
                let w__27 ← (( do (DecodeGPTGranules pgs gpi_index level_1_entry) ) : SailME
                  (GPCFRecord × GPTEntry) (GPCF × GPTEntry) )
                let (tup__0, tup__1) := (w__27 : (GPCF × GPTEntry))
                let gpf : GPCF := tup__0
                let result : GPTEntry := tup__1
                (pure ((gpf, result)))) ) : SailME (GPCFRecord × GPTEntry) (GPCF × GPTEntry) )
          if ((bne gpf GPCF_None) : Bool)
          then
            (do
              let w__28 ← (( do (GPCFault gpf 1) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
              let w__29 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCFRecord × GPTEntry)
                GPTEntry )
              (pure ((w__28, w__29))))
          else
            (do
              let result : GPTEntry := { result with pa := pa }
              let w__30 ← (( do readReg __tlb_enabled ) : SailME (GPCFRecord × GPTEntry) Bool )
              let _ : Unit :=
                if (w__30 : Bool)
                then (GPTTLBCache pgs result)
                else ()
              let w__31 ← (( do (GPCNoFault ()) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
              (pure ((w__31, result))))))


end ArmFull.Functions
