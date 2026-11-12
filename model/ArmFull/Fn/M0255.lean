import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0047
import ArmFull.Fn.M0051
import ArmFull.Fn.M0058
import ArmFull.Fn.M0082
import ArmFull.Fn.M0100
import ArmFull.Fn.M0117
import ArmFull.Fn.M0121
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0189
import ArmFull.Fn.M0194
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0212
import ArmFull.Fn.M0213
import ArmFull.Fn.M0226
import ArmFull.Fn.M0238
import ArmFull.Fn.M0239
import ArmFull.Fn.M0247
import ArmFull.Fn.M0248
import ArmFull.Fn.M0249
import ArmFull.Fn.M0250
import ArmFull.Fn.M0251
import ArmFull.Fn.M0252

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

def AArch32_TakeHypTrapException__1 (except : ExceptionRecord) : SailM Unit := do
  let w__3 ← (( do
    if ((← do
         if (((HaveEL EL2) : Bool) : Bool)
         then
           (do
             let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
             (pure (((BEq.beq w__0 SS_NonSecure) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (ELUsingAArch32 EL2))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__3 "sail-arm/v8_base.sail:41513.87-41513.88"
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x14#8)
  (AArch32_EnterHypMode except preferred_exception_return vect_offset)


def ALUExceptionReturn (address : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.M == M32_User) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.M == M32_System) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let c ← (( do (ConstrainUnpredictable Unpredictable_ALUEXCEPTIONRETURN) ) : SailM
            Constraint )
          ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/v8_base.sail:42343.58-42343.59"
          match c with
          | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
          | .Constraint_NOP =>
            (do
              (EndOfInstruction ()))
          | _ => (pure (())))
      else
        (do
          let w__4 ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
          (AArch32_ExceptionReturn address w__4)))


def AArch32_TakeSMCException (_ : Unit) : SailM Unit := do
  let w__1 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        (ELUsingAArch32 EL3))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__1 "sail-arm/v8_base.sail:42900.44-42900.45"
  (AArch32_ITAdvance ())
  (SSAdvance ())
  let preferred_exception_return ← (( do (NextInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x08#8)
  let lr_offset : Nat := 0
  (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset)


def AArch32_TakeHVCException (immediate : (BitVec 16)) : SailM Unit := do
  let w__1 ← (( do
    if (((HaveEL EL2) : Bool) : Bool)
    then
      (do
        (ELUsingAArch32 EL2))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__1 "sail-arm/v8_base.sail:42912.44-42912.45"
  (AArch32_ITAdvance ())
  (SSAdvance ())
  let preferred_exception_return ← (( do (NextInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x08#8)
  let except ← (( do (ExceptionSyndrome Exception_HypervisorCall) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__2.EL == EL2) : Bool)
  then
    (do
      (AArch32_EnterHypMode except preferred_exception_return vect_offset))
  else
    (do
      (AArch32_EnterHypMode except preferred_exception_return (BitVec.toNat 0x14#8)))


def AArch32_TakeSVCException (immediate : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2776) ()) ) : SailM ExceptionRecord
    )
  (AArch32_ITAdvance ())
  (SSAdvance ())
  let route_to_hyp ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_HCR_Type_TGE w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (NextInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x08#8)
  let lr_offset : Nat := 0
  let w__5 ← (( do
    (pure ((← do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__4.EL == EL2) : Bool)))) || route_to_hyp)) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM ExceptionRecord )
      let except : ExceptionRecord := (w__6 : ExceptionRecord)
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__7.EL == EL2) : Bool)
      then
        (do
          (AArch32_EnterHypMode except preferred_exception_return vect_offset))
      else
        (do
          (AArch32_EnterHypMode except preferred_exception_return (BitVec.toNat 0x14#8))))
  else
    (do
      (AArch32_EnterMode M32_Svc preferred_exception_return lr_offset vect_offset))


def AArch32_TakeMonitorTrapException (_ : Unit) : SailM Unit := do
  let w__1 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        (ELUsingAArch32 EL3))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__1 "sail-arm/v8_base.sail:42977.44-42977.45"
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x04#8)
  let w__2 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  let lr_offset : Int :=
    if ((BEq.beq w__2 InstrSet_A32) : Bool)
    then 4
    else 2
  (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset)


def AArch32_CheckForSVCTrap (immediate : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2780) ()) ) : SailM ExceptionRecord
    )
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 2781) ()) ) : SailM Bool )
  let vect_offset ← (( do (undefined_int_at (← occLabel 2782) ()) ) : SailM Int )
  let w__0 ← (( do (HaveFGTExt ()) ) : SailM Bool )
  let route_to_el2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let route_to_el2 : Bool := false
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        let route_to_el2 ← (( do
          if ((w__1.EL == EL0) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        if ((← do
                             let w__2 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                             (pure (((! w__2) : Bool)))) : Bool)
                        then
                          (do
                            (EL2Enabled ()))
                        else (pure false)) : Bool)
                   then
                     (do
                       let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_HFGITR_EL2_Type_SVC_EL0 w__5) == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  if ((← do
                       let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure (((((_get_HCR_EL2_Type_E2H w__7) +++ (_get_HCR_EL2_Type_TGE w__8)) != 0b11#2) : Bool)))) : Bool)
                  then
                    (do
                      if (((! (HaveEL EL3)) : Bool) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__9 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((((_get_SCR_EL3_Type_FGTEn w__9) == 1#1) : Bool)))))
                  else (pure false))
              else (pure false))
          else (pure (route_to_el2)) ) : SailM Bool )
        if (route_to_el2 : Bool)
        then
          (do
            let w__13 ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM
              ExceptionRecord )
            let except : ExceptionRecord := (w__13 : ExceptionRecord)
            let except : ExceptionRecord :=
              { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
            let except : ExceptionRecord := { except with trappedsyscallinst := true }
            let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
            let vect_offset : Int := (BitVec.toNat 0x0#4)
            (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
        else (pure (()))
        (pure (route_to_el2)))
    else (pure (route_to_el2)) ) : SailM Bool )
  let route_to_el2 := route_to_el2
  (pure (()))


def AArch32_PMUCycle (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
         (pure ((((_get_PMCR_Type_E w__0) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_HDCR_Type_HPME w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (ShouldBRBEFreeze ()) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (BRBEFreeze ()))
      else (pure (())))
  else
    (do
      let w__4 ← (( do (HaveAArch64 ()) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          (AArch64_PMUCycle ()))
      else
        (do
          let w__5 ← (( do (HavePMUv3 ()) ) : SailM Bool )
          if ((! w__5) : Bool)
          then (pure (()))
          else
            (do
              (PMUEvent PMU_EVENT_CPU_CYCLES)
              let counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
              if ((counters != 0) : Bool)
              then
                (do
                  let loop_idx_lower : Nat := 0
                  let loop_idx_upper : Int := (counters -i 1)
                  (do
                    let mut loop_vars := ()
                    for idx in [loop_idx_lower:loop_idx_upper:1]i do
                      let () := loop_vars
                      loop_vars ← do
                        ArmFull.assert ((0 ≤b idx) && (idx ≤b 32)) "sail-arm/v8_base.sail:43597.65-43597.66"
                        let w__6 ← (( do (CountPMUEvents (Sail.Int.toNatChecked (idx))) ) : SailM
                          Bool )
                        if (w__6 : Bool)
                        then
                          (do
                            ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-arm/v8_base.sail:43599.68-43599.69"
                            let w__7 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31)
                              )
                            let accumulated : Int :=
                              (GetElem?.getElem! w__7 (Sail.Int.toNatChecked (idx)))
                            (AArch32_IncrementEventCounter (Sail.Int.toNatChecked (idx)) accumulated))
                        else (pure (()))
                        ArmFull.assert ((0 ≤b idx) && (idx <b 31)) "sail-arm/v8_base.sail:43603.64-43603.65"
                        let w__8 ← (( do readReg PMUEventAccumulator ) : SailM (Vector Int 31) )
                        writeReg PMUEventAccumulator (vectorUpdate w__8
                          (Sail.Int.toNatChecked (idx)) 0)
                    (pure loop_vars)))
              else (pure (()))
              (AArch32_IncrementCycleCounter ())
              (CheckForPMUOverflow ()))))


def execute_aarch32_instrs_ERET_Op_AS_txt (_ : Unit) : SailM Unit := do
  let new_pc_value ← (( do (undefined_bitvector_at (← occLabel 3775) 32) ) : SailM ELR_hyp_Type
    )
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.M == M32_User) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.M == M32_System) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else
        (do
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          let new_pc_value ← (( do
            if ((w__4.EL == EL2) : Bool)
            then
              (do
                (ELR_hyp_read ()))
            else
              (do
                (R_read 14)) ) : SailM ELR_hyp_Type )
          let w__7 ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
          (AArch32_ExceptionReturn new_pc_value w__7)))
  else
    (do
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__8.M == M32_User) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__9.M == M32_System) : Bool)
          then sailThrow ((Error_Unpredictable ()))
          else
            (do
              let _ : Unit := (SynchronizeContext ())
              (DebugRestorePSR ()))))


def BranchTargetCheck (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaveBTIExt ())) : Bool)
    then
      (do
        let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:10588.50-10588.51"
  let w__9 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   readReg InGuardedPage) : Bool)
              then
                (do
                  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__4.BTYPE != 0b00#2) : Bool))))
              else (pure false)) : Bool)
         then
           (do
             let w__6 ← (( do readReg BTypeCompatible ) : SailM Bool )
             (pure (((! w__6) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__8 ← (( do (Halted ()) ) : SailM Bool )
        (pure (((! w__8) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__9 : Bool)
  then
    (do
      let pc ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      (AArch64_BranchTargetException (Sail.BitVec.extractLsb pc 51 0)))
  else (pure (()))
  let branch_instr ← (( do (AArch64_ExecutingBROrBLROrRetInstr ()) ) : SailM Bool )
  let bti_instr ← (( do (AArch64_ExecutingBTIInstr ()) ) : SailM Bool )
  if ((! (branch_instr || bti_instr)) : Bool)
  then
    (do
      writeReg BTypeNext 0b00#2)
  else (pure (()))


def AArch64_CheckForWFxTrap (target_el : (BitVec 2)) (wfxtype : WFxType) : SailM Unit := do
  ArmFull.assert (HaveEL target_el) "sail-arm/v8_base.sail:10675.28-10675.29"
  let is_wfe : Bool := ((BEq.beq wfxtype WFxType_WFE) || (BEq.beq wfxtype WFxType_WFET))
  let trap ← (( do (undefined_bool_at (← occLabel 727) ()) ) : SailM Bool )
  let questionMark := target_el
  let trap ← (( do
    if ((questionMark == EL1) : Bool)
    then
      (do
        let w__2 ← (( do
          if (is_wfe : Bool)
          then
            (do
              let w__0 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
              (pure ((_get_SCTLRType_nTWE w__0))))
          else
            (do
              let w__1 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
              (pure ((_get_SCTLRType_nTWI w__1)))) ) : SailM (BitVec 1) )
        let trap := ((w__2 == 0#1) : Bool)
        (pure (trap)))
    else
      (do
        if ((questionMark == EL2) : Bool)
        then
          (do
            let w__5 ← (( do
              if (is_wfe : Bool)
              then
                (do
                  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_HCR_EL2_Type_TWE w__3))))
              else
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((_get_HCR_EL2_Type_TWI w__4)))) ) : SailM (BitVec 1) )
            let trap := ((w__5 == 1#1) : Bool)
            (pure (trap)))
        else
          (do
            if ((questionMark == EL3) : Bool)
            then
              (do
                let w__8 ← (( do
                  if (is_wfe : Bool)
                  then
                    (do
                      let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((_get_SCR_EL3_Type_TWE w__6))))
                  else
                    (do
                      let w__7 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((_get_SCR_EL3_Type_TWI w__7)))) ) : SailM (BitVec 1) )
                let trap := ((w__8 == 1#1) : Bool)
                (pure (trap)))
            else (pure (trap)))) ) : SailM Bool )
  if (trap : Bool)
  then
    (do
      (AArch64_WFxTrap wfxtype target_el))
  else (pure (()))


def AArch64_Abort (vaddress : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let w__0 ← (( do (IsDebugException fault) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((BEq.beq fault.access.acctype AccessType_IFETCH) : Bool)
      then
        (do
          let w__2 ← (( do
            (pure ((← do
                  (UsingAArch32 ())) && ((fault.debugmoe == DebugException_VectorCatch) : Bool))) )
            : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              (AArch64_VectorCatchException fault))
          else
            (do
              (AArch64_BreakpointException fault)))
      else
        (do
          (AArch64_WatchpointException vaddress fault)))
  else
    (do
      let w__4 ← (( do
        if (((bne fault.gpcf.gpf GPCF_None) : Bool) : Bool)
        then
          (do
            (ReportAsGPCException fault))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          (TakeGPCException vaddress fault))
      else
        (do
          if ((BEq.beq fault.access.acctype AccessType_IFETCH) : Bool)
          then
            (do
              (AArch64_InstructionAbort vaddress fault))
          else
            (do
              (AArch64_DataAbort vaddress fault))))


def AArch32_TakeUndefInstrException (_ : Unit) : SailM Unit := do
  let except ← (( do (ExceptionSyndrome Exception_Uncategorized) ) : SailM ExceptionRecord )
  (AArch32_TakeUndefInstrException__1 except)


/-- Type quantifiers: k_data : Bool, k_is_combined : Bool -/
def Auth (ptr : (BitVec 64)) (modifier : (BitVec 64)) (K : (BitVec 128)) (data : Bool) (key_number : (BitVec 1)) (is_combined : Bool) : SailM (BitVec 64) := do
  let result ← (( do (undefined_bitvector_at (← occLabel 1293) 64) ) : SailM (BitVec 64) )
  let original_ptr ← (( do (undefined_bitvector_at (← occLabel 1294) 64) ) : SailM (BitVec 64) )
  let error_code ← (( do (undefined_bitvector_at (← occLabel 1295) 2) ) : SailM (BitVec 2) )
  let isgeneric : Bool := false
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (EffectiveTBI ptr (! data) w__0.EL) ) : SailM (BitVec 1) )
  let tbi : Bool := (w__1 == 1#1)
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (EffectiveMTX ptr (! data) w__2.EL) ) : SailM (BitVec 1) )
  let mtx : Bool := (w__3 == 1#1)
  let bottom_PAC_bit ← (( do
    (CalculateBottomPACBit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 55)]))) ) : SailM
    Int )
  let extfield : (BitVec 64) :=
    (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 55)])) 64)
  if ((tbi && (bottom_PAC_bit ≥b 55)) : Bool)
  then (pure (ptr))
  else
    (do
      let original_ptr ← (( do
        if (tbi : Bool)
        then
          (do
            ArmFull.assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "sail-arm/v8_base.sail:21616.90-21616.91"
            ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-arm/v8_base.sail:21617.80-21617.81"
            let original_ptr : (BitVec 64) :=
              (Sail.BitVec.castWidth (((Sail.BitVec.extractLsb ptr 63 56) +++ (Sail.BitVec.extractLsb
                    extfield (Sail.Int.toNatChecked (((56 -i bottom_PAC_bit) -i 1))) 0)) +++ (Sail.BitVec.extractLsb
                  ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
            (pure (original_ptr)))
        else
          (do
            if (mtx : Bool)
            then
              (do
                ArmFull.assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "sail-arm/v8_base.sail:21620.90-21620.91"
                ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-arm/v8_base.sail:21621.80-21621.81"
                let original_ptr : (BitVec 64) :=
                  (Sail.BitVec.castWidth ((((Sail.BitVec.extractLsb extfield 63 60) +++ (Sail.BitVec.extractLsb
                          ptr 59 56)) +++ (Sail.BitVec.extractLsb extfield
                        (Sail.Int.toNatChecked (((56 -i bottom_PAC_bit) -i 1))) 0)) +++ (Sail.BitVec.extractLsb
                      ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
                (pure (original_ptr)))
            else
              (do
                ArmFull.assert ((0 ≤b ((64 -i bottom_PAC_bit) -i 1)) && (((64 -i bottom_PAC_bit) -i 1) <b 64)) "sail-arm/v8_base.sail:21624.90-21624.91"
                ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-arm/v8_base.sail:21625.80-21625.81"
                let original_ptr : (BitVec 64) :=
                  (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb extfield
                      (Sail.Int.toNatChecked (((64 -i bottom_PAC_bit) -i 1))) 0) +++ (Sail.BitVec.extractLsb
                      ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
                (pure (original_ptr)))) ) : SailM (BitVec 64) )
      let PAC ← (( do
        (ComputePAC original_ptr modifier (Sail.BitVec.extractLsb K 127 64)
          (Sail.BitVec.extractLsb K 63 0) isgeneric) ) : SailM (BitVec 64) )
      if (tbi : Bool)
      then
        (do
          let w__4 ← (( do (HaveEnhancedPAC2 ()) ) : SailM Bool )
          if ((! w__4) : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b bottom_PAC_bit) && (bottom_PAC_bit ≤b 54)) "sail-arm/v8_base.sail:21631.77-21631.78"
              let result : (BitVec 64) :=
                if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                       PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                       ptr 54 (Sail.Int.toNatChecked (bottom_PAC_bit))))) : Bool)
                then original_ptr
                else
                  (let error_code : (BitVec 2) :=
                    (key_number +++ (Complement.complement key_number))
                  (((Sail.BitVec.extractLsb original_ptr 63 55) +++ error_code) +++ (Sail.BitVec.extractLsb
                      original_ptr 52 0)))
              (pure (result)))
          else
            (do
              let result : (BitVec 64) := ptr
              ArmFull.assert ((0 ≤b bottom_PAC_bit) && (bottom_PAC_bit ≤b 54)) "sail-arm/v8_base.sail:21640.77-21640.78"
              let result : (BitVec 64) :=
                (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange result 54
                  (Sail.Int.toNatChecked (bottom_PAC_bit))
                  (Sail.BitVec.castWidth ((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                      result 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) ^^^ (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                      PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit))))))))
              let w__8 ← (( do
                if ((← do
                     (HaveFPACCombined ())) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          (HaveFPAC ())) && ((! is_combined) : Bool)))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                         result 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) != (Sail.BitVec.castWidth (BitVec.replicateBits
                         (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 55)]))
                         (Sail.Int.toNatChecked ((55 -i bottom_PAC_bit)))))) : Bool)
                  then
                    (do
                      let error_code : (BitVec 2) :=
                        ((if (data : Bool)
                          then 1#1
                          else 0#1) +++ key_number)
                      (AArch64_PACFailException error_code))
                  else (pure (())))
              else (pure (()))
              (pure (result))))
      else
        (do
          if (mtx : Bool)
          then
            (do
              let w__9 ← (( do (HaveEnhancedPAC2 ()) ) : SailM Bool )
              ArmFull.assert w__9 "sail-arm/v8_base.sail:21652.33-21652.34"
              let result : (BitVec 64) := ptr
              ArmFull.assert ((0 ≤b bottom_PAC_bit) && (bottom_PAC_bit ≤b 54)) "sail-arm/v8_base.sail:21654.73-21654.74"
              let result : (BitVec 64) :=
                (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange result 54
                  (Sail.Int.toNatChecked (bottom_PAC_bit))
                  (Sail.BitVec.castWidth ((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                      result 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) ^^^ (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                      PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit))))))))
              let result : (BitVec 64) :=
                (Sail.BitVec.updateSubrange result 63 60
                  ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb result 63 60)) ^^^ (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                      PAC 63 60))))
              let w__13 ← (( do
                if ((← do
                     (HaveFPACCombined ())) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          (HaveFPAC ())) && ((! is_combined) : Bool)))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  if ((((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                           result 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) != (Sail.BitVec.castWidth (BitVec.replicateBits
                           (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 55)]))
                           (Sail.Int.toNatChecked ((55 -i bottom_PAC_bit)))))) || ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           result 63 60)) != (Sail.BitVec.castWidth (m := 4) (BitVec.replicateBits
                           (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 55)])) 4)))) : Bool)
                  then
                    (do
                      let error_code : (BitVec 2) :=
                        ((if (data : Bool)
                          then 1#1
                          else 0#1) +++ key_number)
                      (AArch64_PACFailException error_code))
                  else (pure (())))
              else (pure (()))
              (pure (result)))
          else
            (do
              let w__14 ← (( do (HaveEnhancedPAC2 ()) ) : SailM Bool )
              if ((! w__14) : Bool)
              then
                (do
                  ArmFull.assert ((0 ≤b bottom_PAC_bit) && (bottom_PAC_bit ≤b 54)) "sail-arm/v8_base.sail:21667.77-21667.78"
                  let result : (BitVec 64) :=
                    if ((((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                             PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                             ptr 54 (Sail.Int.toNatChecked (bottom_PAC_bit))))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                             PAC 63 56)) == (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                             ptr 63 56)))) : Bool)
                    then original_ptr
                    else
                      (let error_code : (BitVec 2) :=
                        (key_number +++ (Complement.complement key_number))
                      (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access original_ptr 63)])) +++ error_code) +++ (Sail.BitVec.extractLsb
                          original_ptr 60 0)))
                  (pure (result)))
              else
                (do
                  let result : (BitVec 64) := ptr
                  ArmFull.assert ((0 ≤b bottom_PAC_bit) && (bottom_PAC_bit ≤b 54)) "sail-arm/v8_base.sail:21676.77-21676.78"
                  let result : (BitVec 64) :=
                    (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange result 54
                      (Sail.Int.toNatChecked (bottom_PAC_bit))
                      (Sail.BitVec.castWidth ((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                          result 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) ^^^ (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                          PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit))))))))
                  let result : (BitVec 64) :=
                    (Sail.BitVec.updateSubrange result 63 56
                      ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb result 63 56)) ^^^ (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                          PAC 63 56))))
                  let w__18 ← (( do
                    if ((← do
                         (HaveFPACCombined ())) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              (HaveFPAC ())) && ((! is_combined) : Bool)))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((63 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                             result 63 (Sail.Int.toNatChecked (bottom_PAC_bit)))) != (Sail.BitVec.castWidth (BitVec.replicateBits
                             (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 55)]))
                             (Sail.Int.toNatChecked ((64 -i bottom_PAC_bit)))))) : Bool)
                      then
                        (do
                          let error_code : (BitVec 2) :=
                            ((if (data : Bool)
                              then 1#1
                              else 0#1) +++ key_number)
                          (AArch64_PACFailException error_code))
                      else (pure (())))
                  else (pure (()))
                  (pure (result))))))


end ArmFull.Functions
