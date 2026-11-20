module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0197
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0246
public import ArmFull.Fn.M0247 set_option backward.proofsInPublic true @[expose] public section

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

def AArch32_TakeDataAbortException (vaddress : (BitVec 32)) (fault : FaultRecord) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 858) ()) ) : SailM ExceptionRecord )
  let route_to_monitor ← (( do
    if ((← do
         if ((← do
              (HaveEL EL3)) : Bool)
         then
           (do
             let w__1 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
             (pure (((w__1 == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (IsExternalAbort__1 fault))
    else (pure false) ) : SailM Bool )
  let route_to_hyp ← (( do
    if ((← do
         if ((← do
              (EL2Enabled ())) : Bool)
         then
           (do
             if ((← do
                  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__5.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__6.EL == EL1) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  if ((← do
                       let w__9 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                       (pure ((((_get_HCR_Type_TGE w__9) == 1#1) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      if ((← do
                           if ((← do
                                (HaveRASExt ())) : Bool)
                           then
                             (do
                               let w__11 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_HCR2_Type_TEA w__11) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (IsExternalAbort__1 fault))
                      else (pure false))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      (IsDebugException fault)) : Bool)
                 then
                   (do
                     let w__17 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                     (pure ((((_get_HDCR_Type_TDE w__17) == 1#1) : Bool))))
                 else (pure false))) : Bool)
        then (pure true)
        else
          (do
            (IsSecondStage fault)))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x10#8)
  let lr_offset : Nat := 8
  let w__22 ← (( do (IsDebugException fault) ) : SailM Bool )
  if (w__22 : Bool)
  then
    (do
      let w__23 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_MOE w__23 fault.debugmoe)))
  else (pure (()))
  if (route_to_monitor : Bool)
  then
    (do
      (AArch32_ReportDataAbort route_to_monitor fault vaddress)
      (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset))
  else
    (do
      let w__25 ← (( do
        (pure ((← do
              let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__24.EL == EL2) : Bool)))) || route_to_hyp)) ) : SailM Bool )
      if (w__25 : Bool)
      then
        (do
          let except ← (( do (AArch32_AbortSyndrome Exception_DataAbort fault vaddress EL2) ) :
            SailM ExceptionRecord )
          let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__26.EL == EL2) : Bool)
          then
            (do
              (AArch32_EnterHypMode except preferred_exception_return vect_offset))
          else
            (do
              (AArch32_EnterHypMode except preferred_exception_return (BitVec.toNat 0x14#8))))
      else
        (do
          (AArch32_ReportDataAbort route_to_monitor fault vaddress)
          (AArch32_EnterMode M32_Abort preferred_exception_return lr_offset vect_offset)))


def AArch32_TakePrefetchAbortException (vaddress : (BitVec 32)) (fault : FaultRecord) : SailM Unit := do
  let route_to_monitor ← (( do
    if ((← do
         if ((← do
              (HaveEL EL3)) : Bool)
         then
           (do
             let w__1 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
             (pure (((w__1 == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (IsExternalAbort__1 fault))
    else (pure false) ) : SailM Bool )
  let route_to_hyp ← (( do
    if ((← do
         if ((← do
              (EL2Enabled ())) : Bool)
         then
           (do
             if ((← do
                  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__5.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__6.EL == EL1) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  if ((← do
                       let w__9 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                       (pure ((((_get_HCR_Type_TGE w__9) == 1#1) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      if ((← do
                           if ((← do
                                (HaveRASExt ())) : Bool)
                           then
                             (do
                               let w__11 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
                               (pure ((((_get_HCR2_Type_TEA w__11) == 1#1) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          (IsExternalAbort__1 fault))
                      else (pure false))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      (IsDebugException fault)) : Bool)
                 then
                   (do
                     let w__17 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                     (pure ((((_get_HDCR_Type_TDE w__17) == 1#1) : Bool))))
                 else (pure false))) : Bool)
        then (pure true)
        else
          (do
            (IsSecondStage fault)))
    else (pure false) ) : SailM Bool )
  let except ← (( do (undefined_ExceptionRecord (← occLabel 859) ()) ) : SailM ExceptionRecord )
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x0C#8)
  let lr_offset : Nat := 4
  let w__22 ← (( do (IsDebugException fault) ) : SailM Bool )
  if (w__22 : Bool)
  then
    (do
      let w__23 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_MOE w__23 fault.debugmoe)))
  else (pure (()))
  if (route_to_monitor : Bool)
  then
    (do
      (AArch32_ReportPrefetchAbort route_to_monitor fault vaddress)
      (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset))
  else
    (do
      let w__25 ← (( do
        (pure ((← do
              let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__24.EL == EL2) : Bool)))) || route_to_hyp)) ) : SailM Bool )
      if (w__25 : Bool)
      then
        (do
          let except ← (( do
            if ((BEq.beq fault.statuscode Fault_Alignment) : Bool)
            then
              (do
                let w__26 ← (( do (ExceptionSyndrome Exception_PCAlignment) ) : SailM
                  ExceptionRecord )
                let except := (w__26 : ExceptionRecord)
                let w__27 ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
                let except := ({ except with vaddress := w__27 } : ExceptionRecord)
                (pure (except)))
            else
              (do
                (AArch32_AbortSyndrome Exception_InstructionAbort fault vaddress EL2)) ) : SailM
            ExceptionRecord )
          let w__29 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__29.EL == EL2) : Bool)
          then
            (do
              (AArch32_EnterHypMode except preferred_exception_return vect_offset))
          else
            (do
              (AArch32_EnterHypMode except preferred_exception_return (BitVec.toNat 0x14#8))))
      else
        (do
          (AArch32_ReportPrefetchAbort route_to_monitor fault vaddress)
          (AArch32_EnterMode M32_Abort preferred_exception_return lr_offset vect_offset)))


def AArch64_BreakpointException (fault : FaultRecord) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  ArmFull.assert (w__0.EL != EL3) "sail-inputs/03-v8_base.sail:14848.27-14848.28"
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__1.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__2.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_MDCR_EL2_Type_TDE w__7) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let w__10 ← (( do
    (pure ((← do
          let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__9.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
  let target_el : (BitVec 2) :=
    if (w__10 : Bool)
    then EL2
    else EL1
  let vaddress ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let except ← (( do (AArch64_AbortSyndrome Exception_Breakpoint fault vaddress target_el) ) :
    SailM ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def AArch64_DataAbort (vaddress : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 871) ()) ) : SailM Bool )
  let target_el ← (( do (undefined_bitvector_at (← occLabel 872) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do (IsExternalAbort__1 fault) ) : SailM Bool )
  let target_el ← (( do
    if (w__0 : Bool)
    then
      (do
        (AArch64_SyncExternalAbortTarget fault))
    else
      (do
        let route_to_el2 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL0) : Bool)))) : Bool)
                   then (pure true)
                   else
                     (do
                       let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__4.EL == EL1) : Bool)))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        if ((← do
                             let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                             (pure ((((_get_HCR_EL2_Type_TGE w__7) == 1#1) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            if ((← do
                                 (pure ((← do
                                       (HaveRME ())) && ((BEq.beq fault.gpcf.gpf GPCF_Fail) : Bool)))) : Bool)
                            then
                              (do
                                let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure ((((_get_HCR_EL2_Type_GPF w__10) == 1#1) : Bool))))
                            else (pure false))) : Bool)
                   then (pure true)
                   else
                     (do
                       (pure ((← do
                             (HaveNV2Ext ())) && ((BEq.beq fault.access.acctype AccessType_NV2) : Bool))))) : Bool)
              then (pure true)
              else
                (do
                  (IsSecondStage fault)))
          else (pure false) ) : SailM Bool )
        let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
        if ((w__18.EL == EL3) : Bool)
        then (pure (EL3))
        else
          (do
            let w__20 ← (( do
              (pure ((← do
                    let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__19.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
            let target_el : (BitVec 2) :=
              if (w__20 : Bool)
              then EL2
              else EL1
            (pure (target_el)))) ) : SailM (BitVec 2) )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset ← (( do (undefined_int_at (← occLabel 873) ()) ) : SailM Int )
  let w__23 ← (( do
    if ((← do
         (IsExternalAbort__1 fault)) : Bool)
    then
      (do
        (AArch64_RouteToSErrorOffset target_el))
    else (pure false) ) : SailM Bool )
  let vect_offset : Int :=
    if (w__23 : Bool)
    then (BitVec.toNat 0x180#12)
    else (BitVec.toNat 0x0#4)
  let vect_offset : Int := vect_offset
  let except ← (( do (undefined_ExceptionRecord (← occLabel 874) ()) ) : SailM ExceptionRecord )
  let w__25 ← (( do
    (pure ((← do
          (HaveNV2Ext ())) && ((BEq.beq fault.access.acctype AccessType_NV2) : Bool))) ) : SailM
    Bool )
  let except ← (( do
    if (w__25 : Bool)
    then
      (do
        (AArch64_AbortSyndrome Exception_NV2DataAbort fault vaddress target_el))
    else
      (do
        (AArch64_AbortSyndrome Exception_DataAbort fault vaddress target_el)) ) : SailM
    ExceptionRecord )
  (take_exception (some fault))
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def AArch64_InstructionAbort (vaddress : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 875) ()) ) : SailM Bool )
  let w__0 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (bne fault.statuscode Fault_AsyncExternal) "sail-inputs/03-v8_base.sail:15030.54-15030.55")
  else (pure (()))
  let target_el ← (( do (undefined_bitvector_at (← occLabel 876) 2) ) : SailM (BitVec 2) )
  let w__1 ← (( do (IsExternalAbort__1 fault) ) : SailM Bool )
  let target_el ← (( do
    if (w__1 : Bool)
    then
      (do
        (AArch64_SyncExternalAbortTarget fault))
    else
      (do
        let route_to_el2 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   if ((← do
                        let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__4.EL == EL0) : Bool)))) : Bool)
                   then (pure true)
                   else
                     (do
                       let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__5.EL == EL1) : Bool)))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   if ((← do
                        let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__8) == 1#1) : Bool)))) : Bool)
                   then (pure true)
                   else
                     (do
                       if ((← do
                            (pure ((← do
                                  (HaveRME ())) && ((BEq.beq fault.gpcf.gpf GPCF_Fail) : Bool)))) : Bool)
                       then
                         (do
                           let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_HCR_EL2_Type_GPF w__11) == 1#1) : Bool))))
                       else (pure false))) : Bool)
              then (pure true)
              else
                (do
                  (IsSecondStage fault)))
          else (pure false) ) : SailM Bool )
        let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
        if ((w__16.EL == EL3) : Bool)
        then (pure (EL3))
        else
          (do
            let w__18 ← (( do
              (pure ((← do
                    let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__17.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
            let target_el : (BitVec 2) :=
              if (w__18 : Bool)
              then EL2
              else EL1
            (pure (target_el)))) ) : SailM (BitVec 2) )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset ← (( do (undefined_int_at (← occLabel 877) ()) ) : SailM Int )
  let w__21 ← (( do
    if ((← do
         (IsExternalAbort__1 fault)) : Bool)
    then
      (do
        (AArch64_RouteToSErrorOffset target_el))
    else (pure false) ) : SailM Bool )
  let vect_offset : Int :=
    if (w__21 : Bool)
    then (BitVec.toNat 0x180#12)
    else (BitVec.toNat 0x0#4)
  let vect_offset : Int := vect_offset
  let except ← (( do (AArch64_AbortSyndrome Exception_InstructionAbort fault vaddress target_el) )
    : SailM ExceptionRecord )
  (take_exception (some fault))
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def AArch64_VectorCatchException (fault : FaultRecord) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  ArmFull.assert (w__0.EL != EL2) "sail-inputs/03-v8_base.sail:15061.27-15061.28"
  let w__5 ← (( do
    if ((← do
         (EL2Enabled ())) : Bool)
    then
      (do
        if ((← do
             let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__2) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__3 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_MDCR_EL2_Type_TDE w__3) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__5 "sail-inputs/03-v8_base.sail:15062.70-15062.71"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let vaddress ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  let except ← (( do (AArch64_AbortSyndrome Exception_VectorCatch fault vaddress EL2) ) : SailM
    ExceptionRecord )
  (AArch64_TakeException EL2 except preferred_exception_return vect_offset)


def AArch64_WatchpointException (vaddress : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  ArmFull.assert (w__0.EL != EL3) "sail-inputs/03-v8_base.sail:15073.27-15073.28"
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__1.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__2.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_MDCR_EL2_Type_TDE w__7) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let w__10 ← (( do
    (pure ((← do
          let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__9.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
  let target_el : (BitVec 2) :=
    if (w__10 : Bool)
    then EL2
    else EL1
  let except ← (( do (undefined_ExceptionRecord (← occLabel 878) ()) ) : SailM ExceptionRecord )
  let w__12 ← (( do
    (pure ((← do
          (HaveNV2Ext ())) && ((BEq.beq fault.access.acctype AccessType_NV2) : Bool))) ) : SailM
    Bool )
  let except ← (( do
    if (w__12 : Bool)
    then
      (do
        (AArch64_AbortSyndrome Exception_NV2Watchpoint fault vaddress target_el))
    else
      (do
        (AArch64_AbortSyndrome Exception_Watchpoint fault vaddress target_el)) ) : SailM
    ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def TakeGPCException (vaddress : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:15157.20-15157.21"
  let w__1 ← (( do (HaveAtomicExt ()) ) : SailM Bool )
  ArmFull.assert w__1 "sail-inputs/03-v8_base.sail:15158.26-15158.27"
  let w__2 ← (( do (HaveAccessFlagUpdateExt ()) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:15159.36-15159.37"
  let w__3 ← (( do (HaveDirtyBitModifierExt ()) ) : SailM Bool )
  ArmFull.assert w__3 "sail-inputs/03-v8_base.sail:15160.36-15160.37"
  let w__4 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:15161.31-15161.32"
  let except ← (( do (undefined_ExceptionRecord (← occLabel 881) ()) ) : SailM ExceptionRecord )
  let except : ExceptionRecord := { except with exceptype := Exception_GPC }
  let except : ExceptionRecord := { except with vaddress := (Sail.BitVec.zeroExtend vaddress 64) }
  let except : ExceptionRecord := { except with paddress := fault.paddress }
  let except : ExceptionRecord := { except with pavalid := true }
  let w__5 ← (( do (IPAValid fault) ) : SailM Bool )
  let except : ExceptionRecord :=
    if (w__5 : Bool)
    then
      (let except : ExceptionRecord := { except with ipavalid := true }
      let except : ExceptionRecord :=
        { except with NS := if ((BEq.beq fault.ipaddress.paspace PAS_NonSecure) : Bool)
          then 1#1
          else 0#1 }
      { except with ipaddress := fault.ipaddress.address })
    else { except with ipavalid := false }
  let except : ExceptionRecord :=
    if ((BEq.beq fault.access.acctype AccessType_GCS) : Bool)
    then { except with syndrome2 := (BitVec.update except.syndrome2 8 (Bit 1#1)) }
    else except
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 22 (Zeros (n := 3))) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 21
        (Bit
          (if (fault.gpcfs2walk : Bool)
          then 1#1
          else 0#1))) }
  let except : ExceptionRecord :=
    if ((BEq.beq fault.access.acctype AccessType_IFETCH) : Bool)
    then { except with syndrome := (BitVec.update except.syndrome 20 (Bit 1#1)) }
    else { except with syndrome := (BitVec.update except.syndrome 20 (Bit 0#1)) }
  let w__6 ← (( do (EncodeGPCSC fault.gpcf) ) : SailM (BitVec 6) )
  let except :=
    ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 14 w__6) } : ExceptionRecord)
  let w__8 ← (( do
    (pure ((← do
          (HaveNV2Ext ())) && ((BEq.beq fault.access.acctype AccessType_NV2) : Bool))) ) : SailM
    Bool )
  let except : ExceptionRecord :=
    if (w__8 : Bool)
    then { except with syndrome := (BitVec.update except.syndrome 13 (Bit 1#1)) }
    else { except with syndrome := (BitVec.update except.syndrome 13 (Bit 0#1)) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 12 11 0b00#2) }
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 10 9 0b00#2) }
  let except : ExceptionRecord :=
    if (((BEq.beq fault.access.acctype AccessType_DC) || ((BEq.beq fault.access.acctype
             AccessType_IC) || (BEq.beq fault.access.acctype AccessType_AT))) : Bool)
    then { except with syndrome := (BitVec.update except.syndrome 8 (Bit 1#1)) }
    else { except with syndrome := (BitVec.update except.syndrome 8 (Bit 0#1)) }
  let except : ExceptionRecord :=
    { except with syndrome := (BitVec.update except.syndrome 7
        (Bit
          (if (fault.s2fs1walk : Bool)
          then 1#1
          else 0#1))) }
  let except ← (( do
    if (((BEq.beq fault.access.acctype AccessType_DC) || ((BEq.beq fault.access.acctype
             AccessType_IC) || (BEq.beq fault.access.acctype AccessType_AT))) : Bool)
    then
      (let except : ExceptionRecord :=
        { except with syndrome := (BitVec.update except.syndrome 6 (Bit 1#1)) }
      (pure (except)))
    else
      (do
        if (((BEq.beq fault.statuscode Fault_HWUpdateAccessFlag) || (BEq.beq fault.statuscode
               Fault_Exclusive)) : Bool)
        then
          (do
            let w__9 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
            let except :=
              ({ except with syndrome := (BitVec.update except.syndrome 6 (Bit w__9)) } : ExceptionRecord)
            (pure (except)))
        else
          (do
            let w__11 ← (( do
              if ((fault.access.atomicop : Bool) : Bool)
              then
                (do
                  (IsExternalAbort__1 fault))
              else (pure false) ) : SailM Bool )
            if (w__11 : Bool)
            then
              (do
                let w__12 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                let except :=
                  ({ except with syndrome := (BitVec.update except.syndrome 6 (Bit w__12)) } : ExceptionRecord)
                (pure (except)))
            else
              (let except : ExceptionRecord :=
                { except with syndrome := (BitVec.update except.syndrome 6
                    (Bit
                      (if (fault.write : Bool)
                      then 1#1
                      else 0#1))) }
              (pure (except))))) ) : SailM ExceptionRecord )
  let w__13 ← (( do (EncodeLDFSC fault.statuscode fault.level) ) : SailM (BitVec 6) )
  let except :=
    ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 5 0 w__13) } : ExceptionRecord)
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let target_el : (BitVec 2) := EL3
  let vect_offset ← (( do (undefined_int_at (← occLabel 882) ()) ) : SailM Int )
  let w__16 ← (( do
    if ((← do
         (IsExternalAbort__1 fault)) : Bool)
    then
      (do
        (AArch64_RouteToSErrorOffset target_el))
    else (pure false) ) : SailM Bool )
  let vect_offset : Int :=
    if (w__16 : Bool)
    then (BitVec.toNat 0x180#12)
    else (BitVec.toNat 0x0#4)
  let vect_offset : Int := vect_offset
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


end ArmFull.Functions
