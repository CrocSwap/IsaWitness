import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0042
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0052
import ArmFull.Fn.M0087
import ArmFull.Fn.M0115
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0172
import ArmFull.Fn.M0173
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0200
import ArmFull.Fn.M0203
import ArmFull.Fn.M0248
import ArmFull.Fn.M0249
import ArmFull.Fn.M0253
import ArmFull.Fn.M0254
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

def CheckSoftwareStep (_ : Unit) : SailM Unit := do
  let step_enabled ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (DebugTarget ()) ) : SailM (BitVec 2) )
              let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
              (pure (((! w__1) : Bool)))) : Bool)
         then
           (do
             (AArch64_GenerateDebugExceptions ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_MDSCR_EL1_Type_SS w__4) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__6 ← (( do
    if (step_enabled : Bool)
    then
      (do
        let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__5.SS == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      writeReg __InstructionStep true)
  else (pure (()))
  if ((! step_enabled) : Bool)
  then
    (do
      writeReg __InstructionStep false)
  else (pure (()))
  let w__8 ← (( do
    if (step_enabled : Bool)
    then
      (do
        let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__7.SS == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (AArch64_SoftwareStepException ()))
  else (pure (()))


/-- Type quantifiers: ec : Int -/
def AArch32_TakeHypTrapException (ec : Int) : SailM Unit := do
  let w__0 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  let except ← (( do (AArch32_SystemAccessTrapSyndrome w__0 ec) ) : SailM ExceptionRecord )
  (AArch32_TakeHypTrapException__1 except)


def AArch32_CallHypervisor (immediate : (BitVec 16)) : SailM Unit := do
  ArmFull.assert (HaveEL EL2) "sail-arm/v8_base.sail:42929.22-42929.23"
  let w__0 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (AArch64_CallHypervisor immediate))
  else
    (do
      (AArch32_TakeHVCException immediate))


def AArch32_CallSupervisor (immediate_in : (BitVec 16)) : SailM Unit := do
  let immediate : (BitVec 16) := immediate_in
  let w__0 ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
  let immediate ← (( do
    if ((w__0 != 0b1110#4) : Bool)
    then
      (do
        (__UNKNOWN_bits 16))
    else (pure (immediate)) ) : SailM (BitVec 16) )
  let w__2 ← (( do (AArch32_GeneralExceptionsToAArch64 ()) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (AArch64_CallSupervisor immediate))
  else
    (do
      (AArch32_TakeSVCException immediate))


def AArch32_CheckForSMCUndefOrTrap (_ : Unit) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2783) ()) ) : SailM ExceptionRecord
    )
  let route_to_hyp ← (( do (undefined_bool_at (← occLabel 2784) ()) ) : SailM Bool )
  let w__1 ← (( do
    if (((! (HaveEL EL3)) : Bool) : Bool)
    then (pure true)
    else
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__0.EL == EL0) : Bool)))) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__4 ← (( do
    if ((← do
         (EL2Enabled ())) : Bool)
    then
      (do
        let w__3 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (AArch64_CheckForSMCUndefOrTrap (Zeros (n := 16))))
  else
    (do
      let route_to_hyp ← (( do
        if ((← do
             if ((← do
                  (EL2Enabled ())) : Bool)
             then
               (do
                 let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__6.EL == EL1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__8 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_TSC w__8) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (route_to_hyp : Bool)
      then
        (do
          let except ← (( do (ExceptionSyndrome Exception_MonitorCall) ) : SailM ExceptionRecord )
          (AArch32_TakeHypTrapException__1 except))
      else (pure (())))


/-- Type quantifiers: k_implicit_esb : Bool -/
def AArch32_TakePhysicalSErrorException (implicit_esb : Bool) : SailM Unit := do
  let route_to_aarch64 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__5 ← (( do
    if ((← do
         if (((! route_to_aarch64) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__5 : Bool)
    then
      (do
        if ((← do
             let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__7 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__7) : Bool)))) : Bool)
            then
              (do
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_AMO w__8) == 1#1) : Bool))))
            else (pure false)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  let w__12 ← (( do
    if ((((! route_to_aarch64) && (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__11 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__11) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__12 : Bool)
    then
      (do
        let w__13 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
        let route_to_aarch64 := ((w__13 == 1#1) : Bool)
        (pure (route_to_aarch64)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  if (route_to_aarch64 : Bool)
  then
    (do
      (AArch64_TakePhysicalSErrorException implicit_esb))
  else (pure (()))
  let route_to_monitor ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        let w__14 ← (( do readReg SCR ) : SailM (BitVec 32) )
        (pure ((((_get_SCR_Type_EA w__14) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_hyp ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__15.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__16.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__20 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
             (pure ((((_get_HCR_Type_TGE w__20) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__21 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_AMO w__21) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x10#8)
  let lr_offset : Nat := 8
  let target_el ← (( do (undefined_bitvector_at (← occLabel 2792) 2) ) : SailM (BitVec 2) )
  let target_el ← (( do
    if (route_to_monitor : Bool)
    then (pure (EL3))
    else
      (do
        let w__24 ← (( do
          (pure ((← do
                let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__23.EL == EL2) : Bool)))) || route_to_hyp)) ) : SailM Bool )
        let target_el : (BitVec 2) :=
          if (w__24 : Bool)
          then EL2
          else EL1
        (pure (target_el))) ) : SailM (BitVec 2) )
  let fault ← (( do (GetPendingPhysicalSError ()) ) : SailM FaultRecord )
  let vaddress ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  let except ← (( do (AArch32_AbortSyndrome Exception_DataAbort fault vaddress target_el) ) :
    SailM ExceptionRecord )
  let w__25 ← (( do (IsSErrorEdgeTriggered ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__25 : Bool)
    then (ClearPendingPhysicalSError ())
    else ()
  let questionMark := target_el
  if ((questionMark == EL3) : Bool)
  then
    (do
      (AArch32_ReportDataAbort route_to_monitor fault vaddress)
      (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
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
          if ((questionMark == EL1) : Bool)
          then
            (do
              (AArch32_ReportDataAbort route_to_monitor fault vaddress)
              (AArch32_EnterMode M32_Abort preferred_exception_return lr_offset vect_offset))
          else
            (do
              (Unreachable ()))))


def AArch32_TakeVirtualSErrorException (_ : Unit) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43224.63-43224.64"
  let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__8 ← (( do
        if ((← do
             let w__6 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
             (pure ((((_get_HCR_Type_TGE w__6) == 0#1) : Bool)))) : Bool)
        then
          (do
            let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_AMO w__7) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      ArmFull.assert w__8 "sail-arm/v8_base.sail:43226.62-43226.63")
  else
    (do
      let w__11 ← (( do
        if ((← do
             let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__9) == 0#1) : Bool)))) : Bool)
        then
          (do
            let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_AMO w__10) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      ArmFull.assert w__11 "sail-arm/v8_base.sail:43228.56-43228.57")
  let w__14 ← (( do
    if ((← do
         let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__12.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__13 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__13) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__14 : Bool)
  then
    (do
      (AArch64_TakeVirtualSErrorException ()))
  else (pure (()))
  let route_to_monitor : Bool := false
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x10#8)
  let lr_offset : Nat := 8
  let vaddress ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  let parity : Bool := false
  let fault : Fault := Fault_AsyncExternal
  let level ← (( do (__UNKNOWN_integer ()) ) : SailM Int )
  let fsr : (BitVec 32) := (Zeros (n := 32))
  let w__15 ← (( do (HaveRASExt ()) ) : SailM Bool )
  let fsr ← (( do
    if (w__15 : Bool)
    then
      (do
        let w__16 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        if (w__16 : Bool)
        then
          (do
            let w__17 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
            let fsr :=
              ((Sail.BitVec.updateSubrange fsr 15 14 (_get_VDFSR_Type_AET w__17)) : (BitVec 32))
            let w__18 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
            let fsr := ((BitVec.update fsr 12 (Bit (_get_VDFSR_Type_ExT w__18))) : (BitVec 32))
            (pure (fsr)))
        else
          (do
            let w__19 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
            let fsr :=
              ((Sail.BitVec.updateSubrange fsr 15 14 (_get_VSESR_EL2_Type_AET w__19)) : (BitVec 32))
            let w__20 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
            let fsr := ((BitVec.update fsr 12 (Bit (_get_VSESR_EL2_Type_ExT w__20))) : (BitVec 32))
            (pure (fsr))))
    else
      (do
        let w__21 ← (( do (__IMPDEF_bit "Virtual External abort type") ) : SailM (BitVec 1) )
        let fsr := ((BitVec.update fsr 12 (Bit w__21)) : (BitVec 32))
        (pure (fsr))) ) : SailM (BitVec 32) )
  let w__22 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  let fsr ← (( do
    if (((_get_TTBCR_Type_EAE w__22) == 1#1) : Bool)
    then
      (do
        let fsr : (BitVec 32) := (BitVec.update fsr 9 (Bit 1#1))
        let w__23 ← (( do (EncodeLDFSC fault level) ) : SailM (BitVec 6) )
        let fsr := ((Sail.BitVec.updateSubrange fsr 5 0 w__23) : (BitVec 32))
        (pure (fsr)))
    else
      (do
        let fsr : (BitVec 32) := (BitVec.update fsr 9 (Bit 0#1))
        let split_vec ← (( do (EncodeSDFSC fault level) ) : SailM (BitVec 5) )
        let fsr : (BitVec 32) :=
          (Sail.BitVec.updateSubrange fsr 10 10 (Sail.BitVec.extractLsb split_vec 4 4))
        let fsr : (BitVec 32) :=
          (Sail.BitVec.updateSubrange fsr 3 0 (Sail.BitVec.extractLsb split_vec 3 0))
        (pure (fsr))) ) : SailM (BitVec 32) )
  (DFSR_write (Mk_DFSR_Type fsr))
  let w__24 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
  (DFAR_write w__24)
  (ClearPendingVirtualSError ())
  (AArch32_EnterMode M32_Abort preferred_exception_return lr_offset vect_offset)


def AArch32_TakePhysicalIRQException (_ : Unit) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2793) ()) ) : SailM ExceptionRecord
    )
  let route_to_aarch64 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__5 ← (( do
    if ((← do
         if (((! route_to_aarch64) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__5 : Bool)
    then
      (do
        if ((← do
             let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_IMO w__7) == 1#1) : Bool)))) : Bool)
            then
              (do
                let w__8 ← (( do (IsInHost ()) ) : SailM Bool )
                (pure (((! w__8) : Bool))))
            else (pure false)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  let w__12 ← (( do
    if ((((! route_to_aarch64) && (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__11 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__11) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__12 : Bool)
    then
      (do
        let w__13 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        let route_to_aarch64 := (((_get_SCR_EL3_Type_IRQ w__13) == 1#1) : Bool)
        (pure (route_to_aarch64)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  if (route_to_aarch64 : Bool)
  then
    (do
      (AArch64_TakePhysicalIRQException ()))
  else (pure (()))
  let route_to_monitor ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        let w__14 ← (( do readReg SCR ) : SailM (BitVec 32) )
        (pure ((((_get_SCR_Type_IRQ w__14) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_hyp ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__15.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__16.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__20 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
             (pure ((((_get_HCR_Type_TGE w__20) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__21 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_IMO w__21) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x18#8)
  let lr_offset : Nat := 4
  if (route_to_monitor : Bool)
  then
    (do
      (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset))
  else
    (do
      let w__24 ← (( do
        (pure ((← do
              let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__23.EL == EL2) : Bool)))) || route_to_hyp)) ) : SailM Bool )
      if (w__24 : Bool)
      then
        (do
          let except ← (( do (ExceptionSyndrome Exception_IRQ) ) : SailM ExceptionRecord )
          (AArch32_EnterHypMode except preferred_exception_return vect_offset))
      else
        (do
          (AArch32_EnterMode M32_IRQ preferred_exception_return lr_offset vect_offset)))


def AArch32_TakeVirtualIRQException (_ : Unit) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__4 "sail-arm/v8_base.sail:43298.63-43298.64"
  let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__8 ← (( do
        if ((← do
             let w__6 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
             (pure ((((_get_HCR_Type_TGE w__6) == 0#1) : Bool)))) : Bool)
        then
          (do
            let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_IMO w__7) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      ArmFull.assert w__8 "sail-arm/v8_base.sail:43300.62-43300.63")
  else
    (do
      let w__11 ← (( do
        if ((← do
             let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__9) == 0#1) : Bool)))) : Bool)
        then
          (do
            let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_IMO w__10) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      ArmFull.assert w__11 "sail-arm/v8_base.sail:43302.56-43302.57")
  let w__14 ← (( do
    if ((← do
         let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__12.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__13 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__13) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__14 : Bool)
  then
    (do
      (AArch64_TakeVirtualIRQException ()))
  else (pure (()))
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x18#8)
  let lr_offset : Nat := 4
  (AArch32_EnterMode M32_IRQ preferred_exception_return lr_offset vect_offset)


def AArch32_TakePhysicalFIQException (_ : Unit) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2794) ()) ) : SailM ExceptionRecord
    )
  let route_to_aarch64 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__5 ← (( do
    if ((← do
         if (((! route_to_aarch64) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__5 : Bool)
    then
      (do
        if ((← do
             let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_FMO w__7) == 1#1) : Bool)))) : Bool)
            then
              (do
                let w__8 ← (( do (IsInHost ()) ) : SailM Bool )
                (pure (((! w__8) : Bool))))
            else (pure false)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  let w__12 ← (( do
    if ((((! route_to_aarch64) && (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__11 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__11) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__12 : Bool)
    then
      (do
        let w__13 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        let route_to_aarch64 := (((_get_SCR_EL3_Type_FIQ w__13) == 1#1) : Bool)
        (pure (route_to_aarch64)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  if (route_to_aarch64 : Bool)
  then
    (do
      (AArch64_TakePhysicalFIQException ()))
  else (pure (()))
  let route_to_monitor ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        let w__14 ← (( do readReg SCR ) : SailM (BitVec 32) )
        (pure ((((_get_SCR_Type_FIQ w__14) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_hyp ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__15.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__16.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__20 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
             (pure ((((_get_HCR_Type_TGE w__20) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__21 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_FMO w__21) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x1C#8)
  let lr_offset : Nat := 4
  if (route_to_monitor : Bool)
  then
    (do
      (AArch32_EnterMonitorMode preferred_exception_return lr_offset vect_offset))
  else
    (do
      let w__24 ← (( do
        (pure ((← do
              let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__23.EL == EL2) : Bool)))) || route_to_hyp)) ) : SailM Bool )
      if (w__24 : Bool)
      then
        (do
          let except ← (( do (ExceptionSyndrome Exception_FIQ) ) : SailM ExceptionRecord )
          (AArch32_EnterHypMode except preferred_exception_return vect_offset))
      else
        (do
          (AArch32_EnterMode M32_FIQ preferred_exception_return lr_offset vect_offset)))


end ArmFull.Functions
