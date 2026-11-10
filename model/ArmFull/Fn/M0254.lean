import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0044
import ArmFull.Fn.M0052
import ArmFull.Fn.M0121
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0199
import ArmFull.Fn.M0248

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

def AArch64_CheckForSMCUndefOrTrap (imm : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2412) ()) ) : SailM ExceptionRecord
    )
  let vect_offset ← (( do (undefined_int_at (← occLabel 2413) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__8 ← (( do
    if ((← do
         (pure ((← do
               let w__5 ← (( do
                 if ((← do
                      if ((← do
                           let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__1.EL == EL1) : Bool)))) : Bool)
                      then
                        (do
                          (EL2Enabled ()))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure ((((_get_HCR_EL2_Type_TSC w__4) == 1#1) : Bool))))
                 else (pure false) ) : SailM Bool )
               (pure (((! w__5) : Bool)))) && ((HaveEL EL3) : Bool)))) : Bool)
    then
      (do
        let w__7 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((((_get_SCR_EL3_Type_SMD w__7) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__8 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let route_to_el2 : Bool := false
  let route_to_el2 ← (( do
    if ((! (HaveEL EL3)) : Bool)
    then
      (do
        let w__11 ← (( do
          if ((← do
               let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__9.EL == EL1) : Bool)))) : Bool)
          then
            (do
              (EL2Enabled ()))
          else (pure false) ) : SailM Bool )
        if (w__11 : Bool)
        then
          (do
            let w__16 ← (( do
              if ((← do
                   if ((← do
                        (HaveNVExt ())) : Bool)
                   then
                     (do
                       let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_HCR_EL2_Type_NV w__13) == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TSC w__15) == 1#1) : Bool))))
              else (pure false) ) : SailM Bool )
            if (w__16 : Bool)
            then (pure (true))
            else sailThrow ((Error_Undefined ())))
        else sailThrow ((Error_Undefined ())))
    else
      (do
        if ((← do
             if ((← do
                  let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__17.EL == EL1) : Bool)))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TSC w__20) == 1#1) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (route_to_el2 : Bool)
  then
    (do
      let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      let vect_offset : Int := (BitVec.toNat 0x0#4)
      let w__22 ← (( do (ExceptionSyndrome Exception_MonitorCall) ) : SailM ExceptionRecord )
      let except : ExceptionRecord := (w__22 : ExceptionRecord)
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 imm) }
      let except : ExceptionRecord := { except with trappedsyscallinst := true }
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else (pure (()))


def AArch64_MonitorModeTrap (_ : Unit) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_Uncategorized) ) : SailM ExceptionRecord )
  let w__0 ← (( do (IsSecureEL2Enabled ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else (pure (()))
  (AArch64_TakeException EL3 except preferred_exception_return vect_offset)


/-- Type quantifiers: ec : Int -/
def AArch64_SystemAccessTrap (target_el : (BitVec 2)) (ec : Int) : SailM Unit := do
  let w__1 ← (( do
    if ((((HaveEL target_el) && (target_el != EL0)) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__0.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:33913.86-33913.87"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let w__2 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  let except ← (( do (AArch64_SystemAccessTrapSyndrome w__2 ec) ) : SailM ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: ec : Int -/
def AArch64_AArch32SystemAccessTrap (target_el : (BitVec 2)) (ec : Int) : SailM Unit := do
  let w__1 ← (( do
    if ((((HaveEL target_el) && (target_el != EL0)) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__0.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__1 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34008.86-34008.87"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let w__2 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  let except ← (( do (AArch64_AArch32SystemAccessTrapSyndrome w__2 ec) ) : SailM ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: k_implicit_esb : Bool -/
def AArch64_TakePhysicalSErrorException (implicit_esb : Bool) : SailM Unit := do
  let route_to_el3 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((((_get_SCR_EL3_Type_EA w__0) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
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
            if ((← do
                 let w__7 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__7) : Bool)))) : Bool)
            then
              (do
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_AMO w__8) == 1#1) : Bool))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x180#12)
  let target_el ← (( do (undefined_bitvector_at (← occLabel 2419) 2) ) : SailM (BitVec 2) )
  let w__12 ← (( do
    (pure ((← do
          let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__11.EL == EL3) : Bool)))) || route_to_el3)) ) : SailM Bool )
  let target_el ← (( do
    if (w__12 : Bool)
    then (pure (EL3))
    else
      (do
        let w__14 ← (( do
          (pure ((← do
                let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__13.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
        let target_el : (BitVec 2) :=
          if (w__14 : Bool)
          then EL2
          else EL1
        (pure (target_el))) ) : SailM (BitVec 2) )
  let except ← (( do (ExceptionSyndrome Exception_SError) ) : SailM ExceptionRecord )
  let syndrome ← (( do (AArch64_PhysicalSErrorSyndrome implicit_esb) ) : SailM (BitVec 25) )
  let w__15 ← (( do (IsSErrorEdgeTriggered ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__15 : Bool)
    then (ClearPendingPhysicalSError ())
    else ()
  let except : ExceptionRecord := { except with syndrome := syndrome }
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


def AArch64_TakeVirtualSErrorException (_ : Unit) : SailM Unit := do
  let impdef_syndrome ← (( do (undefined_bool_at (← occLabel 2420) ()) ) : SailM Bool )
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
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34186.63-34186.64"
  let w__7 ← (( do
    if ((← do
         let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
         (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_AMO w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__7 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34187.52-34187.53"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x180#12)
  let except ← (( do (ExceptionSyndrome Exception_SError) ) : SailM ExceptionRecord )
  let w__8 ← (( do (HaveRASExt ()) ) : SailM Bool )
  let except ← (( do
    if (w__8 : Bool)
    then
      (do
        let w__9 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
        let except :=
          ({ except with syndrome := (BitVec.update except.syndrome 24
              (Bit (_get_VSESR_EL2_Type_IDS w__9))) } : ExceptionRecord)
        let w__10 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
        let except :=
          ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 23 0
              (_get_VSESR_EL2_Type_ISS w__10)) } : ExceptionRecord)
        (pure (except)))
    else
      (do
        let syndrome ← (( do (__IMPDEF_bits 25 "Virtual SError syndrome") ) : SailM (BitVec 25) )
        let impdef_syndrome : Bool :=
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access syndrome 24)])) == 1#1)
        let except : ExceptionRecord :=
          if (impdef_syndrome : Bool)
          then { except with syndrome := syndrome }
          else except
        (pure (except))) ) : SailM ExceptionRecord )
  (ClearPendingVirtualSError ())
  (AArch64_TakeException EL1 except preferred_exception_return vect_offset)


def AArch64_TakePhysicalIRQException (_ : Unit) : SailM Unit := do
  let route_to_el3 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((((_get_SCR_EL3_Type_IRQ w__0) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
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
            let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_IMO w__7) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x80#8)
  let except ← (( do (ExceptionSyndrome Exception_IRQ) ) : SailM ExceptionRecord )
  if (route_to_el3 : Bool)
  then
    (do
      (AArch64_TakeException EL3 except preferred_exception_return vect_offset))
  else
    (do
      let w__10 ← (( do
        (pure ((← do
              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__9.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
      if (w__10 : Bool)
      then
        (do
          let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
          ArmFull.assert (w__11.EL != EL3) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34217.31-34217.32"
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          let w__14 ← (( do
            if ((← do
                 let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__12.EL == EL0) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__13.EL == EL1) : Bool)))) ) : SailM Bool )
          ArmFull.assert w__14 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34220.50-34220.51"
          (AArch64_TakeException EL1 except preferred_exception_return vect_offset)))


def AArch64_TakeVirtualIRQException (_ : Unit) : SailM Unit := do
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
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34228.63-34228.64"
  let w__7 ← (( do
    if ((← do
         let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
         (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_IMO w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__7 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34229.52-34229.53"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x80#8)
  let except ← (( do (ExceptionSyndrome Exception_IRQ) ) : SailM ExceptionRecord )
  (AArch64_TakeException EL1 except preferred_exception_return vect_offset)


def AArch64_TakePhysicalFIQException (_ : Unit) : SailM Unit := do
  let route_to_el3 ← (( do
    if (((HaveEL EL3) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((((_get_SCR_EL3_Type_FIQ w__0) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
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
            let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_FMO w__7) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x100#12)
  let except ← (( do (ExceptionSyndrome Exception_FIQ) ) : SailM ExceptionRecord )
  if (route_to_el3 : Bool)
  then
    (do
      (AArch64_TakeException EL3 except preferred_exception_return vect_offset))
  else
    (do
      let w__10 ← (( do
        (pure ((← do
              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__9.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
      if (w__10 : Bool)
      then
        (do
          let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
          ArmFull.assert (w__11.EL != EL3) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34247.31-34247.32"
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          let w__14 ← (( do
            if ((← do
                 let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__12.EL == EL0) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__13.EL == EL1) : Bool)))) ) : SailM Bool )
          ArmFull.assert w__14 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34250.50-34250.51"
          (AArch64_TakeException EL1 except preferred_exception_return vect_offset)))


def AArch64_TakeVirtualFIQException (_ : Unit) : SailM Unit := do
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
  ArmFull.assert w__4 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34258.63-34258.64"
  let w__7 ← (( do
    if ((← do
         let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
         (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_FMO w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__7 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34259.52-34259.53"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x100#12)
  let except ← (( do (ExceptionSyndrome Exception_FIQ) ) : SailM ExceptionRecord )
  (AArch64_TakeException EL1 except preferred_exception_return vect_offset)


def AArch64_SoftwareBreakpoint (immediate : (BitVec 16)) : SailM Unit := do
  let route_to_el2 ← (( do
    if ((← do
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
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__5) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_MDCR_EL2_Type_TDE w__6) == 1#1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_SoftwareBreakpoint) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 15 0 immediate) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  if (((BitVec.toNat w__8.EL) >b (BitVec.toNat EL1)) : Bool)
  then
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      (AArch64_TakeException w__9.EL except preferred_exception_return vect_offset))
  else
    (do
      if (route_to_el2 : Bool)
      then
        (do
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          (AArch64_TakeException EL1 except preferred_exception_return vect_offset)))


def AArch64_SoftwareStepException (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  ArmFull.assert (w__0.EL != EL3) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34290.27-34290.28"
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
  let except ← (( do (ExceptionSyndrome Exception_SoftwareStep) ) : SailM ExceptionRecord )
  let w__9 ← (( do (SoftwareStep_DidNotStep ()) ) : SailM Bool )
  let except ← (( do
    if (w__9 : Bool)
    then
      (let except : ExceptionRecord :=
        { except with syndrome := (BitVec.update except.syndrome 24 (Bit 0#1)) }
      (pure (except)))
    else
      (do
        let except : ExceptionRecord :=
          { except with syndrome := (BitVec.update except.syndrome 24 (Bit 1#1)) }
        let w__10 ← (( do (SoftwareStep_SteppedEX ()) ) : SailM Bool )
        let w__11 : (BitVec 1) :=
          if (w__10 : Bool)
          then 1#1
          else 0#1
        let except :=
          ({ except with syndrome := (BitVec.update except.syndrome 6 (Bit w__11)) } : ExceptionRecord)
        (pure (except))) ) : SailM ExceptionRecord )
  let except : ExceptionRecord :=
    { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 5 0 0b100010#6) }
  let w__13 ← (( do
    (pure ((← do
          let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__12.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
  if (w__13 : Bool)
  then
    (do
      (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
  else
    (do
      (AArch64_TakeException EL1 except preferred_exception_return vect_offset))


def AArch64_PCAlignmentFault (_ : Unit) : SailM Unit := do
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let except ← (( do (ExceptionSyndrome Exception_PCAlignment) ) : SailM ExceptionRecord )
  let w__0 ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let except := ({ except with vaddress := w__0 } : ExceptionRecord)
  let target_el : (BitVec 2) := EL1
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let target_el ← (( do
    if (((BitVec.toNat w__1.EL) >b (BitVec.toNat EL1)) : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        let target_el := (w__2.EL : (BitVec 2))
        (pure (target_el)))
    else
      (do
        let w__5 ← (( do
          if ((← do
               (EL2Enabled ())) : Bool)
          then
            (do
              let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCR_EL2_Type_TGE w__4) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let target_el : (BitVec 2) :=
          if (w__5 : Bool)
          then EL2
          else target_el
        (pure (target_el))) ) : SailM (BitVec 2) )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


end ArmFull.Functions
