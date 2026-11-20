module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0174
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0198
public import ArmFull.Fn.M0246 set_option backward.proofsInPublic true @[expose] public section

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

def AArch64_CheckForSVCTrap (immediate : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2409) ()) ) : SailM ExceptionRecord
    )
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 2410) ()) ) : SailM Bool )
  let vect_offset ← (( do (undefined_int_at (← occLabel 2411) ()) ) : SailM Int )
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
                             if ((← do
                                  let w__2 ← (( do (UsingAArch32 ()) ) : SailM Bool )
                                  (pure (((! w__2) : Bool)))) : Bool)
                             then
                               (do
                                 let w__3 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                 (pure (((! w__3) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (EL2Enabled ()))
                        else (pure false)) : Bool)
                   then
                     (do
                       let w__7 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_HFGITR_EL2_Type_SVC_EL0 w__7) == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  if ((← do
                       let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) != 0b11#2) : Bool)))) : Bool)
                  then
                    (do
                      if ((← do
                           let w__11 ← (( do (HaveEL EL3) ) : SailM Bool )
                           (pure (((! w__11) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__12 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((((_get_SCR_EL3_Type_FGTEn w__12) == 1#1) : Bool)))))
                  else (pure false))
              else (pure false))
          else
            (do
              let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__16.EL == EL1) : Bool)
              then
                (do
                  if ((← do
                       if ((← do
                            (EL2Enabled ())) : Bool)
                       then
                         (do
                           let w__18 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_HFGITR_EL2_Type_SVC_EL1 w__18) == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      if ((← do
                           let w__20 ← (( do (HaveEL EL3) ) : SailM Bool )
                           (pure (((! w__20) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__21 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((((_get_SCR_EL3_Type_FGTEn w__21) == 1#1) : Bool)))))
                  else (pure false))
              else (pure (route_to_el2))) ) : SailM Bool )
        if (route_to_el2 : Bool)
        then
          (do
            let w__24 ← (( do (ExceptionSyndrome Exception_SupervisorCall) ) : SailM
              ExceptionRecord )
            let except : ExceptionRecord := (w__24 : ExceptionRecord)
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


def AArch64_CheckForSMCUndefOrTrap (imm : (BitVec 16)) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2412) ()) ) : SailM ExceptionRecord
    )
  let vect_offset ← (( do (undefined_int_at (← occLabel 2413) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__9 ← (( do
    if ((← do
         if ((← do
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
              (pure (((! w__5) : Bool)))) : Bool)
         then
           (do
             (HaveEL EL3))
         else (pure false)) : Bool)
    then
      (do
        let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((((_get_SCR_EL3_Type_SMD w__8) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__9 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let route_to_el2 : Bool := false
  let w__10 ← (( do (HaveEL EL3) ) : SailM Bool )
  let route_to_el2 ← (( do
    if ((! w__10) : Bool)
    then
      (do
        let w__13 ← (( do
          if ((← do
               let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__11.EL == EL1) : Bool)))) : Bool)
          then
            (do
              (EL2Enabled ()))
          else (pure false) ) : SailM Bool )
        if (w__13 : Bool)
        then
          (do
            let w__18 ← (( do
              if ((← do
                   if ((← do
                        (HaveNVExt ())) : Bool)
                   then
                     (do
                       let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_HCR_EL2_Type_NV w__15) == 1#1) : Bool))))
                   else (pure false)) : Bool)
              then
                (do
                  let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TSC w__17) == 1#1) : Bool))))
              else (pure false) ) : SailM Bool )
            if (w__18 : Bool)
            then (pure (true))
            else sailThrow ((Error_Undefined ())))
        else sailThrow ((Error_Undefined ())))
    else
      (do
        if ((← do
             if ((← do
                  let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__19.EL == EL1) : Bool)))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TSC w__22) == 1#1) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (route_to_el2 : Bool)
  then
    (do
      let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
      let vect_offset : Int := (BitVec.toNat 0x0#4)
      let w__24 ← (( do (ExceptionSyndrome Exception_MonitorCall) ) : SailM ExceptionRecord )
      let except : ExceptionRecord := (w__24 : ExceptionRecord)
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
  let w__3 ← (( do
    if ((← do
         (pure ((← do
               (HaveEL target_el)) && ((target_el != EL0) : Bool)))) : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__2.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__3 "sail-inputs/03-v8_base.sail:33923.86-33923.87"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let w__4 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  let except ← (( do (AArch64_SystemAccessTrapSyndrome w__4 ec) ) : SailM ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: ec : Int -/
def AArch64_AArch32SystemAccessTrap (target_el : (BitVec 2)) (ec : Int) : SailM Unit := do
  let w__3 ← (( do
    if ((← do
         (pure ((← do
               (HaveEL target_el)) && ((target_el != EL0) : Bool)))) : Bool)
    then
      (do
        let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__2.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__3 "sail-inputs/03-v8_base.sail:34018.86-34018.87"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x0#4)
  let w__4 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  let except ← (( do (AArch64_AArch32SystemAccessTrapSyndrome w__4 ec) ) : SailM ExceptionRecord )
  (AArch64_TakeException target_el except preferred_exception_return vect_offset)


/-- Type quantifiers: k_implicit_esb : Bool -/
def AArch64_TakePhysicalSErrorException (implicit_esb : Bool) : SailM Unit := do
  let route_to_el3 ← (( do
    if ((← do
         (HaveEL EL3)) : Bool)
    then
      (do
        let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((((_get_SCR_EL3_Type_EA w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__2.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__3.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__7) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__8 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__8) : Bool)))) : Bool)
            then
              (do
                let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_AMO w__9) == 1#1) : Bool))))
            else (pure false)))
    else (pure false) ) : SailM Bool )
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x180#12)
  let target_el ← (( do (undefined_bitvector_at (← occLabel 2419) 2) ) : SailM (BitVec 2) )
  let w__13 ← (( do
    (pure ((← do
          let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__12.EL == EL3) : Bool)))) || route_to_el3)) ) : SailM Bool )
  let target_el ← (( do
    if (w__13 : Bool)
    then (pure (EL3))
    else
      (do
        let w__15 ← (( do
          (pure ((← do
                let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__14.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
        let target_el : (BitVec 2) :=
          if (w__15 : Bool)
          then EL2
          else EL1
        (pure (target_el))) ) : SailM (BitVec 2) )
  let except ← (( do (ExceptionSyndrome Exception_SError) ) : SailM ExceptionRecord )
  let syndrome ← (( do (AArch64_PhysicalSErrorSyndrome implicit_esb) ) : SailM (BitVec 25) )
  let w__16 ← (( do (IsSErrorEdgeTriggered ()) ) : SailM Bool )
  let _ : Unit :=
    if (w__16 : Bool)
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:34196.63-34196.64"
  let w__7 ← (( do
    if ((← do
         let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
         (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_AMO w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__7 "sail-inputs/03-v8_base.sail:34197.52-34197.53"
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
    if ((← do
         (HaveEL EL3)) : Bool)
    then
      (do
        let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((((_get_SCR_EL3_Type_IRQ w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__2.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__3.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__7) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_IMO w__8) == 1#1) : Bool)))))
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
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__10.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
          ArmFull.assert (w__12.EL != EL3) "sail-inputs/03-v8_base.sail:34227.31-34227.32"
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          let w__15 ← (( do
            if ((← do
                 let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__13.EL == EL0) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__14.EL == EL1) : Bool)))) ) : SailM Bool )
          ArmFull.assert w__15 "sail-inputs/03-v8_base.sail:34230.50-34230.51"
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:34238.63-34238.64"
  let w__7 ← (( do
    if ((← do
         let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
         (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_IMO w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__7 "sail-inputs/03-v8_base.sail:34239.52-34239.53"
  let preferred_exception_return ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  let vect_offset : Int := (BitVec.toNat 0x80#8)
  let except ← (( do (ExceptionSyndrome Exception_IRQ) ) : SailM ExceptionRecord )
  (AArch64_TakeException EL1 except preferred_exception_return vect_offset)


def AArch64_TakePhysicalFIQException (_ : Unit) : SailM Unit := do
  let route_to_el3 ← (( do
    if ((← do
         (HaveEL EL3)) : Bool)
    then
      (do
        let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
        (pure ((((_get_SCR_EL3_Type_FIQ w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if ((← do
         if ((← do
              if ((← do
                   let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__2.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__3.EL == EL1) : Bool))))) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__7) == 1#1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_FMO w__8) == 1#1) : Bool)))))
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
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__10.EL == EL2) : Bool)))) || route_to_el2)) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
          ArmFull.assert (w__12.EL != EL3) "sail-inputs/03-v8_base.sail:34257.31-34257.32"
          (AArch64_TakeException EL2 except preferred_exception_return vect_offset))
      else
        (do
          let w__15 ← (( do
            if ((← do
                 let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__13.EL == EL0) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__14.EL == EL1) : Bool)))) ) : SailM Bool )
          ArmFull.assert w__15 "sail-inputs/03-v8_base.sail:34260.50-34260.51"
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
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:34268.63-34268.64"
  let w__7 ← (( do
    if ((← do
         let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
         (pure ((((_get_HCR_EL2_Type_TGE w__5) == 0#1) : Bool)))) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_FMO w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__7 "sail-inputs/03-v8_base.sail:34269.52-34269.53"
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


end ArmFull.Functions
