import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0044
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0080
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0220
import ArmFull.Fn.M0227
import ArmFull.Fn.M0229
import ArmFull.Fn.M0243
import ArmFull.Fn.M0248
import ArmFull.Fn.M0250
import ArmFull.Fn.M0252
import ArmFull.Fn.M0253
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255
import ArmFull.Fn.M0259
import ArmFull.Fn.M0260
import ArmFull.Fn.M0261

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

/-- Type quantifiers: ec : Int -/
def AArch32_SystemAccessTrap (mode : (BitVec 5)) (ec : Int) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2709) ()) ) : SailM ExceptionRecord
    )
  let target_el ← (( do (undefined_bitvector_at (← occLabel 2710) 2) ) : SailM (BitVec 2) )
  let valid_name ← (( do (undefined_bool_at (← occLabel 2711) ()) ) : SailM Bool )
  let w__0 ← (( do (ELFromM32 mode) ) : SailM (Bool × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (Bool × (BitVec 2)))
  let valid_name : Bool := tup__0
  let target_el : (BitVec 2) := tup__1
  let w__2 ← (( do
    if ((((valid_name && (HaveEL target_el)) && (target_el != EL0)) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure ((((BitVec.toNat target_el) ≥b (BitVec.toNat w__1.EL)) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__2 "sail-arm/v8_base.sail:41526.101-41526.102"
  if ((target_el == EL2) : Bool)
  then
    (do
      let w__3 ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      let except ← (( do (AArch32_SystemAccessTrapSyndrome w__3 ec) ) : SailM ExceptionRecord )
      (AArch32_TakeHypTrapException__1 except))
  else
    (do
      (AArch32_TakeUndefInstrException ()))


/-- Type quantifiers: k_advsimd : Bool -/
def AArch32_CheckFPAdvSIMDTrap (advsimd : Bool) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2713) ()) ) : SailM ExceptionRecord
    )
  let hcptr_cp10 ← (( do (undefined_bitvector_at (← occLabel 2714) 1) ) : SailM (BitVec 1) )
  let hcptr_tase ← (( do (undefined_bitvector_at (← occLabel 2715) 1) ) : SailM (BitVec 1) )
  let ss ← (( do (undefined_SecurityState (← occLabel 2716) ()) ) : SailM SecurityState )
  let w__2 ← (( do
    if ((← do
         (EL2Enabled ())) : Bool)
    then
      (do
        let w__1 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (AArch64_CheckFPAdvSIMDTrap ()))
  else
    (do
      let w__8 ← (( do
        if ((← do
             if ((← do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__3 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__3) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 let w__5 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
                 (pure ((((_get_CPTR_EL3_Type_TFP w__5) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
      if (((HaveEL EL2) && (bne ss SS_Secure)) : Bool)
      then
        (do
          let w__9 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
          let hcptr_tase : (BitVec 1) := ((_get_HCPTR_Type_TASE w__9) : (BitVec 1))
          let w__10 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
          let hcptr_cp10 : (BitVec 1) := ((_get_HCPTR_Type_TCP10 w__10) : (BitVec 1))
          let w__12 ← (( do
            if (((HaveEL EL3) : Bool) : Bool)
            then
              (do
                (ELUsingAArch32 EL3))
            else (pure false) ) : SailM Bool )
          let (hcptr_cp10, hcptr_tase) ← (( do
            if (w__12 : Bool)
            then
              (do
                let w__13 ← (( do readReg NSACR ) : SailM (BitVec 32) )
                let hcptr_tase : (BitVec 1) :=
                  if (((_get_NSACR_Type_NSASEDIS w__13) == 1#1) : Bool)
                  then 1#1
                  else hcptr_tase
                let w__14 ← (( do readReg NSACR ) : SailM (BitVec 32) )
                let hcptr_cp10 : (BitVec 1) :=
                  if (((_get_NSACR_Type_cp10 w__14) == 0#1) : Bool)
                  then 1#1
                  else hcptr_cp10
                (pure ((hcptr_cp10, hcptr_tase))))
            else (pure ((hcptr_cp10, hcptr_tase))) ) : SailM ((BitVec 1) × (BitVec 1)) )
          if (((advsimd && (hcptr_tase == 1#1)) || (hcptr_cp10 == 1#1)) : Bool)
          then
            (do
              let w__15 ← (( do (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap) ) : SailM
                ExceptionRecord )
              let except : ExceptionRecord := (w__15 : ExceptionRecord)
              let w__16 ← (( do (ConditionSyndrome ()) ) : SailM (BitVec 5) )
              let except :=
                ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 20 w__16) } : ExceptionRecord)
              let except : ExceptionRecord :=
                if (advsimd : Bool)
                then { except with syndrome := (BitVec.update except.syndrome 5 (Bit 1#1)) }
                else
                  (let except : ExceptionRecord :=
                    { except with syndrome := (BitVec.update except.syndrome 5 (Bit 0#1)) }
                  { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 3 0 0b1010#4) })
              let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__17.EL == EL2) : Bool)
              then
                (do
                  (AArch32_TakeUndefInstrException__1 except))
              else
                (do
                  (AArch32_TakeHypTrapException__1 except)))
          else (pure (())))
      else (pure (()))
      let w__19 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__18 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            (pure (((! w__18) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__19 : Bool)
      then
        (do
          let w__20 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
          if (((_get_CPTR_EL3_Type_TFP w__20) == 1#1) : Bool)
          then
            (do
              let w__21 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
              if (w__21 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (AArch64_AdvSIMDFPAccessTrap EL3)))
          else (pure (())))
      else (pure (())))


def AArch32_UndefinedFault (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (AArch32_GeneralExceptionsToAArch64 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch64_UndefinedFault ()))
  else (pure (()))
  (AArch32_TakeUndefInstrException ())


def AArch32_CheckIllegalState (_ : Unit) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (.site 2777) ()) ) : SailM ExceptionRecord )
  let route_to_hyp ← (( do (undefined_bool_at (.site 2778) ()) ) : SailM Bool )
  let vect_offset ← (( do (undefined_int_at (.site 2779) ()) ) : SailM Int )
  let w__0 ← (( do (AArch32_GeneralExceptionsToAArch64 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch64_CheckIllegalState ()))
  else
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.IL == 1#1) : Bool)
      then
        (do
          let route_to_hyp ← (( do
            if ((← do
                 if ((← do
                      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__2.EL == EL0) : Bool)))) : Bool)
                 then
                   (do
                     (EL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                (pure ((((_get_HCR_Type_TGE w__5) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
          let vect_offset : Int := (BitVec.toNat 0x04#8)
          let w__7 ← (( do
            (pure ((← do
                  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__6.EL == EL2) : Bool)))) || route_to_hyp)) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let except ← (( do (ExceptionSyndrome Exception_IllegalState) ) : SailM
                ExceptionRecord )
              let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__8.EL == EL2) : Bool)
              then
                (do
                  (AArch32_EnterHypMode except preferred_exception_return vect_offset))
              else
                (do
                  (AArch32_EnterHypMode except preferred_exception_return (BitVec.toNat 0x14#8))))
          else
            (do
              (AArch32_TakeUndefInstrException ())))
      else (pure (())))


def AArch32_CheckForWFxTrap (target_el : (BitVec 2)) (wfxtype : WFxType) : SailM Unit := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2785) ()) ) : SailM ExceptionRecord
    )
  ArmFull.assert (HaveEL target_el) "sail-arm/v8_base.sail:43067.28-43067.29"
  let w__0 ← (( do (ELUsingAArch32 target_el) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (AArch64_CheckForWFxTrap target_el wfxtype))
  else
    (do
      let is_wfe : Bool := (BEq.beq wfxtype WFxType_WFE)
      let trap ← (( do (undefined_bool_at (← occLabel 2786) ()) ) : SailM Bool )
      let questionMark := target_el
      let trap ← (( do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__3 ← (( do
              if (is_wfe : Bool)
              then
                (do
                  let w__1 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                  (pure ((_get_SCTLR_Type_nTWE w__1))))
              else
                (do
                  let w__2 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                  (pure ((_get_SCTLR_Type_nTWI w__2)))) ) : SailM (BitVec 1) )
            let trap := ((w__3 == 0#1) : Bool)
            (pure (trap)))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__6 ← (( do
                  if (is_wfe : Bool)
                  then
                    (do
                      let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((_get_HCR_Type_TWE w__4))))
                  else
                    (do
                      let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                      (pure ((_get_HCR_Type_TWI w__5)))) ) : SailM (BitVec 1) )
                let trap := ((w__6 == 1#1) : Bool)
                (pure (trap)))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__9 ← (( do
                      if (is_wfe : Bool)
                      then
                        (do
                          let w__7 ← (( do readReg SCR ) : SailM (BitVec 32) )
                          (pure ((_get_SCR_Type_TWE w__7))))
                      else
                        (do
                          let w__8 ← (( do readReg SCR ) : SailM (BitVec 32) )
                          (pure ((_get_SCR_Type_TWI w__8)))) ) : SailM (BitVec 1) )
                    let trap := ((w__9 == 1#1) : Bool)
                    (pure (trap)))
                else (pure (trap)))) ) : SailM Bool )
      if (trap : Bool)
      then
        (do
          let w__15 ← (( do
            if ((← do
                 if ((← do
                      if (((target_el == EL1) : Bool) : Bool)
                      then
                        (do
                          (EL2Enabled ()))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__12 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                     (pure (((! w__12) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__14) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__15 : Bool)
          then
            (do
              (AArch64_WFxTrap wfxtype target_el))
          else (pure (()))
          if ((target_el == EL3) : Bool)
          then
            (do
              (AArch32_TakeMonitorTrapException ()))
          else
            (do
              if ((target_el == EL2) : Bool)
              then
                (do
                  let w__16 ← (( do (ExceptionSyndrome Exception_WFxTrap) ) : SailM
                    ExceptionRecord )
                  let except : ExceptionRecord := (w__16 : ExceptionRecord)
                  let w__17 ← (( do (ConditionSyndrome ()) ) : SailM (BitVec 5) )
                  let except :=
                    ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 20
                        w__17) } : ExceptionRecord)
                  let except : ExceptionRecord :=
                    match wfxtype with
                    | .WFxType_WFI =>
                      { except with syndrome := (BitVec.update except.syndrome 0 (Bit 0#1)) }
                    | .WFxType_WFE =>
                      { except with syndrome := (BitVec.update except.syndrome 0 (Bit 1#1)) }
                    | _ => except
                  (AArch32_TakeHypTrapException__1 except))
              else
                (do
                  (AArch32_TakeUndefInstrException ()))))
      else (pure (())))


def TakePendingInterrupts (interrupt_req : InterruptReq) : SailM Bool := do
  let interrupt_pend ← (( do (undefined_bool_at (← occLabel 2871) ()) ) : SailM Bool )
  let interrupt_taken ← (( do (undefined_bool_at (← occLabel 2872) ()) ) : SailM Bool )
  let vAA ← (( do (undefined_bool_at (← occLabel 2873) ()) ) : SailM Bool )
  let vIRQ ← (( do (undefined_bool_at (← occLabel 2874) ()) ) : SailM Bool )
  let vSE ← (( do (undefined_bool_at (← occLabel 2875) ()) ) : SailM Bool )
  let vFIQ ← (( do (undefined_bool_at (← occLabel 2876) ()) ) : SailM Bool )
  let AA ← (( do (undefined_bool_at (← occLabel 2877) ()) ) : SailM Bool )
  let IRQ ← (( do (undefined_bool_at (← occLabel 2878) ()) ) : SailM Bool )
  let FIQ ← (( do (undefined_bool_at (← occLabel 2879) ()) ) : SailM Bool )
  let SE ← (( do (undefined_bool_at (← occLabel 2880) ()) ) : SailM Bool )
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (AArch32_PendingUnmaskedVirtualInterrupts ()) ) : SailM
        (Bool × Bool × Bool) )
      let (tup__0, tup__1, tup__2) := (w__1 : (Bool × Bool × Bool))
      let vAA : Bool := tup__0
      let vIRQ : Bool := tup__1
      let vFIQ : Bool := tup__2
      let w__2 ← (( do (AArch32_PendingUnmaskedPhysicalInterrupts ()) ) : SailM
        (Bool × Bool × Bool) )
      let (tup__0, tup__1, tup__2) := (w__2 : (Bool × Bool × Bool))
      let AA : Bool := tup__0
      let IRQ : Bool := tup__1
      let FIQ : Bool := tup__2
      let AA : Bool :=
        if ((! interrupt_req.take_SE) : Bool)
        then false
        else AA
      let vAA : Bool :=
        if ((! interrupt_req.take_vSE) : Bool)
        then false
        else vAA
      let IRQ : Bool :=
        if ((! interrupt_req.take_IRQ) : Bool)
        then false
        else IRQ
      let vIRQ : Bool :=
        if ((! interrupt_req.take_vIRQ) : Bool)
        then false
        else vIRQ
      let FIQ : Bool :=
        if ((! interrupt_req.take_FIQ) : Bool)
        then false
        else FIQ
      let vFIQ : Bool :=
        if ((! interrupt_req.take_vFIQ) : Bool)
        then false
        else vFIQ
      let interrupt_taken : Bool :=
        if ((((((AA || FIQ) || IRQ) || vAA) || vFIQ) || vIRQ) : Bool)
        then true
        else false
      if (vFIQ : Bool)
      then
        (do
          (AArch32_TakeVirtualFIQException ()))
      else
        (do
          if (vIRQ : Bool)
          then
            (do
              (AArch32_TakeVirtualIRQException ()))
          else
            (do
              if (vAA : Bool)
              then
                (do
                  (AArch32_TakeVirtualSErrorException ()))
              else
                (do
                  if (FIQ : Bool)
                  then
                    (do
                      (AArch32_TakePhysicalFIQException ()))
                  else
                    (do
                      if (IRQ : Bool)
                      then
                        (do
                          (AArch32_TakePhysicalIRQException ()))
                      else
                        (do
                          if (AA : Bool)
                          then
                            (do
                              (AArch32_TakePhysicalSErrorException interrupt_req.iesb_req))
                          else (pure (())))))))
      (pure (interrupt_taken)))
  else
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__6 ← (( do (AArch64_PendingUnmaskedVirtualInterrupts (w__3.A +++ (w__4.I +++ w__5.F)))
        ) : SailM (Bool × Bool × Bool) )
      let (tup__0, tup__1, tup__2) := (w__6 : (Bool × Bool × Bool))
      let vSE : Bool := tup__0
      let vIRQ : Bool := tup__1
      let vFIQ : Bool := tup__2
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__10 ← (( do
        (AArch64_PendingUnmaskedPhysicalInterrupts (w__7.A +++ (w__8.I +++ w__9.F))) ) : SailM
        (Bool × Bool × Bool) )
      let (tup__0, tup__1, tup__2) := (w__10 : (Bool × Bool × Bool))
      let SE : Bool := tup__0
      let IRQ : Bool := tup__1
      let FIQ : Bool := tup__2
      let SE : Bool :=
        if ((! interrupt_req.take_SE) : Bool)
        then false
        else SE
      let vSE : Bool :=
        if ((! interrupt_req.take_vSE) : Bool)
        then false
        else vSE
      let IRQ : Bool :=
        if ((! interrupt_req.take_IRQ) : Bool)
        then false
        else IRQ
      let vIRQ : Bool :=
        if ((! interrupt_req.take_vIRQ) : Bool)
        then false
        else vIRQ
      let FIQ : Bool :=
        if ((! interrupt_req.take_FIQ) : Bool)
        then false
        else FIQ
      let vFIQ : Bool :=
        if ((! interrupt_req.take_vFIQ) : Bool)
        then false
        else vFIQ
      let (FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE) ← (( do
        if ((((((SE || FIQ) || IRQ) || vSE) || vFIQ) || vIRQ) : Bool)
        then
          (do
            let w__13 ← (( do
              if ((← do
                   (HaveTME ())) : Bool)
              then
                (do
                  let w__12 ← (( do readReg TSTATE ) : SailM TMState )
                  (pure (((w__12.depth >b 0) : Bool))))
              else (pure false) ) : SailM Bool )
            let (FIQ, IRQ, SE, vFIQ, vIRQ, vSE) ← (( do
              if (w__13 : Bool)
              then
                (do
                  let w__14 ← (( do readReg TSTATE ) : SailM TMState )
                  let w__15 ← (( do readReg TSTATE ) : SailM TMState )
                  let w__16 ← (( do readReg TSTATE ) : SailM TMState )
                  let w__17 ← (( do
                    (AArch64_PendingUnmaskedVirtualInterrupts (w__14.A +++ (w__15.I +++ w__16.F))) )
                    : SailM (Bool × Bool × Bool) )
                  let (tup__0, tup__1, tup__2) := (w__17 : (Bool × Bool × Bool))
                  let vSE : Bool := tup__0
                  let vIRQ : Bool := tup__1
                  let vFIQ : Bool := tup__2
                  let w__18 ← (( do readReg TSTATE ) : SailM TMState )
                  let w__19 ← (( do readReg TSTATE ) : SailM TMState )
                  let w__20 ← (( do readReg TSTATE ) : SailM TMState )
                  let w__21 ← (( do
                    (AArch64_PendingUnmaskedPhysicalInterrupts (w__18.A +++ (w__19.I +++ w__20.F)))
                    ) : SailM (Bool × Bool × Bool) )
                  let (tup__0, tup__1, tup__2) := (w__21 : (Bool × Bool × Bool))
                  let SE : Bool := tup__0
                  let IRQ : Bool := tup__1
                  let FIQ : Bool := tup__2
                  let SE : Bool :=
                    if ((! interrupt_req.take_SE) : Bool)
                    then false
                    else SE
                  let vSE : Bool :=
                    if ((! interrupt_req.take_vSE) : Bool)
                    then false
                    else vSE
                  let IRQ : Bool :=
                    if ((! interrupt_req.take_IRQ) : Bool)
                    then false
                    else IRQ
                  let vIRQ : Bool :=
                    if ((! interrupt_req.take_vIRQ) : Bool)
                    then false
                    else vIRQ
                  let FIQ : Bool :=
                    if ((! interrupt_req.take_FIQ) : Bool)
                    then false
                    else FIQ
                  let vFIQ : Bool :=
                    if ((! interrupt_req.take_vFIQ) : Bool)
                    then false
                    else vFIQ
                  let interrupt_pend : Bool := (((((SE || FIQ) || IRQ) || vSE) || vFIQ) || vIRQ)
                  (FailTransaction__1 TMFailure_IMP interrupt_pend (! interrupt_pend)
                    (Zeros (n := 15)))
                  (pure ((FIQ, IRQ, SE, vFIQ, vIRQ, vSE))))
              else (pure ((FIQ, IRQ, SE, vFIQ, vIRQ, vSE))) ) : SailM
              (Bool × Bool × Bool × Bool × Bool × Bool) )
            let interrupt_taken : Bool := true
            (pure ((FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE))))
        else
          (let interrupt_taken : Bool := false
          (pure ((FIQ, IRQ, SE, interrupt_taken, vFIQ, vIRQ, vSE)))) ) : SailM
        (Bool × Bool × Bool × Bool × Bool × Bool × Bool) )
      if (vFIQ : Bool)
      then
        (do
          (AArch64_TakeVirtualFIQException ()))
      else
        (do
          if (vIRQ : Bool)
          then
            (do
              (AArch64_TakeVirtualIRQException ()))
          else
            (do
              if (vSE : Bool)
              then
                (do
                  (AArch64_TakeVirtualSErrorException ()))
              else
                (do
                  if (FIQ : Bool)
                  then
                    (do
                      (AArch64_TakePhysicalFIQException ()))
                  else
                    (do
                      if (IRQ : Bool)
                      then
                        (do
                          (AArch64_TakePhysicalIRQException ()))
                      else
                        (do
                          if (SE : Bool)
                          then
                            (do
                              (AArch64_TakePhysicalSErrorException interrupt_req.iesb_req))
                          else (pure (())))))))
      (pure (interrupt_taken)))


/-- Type quantifiers: t : Int, t2 : Int -/
def AMEVCNTR0_SysRegWrite64_00363288e0ffc481 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__1)
  let w__8 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     if ((← do
                          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__2.EL == EL1) : Bool)))) : Bool)
                     then
                       (do
                         (EL2Enabled ()))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                    (pure (((! w__5) : Bool))))
                else (pure false)) && ((0 <b 8) : Bool)))) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) :
    SailM Bool )
  if (w__8 : Bool)
  then
    (do
      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x04#8)))
  else
    (do
      let w__15 ← (( do
        (pure ((← do
              (pure ((← do
                    if ((← do
                         if ((← do
                              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                         then
                           (do
                             (EL2Enabled ()))
                         else (pure false)) : Bool)
                    then
                      (do
                        (ELUsingAArch32 EL2))
                    else (pure false)) && ((0 <b 8) : Bool)))) && ((__HSTR_T0 == 1#1) : Bool))) ) :
        SailM Bool )
      if (w__15 : Bool)
      then
        (do
          (AArch32_TakeHypTrapException (BitVec.toNat 0x04#8)))
      else
        (do
          let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((IsHighestEL w__16.EL) : Bool)
          then
            (do
              let w__17 ← (( do readReg AMEVCNTR0 ) : SailM (Vector (BitVec 64) 4) )
              let w__18 ← (( do (R_read t2) ) : SailM (BitVec 32) )
              let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
              writeReg AMEVCNTR0 (vectorUpdate w__17 0 (Mk_AMEVCNTR0_Type (w__18 +++ w__19))))
          else sailThrow ((Error_Undefined ()))))


end ArmFull.Functions
