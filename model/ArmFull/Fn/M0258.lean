import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0052
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0172
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0253

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

def CheckOriginalSVEEnabled (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  ArmFull.assert w__0 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:29250.20-29250.21"
  let disabled ← (( do (undefined_bool_at (← occLabel 1710) ()) ) : SailM Bool )
  let w__6 ← (( do
    if ((← do
         if (((HaveEL EL3) : Bool) : Bool)
         then
           (do
             if ((← do
                  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_CPTR_EL3_Type_EZ w__1) == 0#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__2 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
                 (pure ((((_get_CPTR_EL3_Type_TFP w__2) == 1#1) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        (EL3SDDUndefPriority ()))
    else (pure false) ) : SailM Bool )
  if (w__6 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__11 ← (( do
    if ((← do
         if ((← do
              let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__7.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__8.EL == EL1) : Bool))))) : Bool)
    then
      (do
        let w__10 ← (( do (IsInHost ()) ) : SailM Bool )
        (pure (((! w__10) : Bool))))
    else (pure false) ) : SailM Bool )
  let disabled ← (( do
    if (w__11 : Bool)
    then
      (do
        let w__12 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
        let b__0 := (_get_CPACR_EL1_Type_ZEN w__12)
        let disabled ← (( do
          if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
          then (pure (true))
          else
            (do
              match b__0 with
              | 0b01 =>
                (do
                  let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                  let disabled := ((w__13.EL == EL0) : Bool)
                  (pure (disabled)))
              | _ => (pure (false))) ) : SailM Bool )
        if (disabled : Bool)
        then
          (do
            (SVEAccessTrap EL1))
        else (pure (()))
        let w__14 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
        let b__1 := (_get_CPACR_EL1_Type_FPEN w__14)
        let disabled ← (( do
          if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
          then (pure (true))
          else
            (do
              match b__1 with
              | 0b01 =>
                (do
                  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                  let disabled := ((w__15.EL == EL0) : Bool)
                  (pure (disabled)))
              | _ => (pure (false))) ) : SailM Bool )
        if (disabled : Bool)
        then
          (do
            (AArch64_AdvSIMDFPAccessTrap EL1))
        else (pure (()))
        (pure (disabled)))
    else (pure (disabled)) ) : SailM Bool )
  let w__22 ← (( do
    if ((← do
         if ((← do
              let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__16.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__17.EL == EL1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__18.EL == EL2) : Bool)))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__22 : Bool)
  then
    (do
      let w__25 ← (( do
        if ((← do
             (HaveVirtHostExt ())) : Bool)
        then
          (do
            let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_E2H w__24) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__25 : Bool)
      then
        (do
          let w__26 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          let b__2 := (_get_CPTR_EL2_Type_ZEN w__26)
          let disabled ← (( do
            if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 0 0)) == (0#1 : (BitVec 1))) : Bool)
            then (pure (true))
            else
              (do
                match b__2 with
                | 0b01 =>
                  (do
                    if ((← do
                         let w__27 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__27.EL == EL0) : Bool)))) : Bool)
                    then
                      (do
                        let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__28) == 1#1) : Bool))))
                    else (pure false))
                | _ => (pure (false))) ) : SailM Bool )
          if (disabled : Bool)
          then
            (do
              (SVEAccessTrap EL2))
          else (pure (()))
          let w__30 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          let b__3 := (_get_CPTR_EL2_Type_FPEN w__30)
          let disabled ← (( do
            if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
            then (pure (true))
            else
              (do
                match b__3 with
                | 0b01 =>
                  (do
                    if ((← do
                         let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__31.EL == EL0) : Bool)))) : Bool)
                    then
                      (do
                        let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__32) == 1#1) : Bool))))
                    else (pure false))
                | _ => (pure (false))) ) : SailM Bool )
          if (disabled : Bool)
          then
            (do
              (AArch64_AdvSIMDFPAccessTrap EL2))
          else (pure (())))
      else
        (do
          let w__34 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          if (((_get_CPTR_EL2_Type_TZ w__34) == 1#1) : Bool)
          then
            (do
              (SVEAccessTrap EL2))
          else (pure (()))
          let w__35 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          if (((_get_CPTR_EL2_Type_TFP w__35) == 1#1) : Bool)
          then
            (do
              (AArch64_AdvSIMDFPAccessTrap EL2))
          else (pure (()))))
  else (pure (()))
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__36 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      if (((_get_CPTR_EL3_Type_EZ w__36) == 0#1) : Bool)
      then
        (do
          let w__37 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
          if (w__37 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (SVEAccessTrap EL3)))
      else (pure (()))
      let w__38 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      if (((_get_CPTR_EL3_Type_TFP w__38) == 1#1) : Bool)
      then
        (do
          let w__39 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
          if (w__39 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (AArch64_AdvSIMDFPAccessTrap EL3)))
      else (pure (())))
  else (pure (()))


def CheckSMEEnabled (_ : Unit) : SailM Unit := do
  let disabled ← (( do (undefined_bool_at (← occLabel 1711) ()) ) : SailM Bool )
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
        let w__3 ← (( do (IsInHost ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  let disabled ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
        let b__0 := (_get_CPACR_EL1_Type_SMEN w__5)
        let disabled ← (( do
          if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
          then (pure (true))
          else
            (do
              match b__0 with
              | 0b01 =>
                (do
                  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                  let disabled := ((w__6.EL == EL0) : Bool)
                  (pure (disabled)))
              | _ => (pure (false))) ) : SailM Bool )
        if (disabled : Bool)
        then
          (do
            (SMEAccessTrap SMEExceptionType_AccessTrap EL1))
        else (pure (()))
        let w__7 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
        let b__1 := (_get_CPACR_EL1_Type_FPEN w__7)
        let disabled ← (( do
          if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
          then (pure (true))
          else
            (do
              match b__1 with
              | 0b01 =>
                (do
                  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                  let disabled := ((w__8.EL == EL0) : Bool)
                  (pure (disabled)))
              | _ => (pure (false))) ) : SailM Bool )
        if (disabled : Bool)
        then
          (do
            (AArch64_AdvSIMDFPAccessTrap EL1))
        else (pure (()))
        (pure (disabled)))
    else (pure (disabled)) ) : SailM Bool )
  let w__15 ← (( do
    if ((← do
         if ((← do
              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__9.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__10.EL == EL1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__11.EL == EL2) : Bool)))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__15 : Bool)
  then
    (do
      let w__18 ← (( do
        if ((← do
             (HaveVirtHostExt ())) : Bool)
        then
          (do
            let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_E2H w__17) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__18 : Bool)
      then
        (do
          let w__19 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          let b__2 := (_get_CPTR_EL2_Type_SMEN w__19)
          let disabled ← (( do
            if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 0 0)) == (0#1 : (BitVec 1))) : Bool)
            then (pure (true))
            else
              (do
                match b__2 with
                | 0b01 =>
                  (do
                    if ((← do
                         let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__20.EL == EL0) : Bool)))) : Bool)
                    then
                      (do
                        let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__21) == 1#1) : Bool))))
                    else (pure false))
                | _ => (pure (false))) ) : SailM Bool )
          if (disabled : Bool)
          then
            (do
              (SMEAccessTrap SMEExceptionType_AccessTrap EL2))
          else (pure (()))
          let w__23 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          let b__3 := (_get_CPTR_EL2_Type_FPEN w__23)
          let disabled ← (( do
            if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
            then (pure (true))
            else
              (do
                match b__3 with
                | 0b01 =>
                  (do
                    if ((← do
                         let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__24.EL == EL0) : Bool)))) : Bool)
                    then
                      (do
                        let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__25) == 1#1) : Bool))))
                    else (pure false))
                | _ => (pure (false))) ) : SailM Bool )
          if (disabled : Bool)
          then
            (do
              (AArch64_AdvSIMDFPAccessTrap EL2))
          else (pure (())))
      else
        (do
          let w__27 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          if (((_get_CPTR_EL2_Type_TSM w__27) == 1#1) : Bool)
          then
            (do
              (SMEAccessTrap SMEExceptionType_AccessTrap EL2))
          else (pure (()))
          let w__28 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          if (((_get_CPTR_EL2_Type_TFP w__28) == 1#1) : Bool)
          then
            (do
              (AArch64_AdvSIMDFPAccessTrap EL2))
          else (pure (()))))
  else (pure (()))
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__29 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      if (((_get_CPTR_EL3_Type_ESM w__29) == 0#1) : Bool)
      then
        (do
          (SMEAccessTrap SMEExceptionType_AccessTrap EL3))
      else (pure (()))
      let w__30 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      if (((_get_CPTR_EL3_Type_TFP w__30) == 1#1) : Bool)
      then
        (do
          (AArch64_AdvSIMDFPAccessTrap EL3))
      else (pure (())))
  else (pure (()))


def CheckSMEZT0Enabled (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.ZA == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (SMEAccessTrap SMEExceptionType_InactiveZA w__1.EL))
  else (pure (()))
  let w__6 ← (( do
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
        let w__5 ← (( do (IsInHost ()) ) : SailM Bool )
        (pure (((! w__5) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      let w__7 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
      if (((_get_SMCR_EL1_Type_EZT0 w__7) == 0#1) : Bool)
      then
        (do
          (SMEAccessTrap SMEExceptionType_InaccessibleZT0 EL1))
      else (pure (())))
  else (pure (()))
  let w__14 ← (( do
    if ((← do
         if ((← do
              let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__8.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__9.EL == EL1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__10.EL == EL2) : Bool)))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__14 : Bool)
  then
    (do
      let w__15 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
      if (((_get_SMCR_EL2_Type_EZT0 w__15) == 0#1) : Bool)
      then
        (do
          (SMEAccessTrap SMEExceptionType_InaccessibleZT0 EL2))
      else (pure (())))
  else (pure (()))
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__16 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
      if (((_get_SMCR_EL3_Type_EZT0 w__16) == 0#1) : Bool)
      then
        (do
          (SMEAccessTrap SMEExceptionType_InaccessibleZT0 EL3))
      else (pure (())))
  else (pure (()))


def CheckSMEAccess (_ : Unit) : SailM Unit := do
  let disabled ← (( do (undefined_bool_at (← occLabel 1712) ()) ) : SailM Bool )
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
        let w__3 ← (( do (IsInHost ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  let disabled ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
        let b__0 := (_get_CPACR_EL1_Type_SMEN w__5)
        let disabled ← (( do
          if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
          then (pure (true))
          else
            (do
              match b__0 with
              | 0b01 =>
                (do
                  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                  let disabled := ((w__6.EL == EL0) : Bool)
                  (pure (disabled)))
              | _ => (pure (false))) ) : SailM Bool )
        if (disabled : Bool)
        then
          (do
            (SMEAccessTrap SMEExceptionType_AccessTrap EL1))
        else (pure (()))
        (pure (disabled)))
    else (pure (disabled)) ) : SailM Bool )
  let w__13 ← (( do
    if ((← do
         if ((← do
              let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__7.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__8.EL == EL1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__9.EL == EL2) : Bool)))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__13 : Bool)
  then
    (do
      let w__16 ← (( do
        if ((← do
             (HaveVirtHostExt ())) : Bool)
        then
          (do
            let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_E2H w__15) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__16 : Bool)
      then
        (do
          let w__17 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          let b__1 := (_get_CPTR_EL2_Type_SMEN w__17)
          let disabled ← (( do
            if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
            then (pure (true))
            else
              (do
                match b__1 with
                | 0b01 =>
                  (do
                    if ((← do
                         let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__18.EL == EL0) : Bool)))) : Bool)
                    then
                      (do
                        let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__19) == 1#1) : Bool))))
                    else (pure false))
                | _ => (pure (false))) ) : SailM Bool )
          if (disabled : Bool)
          then
            (do
              (SMEAccessTrap SMEExceptionType_AccessTrap EL2))
          else (pure (())))
      else
        (do
          let w__21 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          if (((_get_CPTR_EL2_Type_TSM w__21) == 1#1) : Bool)
          then
            (do
              (SMEAccessTrap SMEExceptionType_AccessTrap EL2))
          else (pure (()))))
  else (pure (()))
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__22 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      if (((_get_CPTR_EL3_Type_ESM w__22) == 0#1) : Bool)
      then
        (do
          (SMEAccessTrap SMEExceptionType_AccessTrap EL3))
      else (pure (())))
  else (pure (()))


def CheckGCSSTREnabled (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__0.EL
  if ((questionMark == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
      if (((_get_GCSCRE0_EL1_Type_STREn w__1) == 0#1) : Bool)
      then
        (do
          let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
          if (((_get_HCR_EL2_Type_TGE w__2) == 0#1) : Bool)
          then
            (do
              (GCSSTRTrapException EL1))
          else
            (do
              (GCSSTRTrapException EL2)))
      else (pure (())))
  else
    (do
      if ((questionMark == EL1) : Bool)
      then
        (do
          let w__3 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
          if (((_get_GCSCR_EL1_Type_STREn w__3) == 0#1) : Bool)
          then
            (do
              (GCSSTRTrapException EL1))
          else
            (do
              let w__9 ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         if (((! (HaveEL EL3)) : Bool) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_FGTEn w__5) == 1#1) : Bool)))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HFGITR_EL2_Type_nGCSSTR_EL1 w__8) == 0#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (GCSSTRTrapException EL2))
              else (pure (()))))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__10 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
              if (((_get_GCSCR_EL2_Type_STREn w__10) == 0#1) : Bool)
              then
                (do
                  (GCSSTRTrapException EL2))
              else (pure (())))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__11 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
                  if (((_get_GCSCR_EL3_Type_STREn w__11) == 0#1) : Bool)
                  then
                    (do
                      (GCSSTRTrapException EL3))
                  else (pure (())))
              else (pure (())))))


end ArmFull.Functions
