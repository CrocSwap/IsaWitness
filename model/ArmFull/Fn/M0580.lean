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
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0087
import ArmFull.Fn.M0113
import ArmFull.Fn.M0115
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0158
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0195
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0229
import ArmFull.Fn.M0244
import ArmFull.Fn.M0250
import ArmFull.Fn.M0251
import ArmFull.Fn.M0252
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

def __CycleEnd (_ : Unit) : SailM Unit := do
  (SPECycle ())
  (__UpdateSystemCounter ())
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch32_PMUCycle ()))
  else
    (do
      (AArch64_PMUCycle ()))
  (__EndCycle ())


/-- Type quantifiers: localtimeout : Int -/
def Hint_WFE (localtimeout : Int) (wfxtype : WFxType) : SailM Unit := do
  let delay ← (( do (undefined_int_at (← occLabel 730) ()) ) : SailM Int )
  let delay_enabled ← (( do (undefined_bool_at (← occLabel 731) ()) ) : SailM Bool )
  let sctlr ← (( do (undefined_SCTLRType (← occLabel 732) ()) ) : SailM SCTLRType )
  let trap ← (( do (undefined_bool_at (← occLabel 733) ()) ) : SailM Bool )
  let w__0 ← (( do (IsEventRegisterSet ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (ClearEventRegister ()))
  else
    (do
      let w__3 ← (( do
        if ((← do
             (HaveFeatWFxT ())) : Bool)
        then
          (do
            (LocalTimeoutEvent localtimeout))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (EndOfInstruction ()))
      else
        (do
          let target_el ← (( do (undefined_bitvector_at (← occLabel 734) 2) ) : SailM (BitVec 2)
            )
          let trap : Bool := false
          let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
          let (target_el, trap) ← (( do
            if ((w__4.EL == EL0) : Bool)
            then
              (do
                let w__5 ← (( do (HaveTWEDExt ()) ) : SailM Bool )
                if (w__5 : Bool)
                then
                  (do
                    let sctlr ← (( do (SCTLR_read__1 ()) ) : SailM SCTLRType )
                    let trap : Bool := ((_get_SCTLRType_nTWE sctlr) == 0#1)
                    let target_el : (BitVec 2) := EL1
                    (pure ((target_el, trap))))
                else
                  (do
                    (AArch64_CheckForWFxTrap EL1 wfxtype)
                    (pure ((target_el, trap)))))
            else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
          let w__13 ← (( do
            if ((← do
                 if ((← do
                      if (((! trap) : Bool) : Bool)
                      then
                        (do
                          if ((← do
                               let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                               (pure (((w__6.EL == EL0) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__7.EL == EL1) : Bool)))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (EL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__12 ← (( do (IsInHost ()) ) : SailM Bool )
                (pure (((! w__12) : Bool))))
            else (pure false) ) : SailM Bool )
          let (target_el, trap) ← (( do
            if (w__13 : Bool)
            then
              (do
                let w__14 ← (( do (HaveTWEDExt ()) ) : SailM Bool )
                if (w__14 : Bool)
                then
                  (do
                    let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let trap := (((_get_HCR_EL2_Type_TWE w__15) == 1#1) : Bool)
                    let target_el : (BitVec 2) := EL2
                    (pure ((target_el, trap))))
                else
                  (do
                    (AArch64_CheckForWFxTrap EL2 wfxtype)
                    (pure ((target_el, trap)))))
            else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
          let w__17 ← (( do
            if ((((! trap) && (HaveEL EL3)) : Bool) : Bool)
            then
              (do
                let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__16.EL != EL3) : Bool))))
            else (pure false) ) : SailM Bool )
          let (target_el, trap) ← (( do
            if (w__17 : Bool)
            then
              (do
                let w__18 ← (( do (HaveTWEDExt ()) ) : SailM Bool )
                if (w__18 : Bool)
                then
                  (do
                    let w__19 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                    let trap := (((_get_SCR_EL3_Type_TWE w__19) == 1#1) : Bool)
                    let target_el : (BitVec 2) := EL3
                    (pure ((target_el, trap))))
                else
                  (do
                    (AArch64_CheckForWFxTrap EL3 wfxtype)
                    (pure ((target_el, trap)))))
            else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
          let w__21 ← (( do
            if ((trap : Bool) : Bool)
            then
              (do
                let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__20.EL != EL3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              let w__22 ← (( do (WFETrapDelay target_el) ) : SailM (Bool × Int) )
              let (tup__0, tup__1) := (w__22 : (Bool × Int))
              let delay_enabled : Bool := tup__0
              let delay : Int := tup__1
              let delay : Int := delay
              let w__23 ← (( do (WaitForEventUntilDelay delay_enabled delay) ) : SailM Bool )
              if ((! w__23) : Bool)
              then
                (do
                  (AArch64_WFxTrap wfxtype target_el))
              else (pure (())))
          else
            (do
              (WaitForEvent localtimeout))))


/-- Type quantifiers: localtimeout : Int -/
def Hint_WFI (localtimeout : Int) (wfxtype : WFxType) : SailM Unit := do
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
      (FailTransaction TMFailure_ERR false))
  else (pure (()))
  let w__7 ← (( do
    if ((← do
         (InterruptPending ())) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (HaveFeatWFxT ())) : Bool)
        then
          (do
            (LocalTimeoutEvent localtimeout))
        else (pure false)) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (EndOfInstruction ()))
  else
    (do
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__8.EL == EL0) : Bool)
      then
        (do
          (AArch64_CheckForWFxTrap EL1 wfxtype))
      else (pure (()))
      let w__15 ← (( do
        if ((← do
             if ((← do
                  if ((← do
                       let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__9.EL == EL0) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__10.EL == EL1) : Bool))))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__14 ← (( do (IsInHost ()) ) : SailM Bool )
            (pure (((! w__14) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__15 : Bool)
      then
        (do
          (AArch64_CheckForWFxTrap EL2 wfxtype))
      else (pure (()))
      let w__17 ← (( do
        if (((HaveEL EL3) : Bool) : Bool)
        then
          (do
            let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__16.EL != EL3) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          (AArch64_CheckForWFxTrap EL3 wfxtype))
      else (pure (()))
      (WaitForInterrupt localtimeout))


def AArch32_Abort (vaddress : (BitVec 32)) (fault : FaultRecord) : SailM Unit := do
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
             if ((← do
                  if ((← do
                       let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_HCR_EL2_Type_TGE w__6) == 1#1) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      (IsSecondStage fault))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      if ((← do
                           (HaveRASExt ())) : Bool)
                      then
                        (do
                          let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_TEA w__10) == 1#1) : Bool))))
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
                let w__16 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL2_Type_TDE w__16) == 1#1) : Bool))))
            else (pure false)))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  let w__20 ← (( do
    if ((((! route_to_aarch64) && (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__19 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
        (pure (((! w__19) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_aarch64 ← (( do
    if (w__20 : Bool)
    then
      (do
        if ((← do
             let w__21 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
             (pure (((w__21 == 1#1) : Bool)))) : Bool)
        then
          (do
            (IsExternalAbort__1 fault))
        else (pure false))
    else (pure (route_to_aarch64)) ) : SailM Bool )
  if (route_to_aarch64 : Bool)
  then
    (do
      (AArch64_Abort (Sail.BitVec.zeroExtend vaddress 64) fault))
  else
    (do
      if ((BEq.beq fault.access.acctype AccessType_IFETCH) : Bool)
      then
        (do
          (AArch32_TakePrefetchAbortException vaddress fault))
      else
        (do
          (AArch32_TakeDataAbortException vaddress fault)))


def AArch32_FPTrappedException (accumulated_exceptions : (BitVec 8)) : SailM Unit := do
  let element ← (( do (undefined_int_at (← occLabel 888) ()) ) : SailM Int )
  let is_ase ← (( do (undefined_bool_at (← occLabel 889) ()) ) : SailM Bool )
  let w__0 ← (( do (AArch32_GeneralExceptionsToAArch64 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let is_ase : Bool := false
      let element : Int := 0
      (AArch64_FPTrappedException is_ase accumulated_exceptions))
  else (pure (()))
  let w__1 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_DEX w__1 1#1))
  let w__2 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_TFV w__2 1#1))
  let w__3 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write
    (Mk_FPEXC_Type
      (Sail.BitVec.updateSubrange w__3 7 7
        (BitVec.slice
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access accumulated_exceptions 7)])) +++ (Sail.BitVec.extractLsb
              accumulated_exceptions 4 0)) 5 1))))
  let w__4 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write
    (Mk_FPEXC_Type
      (Sail.BitVec.updateSubrange w__4 4 0
        (BitVec.slice
          ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access accumulated_exceptions 7)])) +++ (Sail.BitVec.extractLsb
              accumulated_exceptions 4 0)) 0 5))))
  let w__5 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (Mk_FPEXC_Type (Sail.BitVec.updateSubrange w__5 10 8 0b111#3)))
  (AArch32_TakeUndefInstrException ())


/-- Type quantifiers: k_is_combined : Bool -/
def AuthIA (x : (BitVec 64)) (y : (BitVec 64)) (is_combined : Bool) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1323) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1324) ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector_at (← occLabel 1325) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg APIAKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APIAKeyLo_EL1 ) : SailM (BitVec 64) )
  let APIAKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (Enable, TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__3 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__3 == EL1)
        let w__6 ← (( do
          if (IsEL1Regime : Bool)
          then
            (do
              let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EnIA w__4))))
          else
            (do
              let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EnIA w__5)))) ) : SailM (BitVec 1) )
        let Enable := (w__6 : (BitVec 1))
        let w__13 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__10) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__11) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__13 : Bool)
        let w__15 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__14) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__15 : Bool)
        (pure ((Enable, TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__16 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let Enable := ((_get_SCTLR_EL1_Type_EnIA w__16) : (BitVec 1))
            let w__19 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__18) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__19 : Bool)
            let w__21 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__20) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__21 : Bool)
            (pure ((Enable, TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let Enable := ((_get_SCTLR_EL2_Type_EnIA w__22) : (BitVec 1))
                let TrapEL2 : Bool := false
                let w__24 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__23) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__24 : Bool)
                (pure ((Enable, TrapEL2, TrapEL3))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let Enable := ((_get_SCTLR_EL3_Type_EnIA w__25) : (BitVec 1))
                    let TrapEL2 : Bool := false
                    let TrapEL3 : Bool := false
                    (pure ((Enable, TrapEL2, TrapEL3))))
                else (pure ((Enable, TrapEL2, TrapEL3)))))) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure (x))
  else
    (do
      let w__27 ← (( do
        if ((TrapEL3 : Bool) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__27 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector_at (← occLabel 1327) 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  let w__30 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector_at (← occLabel 1326) 64)))
              else
                (do
                  (Auth x y APIAKey_EL1 false 0#1 is_combined)))))


/-- Type quantifiers: k_is_combined : Bool -/
def AuthIB (x : (BitVec 64)) (y : (BitVec 64)) (is_combined : Bool) : SailM (BitVec 64) := do
  let TrapEL2 ← (( do (undefined_bool_at (← occLabel 1328) ()) ) : SailM Bool )
  let TrapEL3 ← (( do (undefined_bool_at (← occLabel 1329) ()) ) : SailM Bool )
  let Enable ← (( do (undefined_bitvector_at (← occLabel 1330) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg APIBKeyHi_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg APIBKeyLo_EL1 ) : SailM (BitVec 64) )
  let APIBKey_EL1 : (BitVec 128) :=
    ((Sail.BitVec.extractLsb w__0 63 0) +++ (Sail.BitVec.extractLsb w__1 63 0))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let questionMark := w__2.EL
  let (Enable, TrapEL2, TrapEL3) ← (( do
    if ((questionMark == EL0) : Bool)
    then
      (do
        let w__3 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        let IsEL1Regime : Bool := (w__3 == EL1)
        let w__6 ← (( do
          if (IsEL1Regime : Bool)
          then
            (do
              let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL1_Type_EnIB w__4))))
          else
            (do
              let w__5 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_SCTLR_EL2_Type_EnIB w__5)))) ) : SailM (BitVec 1) )
        let Enable := (w__6 : (BitVec 1))
        let w__13 ← (( do
          if ((← do
               if ((← do
                    (EL2Enabled ())) : Bool)
               then
                 (do
                   let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_API w__8) == 0#1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              if ((← do
                   let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                   (pure ((((_get_HCR_EL2_Type_TGE w__10) == 0#1) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_E2H w__11) == 0#1) : Bool)))))
          else (pure false) ) : SailM Bool )
        let TrapEL2 := (w__13 : Bool)
        let w__15 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_API w__14) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let TrapEL3 := (w__15 : Bool)
        (pure ((Enable, TrapEL2, TrapEL3))))
    else
      (do
        if ((questionMark == EL1) : Bool)
        then
          (do
            let w__16 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let Enable := ((_get_SCTLR_EL1_Type_EnIB w__16) : (BitVec 1))
            let w__19 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_API w__18) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL2 := (w__19 : Bool)
            let w__21 ← (( do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  let w__20 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCR_EL3_Type_API w__20) == 0#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let TrapEL3 := (w__21 : Bool)
            (pure ((Enable, TrapEL2, TrapEL3))))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__22 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                let Enable := ((_get_SCTLR_EL2_Type_EnIB w__22) : (BitVec 1))
                let TrapEL2 : Bool := false
                let w__24 ← (( do
                  if (((HaveEL EL3) : Bool) : Bool)
                  then
                    (do
                      let w__23 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                      (pure ((((_get_SCR_EL3_Type_API w__23) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let TrapEL3 := (w__24 : Bool)
                (pure ((Enable, TrapEL2, TrapEL3))))
            else
              (do
                if ((questionMark == EL3) : Bool)
                then
                  (do
                    let w__25 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
                    let Enable := ((_get_SCTLR_EL3_Type_EnIB w__25) : (BitVec 1))
                    let TrapEL2 : Bool := false
                    let TrapEL3 : Bool := false
                    (pure ((Enable, TrapEL2, TrapEL3))))
                else (pure ((Enable, TrapEL2, TrapEL3)))))) ) : SailM ((BitVec 1) × Bool × Bool) )
  if ((Enable == 0#1) : Bool)
  then (pure (x))
  else
    (do
      let w__27 ← (( do
        if ((TrapEL3 : Bool) : Bool)
        then
          (do
            (EL3SDDUndefPriority ()))
        else (pure false) ) : SailM Bool )
      if (w__27 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if (TrapEL2 : Bool)
          then
            (do
              (TrapPACUse EL2)
              (undefined_bitvector_at (← occLabel 1332) 64))
          else
            (do
              if (TrapEL3 : Bool)
              then
                (do
                  let w__30 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
                  if (w__30 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (TrapPACUse EL3)
                      (undefined_bitvector_at (← occLabel 1331) 64)))
              else
                (do
                  (Auth x y APIBKey_EL1 false 1#1 is_combined)))))


end ArmFull.Functions
