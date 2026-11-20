module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0153
public import ArmFull.Fn.M0154
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0174
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0189
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0197
public import ArmFull.Fn.M0198 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_route_to_monitor : Bool -/
def AArch32_ReportPrefetchAbort (route_to_monitor : Bool) (fault : FaultRecord) (vaddress : (BitVec 32)) : SailM Unit := do
  let long_format : Bool := false
  let w__1 ← (( do
    if ((route_to_monitor : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((bne w__0 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  let long_format ← (( do
    if (w__1 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__2 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
                  (pure ((((_get_TTBCR_Type_EAE w__2) == 1#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__3.EL == EL2) : Bool))))) : Bool)
        then (pure true)
        else
          (do
            let w__5 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_TTBCR_Type_EAE w__5) == 1#1) : Bool)))))
    else
      (do
        let w__7 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
        let long_format := (((_get_TTBCR_Type_EAE w__7) == 1#1) : Bool)
        (pure (long_format))) ) : SailM Bool )
  let fsr ← (( do (AArch32_CommonFaultStatus fault long_format) ) : SailM (BitVec 32) )
  if (route_to_monitor : Bool)
  then
    (do
      writeReg IFSR_S (Mk_IFSR_Type fsr)
      (IFAR_S_write vaddress))
  else
    (do
      (IFSR_write (Mk_IFSR_Type fsr))
      (IFAR_write vaddress))


def AArch64_AbortSyndrome (exceptype : Exception) (fault : FaultRecord) (vaddress : (BitVec 64)) (target_el : (BitVec 2)) : SailM ExceptionRecord := do
  let except ← (( do (ExceptionSyndrome exceptype) ) : SailM ExceptionRecord )
  let d_side : Bool :=
    ((BEq.beq exceptype Exception_DataAbort) || ((BEq.beq exceptype Exception_NV2DataAbort) || ((BEq.beq
            exceptype Exception_Watchpoint) || (BEq.beq exceptype Exception_NV2Watchpoint))))
  let w__7 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (HavePFAR ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do (IsExternalSyncAbort__1 fault) ) : SailM Bool )
             (pure (((! w__1) : Bool))))) : Bool)
    then (pure true)
    else
      (do
        (pure ((← do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_VM w__4) == 1#1) : Bool))))
              else (pure false)) && ((target_el == EL1) : Bool)))) ) : SailM Bool )
  let except ← (( do
    if (w__7 : Bool)
    then
      (let except : ExceptionRecord := { except with pavalid := false }
      (pure (except)))
    else
      (do
        let w__8 ← (( do (__IMPDEF_boolean "PFAR_ELx is valid") ) : SailM Bool )
        let except := ({ except with pavalid := w__8 } : ExceptionRecord)
        (pure (except))) ) : SailM ExceptionRecord )
  let w__9 ← (( do (AArch64_FaultSyndrome d_side fault except.pavalid) ) : SailM
    ((BitVec 25) × (BitVec 24)) )
  let (tup__0, tup__1) := (w__9 : ((BitVec 25) × (BitVec 24)))
  let except : ExceptionRecord := { except with syndrome := tup__0 }
  let except : ExceptionRecord := { except with syndrome2 := tup__1 }
  let except ← (( do
    if ((BEq.beq fault.statuscode Fault_TagCheck) : Bool)
    then
      (do
        let w__10 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
        if (w__10 : Bool)
        then
          (let except : ExceptionRecord :=
            { except with vaddress := (Sail.BitVec.zeroExtend vaddress 64) }
          (pure (except)))
        else
          (do
            let w__11 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
            let except :=
              ({ except with vaddress := (w__11 +++ (Sail.BitVec.extractLsb vaddress 59 0)) } : ExceptionRecord)
            (pure (except))))
    else
      (let except : ExceptionRecord :=
        { except with vaddress := (Sail.BitVec.zeroExtend vaddress 64) }
      (pure (except))) ) : SailM ExceptionRecord )
  let w__12 ← (( do (IPAValid fault) ) : SailM Bool )
  let except : ExceptionRecord :=
    if (w__12 : Bool)
    then
      (let except : ExceptionRecord := { except with ipavalid := true }
      let except : ExceptionRecord :=
        { except with NS := if ((BEq.beq fault.ipaddress.paspace PAS_NonSecure) : Bool)
          then 1#1
          else 0#1 }
      { except with ipaddress := fault.ipaddress.address })
    else { except with ipavalid := false }
  (pure (except))


def IsMerging (fpcr : (BitVec 64)) : SailM Bool := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              (HaveSME ())) : Bool)
         then
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.SM == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do (IsFullA64Enabled ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  let nep : (BitVec 1) :=
    if (w__4 : Bool)
    then 0#1
    else (_get_FPCRType_NEP fpcr)
  (pure ((← do
        if ((← do
             (HaveAltFP ())) : Bool)
        then
          (do
            let w__6 ← (( do (UsingAArch32 ()) ) : SailM Bool )
            (pure (((! w__6) : Bool))))
        else (pure false)) && ((nep == 1#1) : Bool)))


def AArch32_CheckTimerConditions (_ : Unit) : SailM Unit := do
  let status ← (( do (undefined_bool_at (.site 1165) ()) ) : SailM Bool )
  let offset : (BitVec 64) := (Zeros (n := 64))
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  ArmFull.assert (! w__0) "sail-inputs/03-v8_base.sail:18204.34-18204.35"
  let w__1 ← (( do (HaveEL EL3) ) : SailM Bool )
  let status ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
        let status ← (( do
          if (((_get_CNTP_CTL_Type_ENABLE w__2) == 1#1) : Bool)
          then
            (do
              let w__3 ← (( do readReg CNTP_CVAL_S ) : SailM (BitVec 64) )
              let w__4 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
              let w__5 ← (( do
                (IsTimerConditionMet offset w__3 (_get_CNTP_CTL_Type_IMASK w__4) InterruptID_CNTPS)
                ) : SailM Bool )
              let status := (w__5 : Bool)
              let w__6 ← (( do readReg CNTP_CTL_S ) : SailM (BitVec 32) )
              writeReg CNTP_CTL_S (Sail.BitVec.updateSubrange w__6 2 2
                (if (status : Bool)
                then 1#1
                else 0#1))
              (pure (status)))
          else (pure (status)) ) : SailM Bool )
        let w__7 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
        if (((_get_CNTP_CTL_Type_ENABLE w__7) == 1#1) : Bool)
        then
          (do
            let w__8 ← (( do (CNTP_CVAL_NS_read ()) ) : SailM (BitVec 64) )
            let w__9 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
            let w__10 ← (( do
              (IsTimerConditionMet offset w__8 (_get_CNTP_CTL_Type_IMASK w__9) InterruptID_CNTP) ) :
              SailM Bool )
            let status := (w__10 : Bool)
            let w__11 ← (( do (CNTP_CTL_NS_read ()) ) : SailM (BitVec 32) )
            (CNTP_CTL_NS_write
              (_update_CNTP_CTL_Type_ISTATUS w__11
                (if (status : Bool)
                then 1#1
                else 0#1)))
            (pure (status)))
        else (pure (status)))
    else
      (do
        let w__12 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
        if (((_get_CNTP_CTL_Type_ENABLE w__12) == 1#1) : Bool)
        then
          (do
            let w__13 ← (( do (CNTP_CVAL_read ()) ) : SailM (BitVec 64) )
            let w__14 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
            let w__15 ← (( do
              (IsTimerConditionMet offset w__13 (_get_CNTP_CTL_Type_IMASK w__14) InterruptID_CNTP) )
              : SailM Bool )
            let status := (w__15 : Bool)
            let w__16 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
            (CNTP_CTL_write
              (_update_CNTP_CTL_Type_ISTATUS w__16
                (if (status : Bool)
                then 1#1
                else 0#1)))
            (pure (status)))
        else (pure (status))) ) : SailM Bool )
  let w__19 ← (( do
    if ((← do
         (HaveEL EL2)) : Bool)
    then
      (do
        let w__18 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_CNTHP_CTL_Type_ENABLE w__18) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__19 : Bool)
    then
      (do
        let w__20 ← (( do (CNTHP_CVAL_read ()) ) : SailM (BitVec 64) )
        let w__21 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
        let w__22 ← (( do
          (IsTimerConditionMet offset w__20 (_get_CNTHP_CTL_Type_IMASK w__21) InterruptID_CNTHP) ) :
          SailM Bool )
        let status := (w__22 : Bool)
        let w__23 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
        (CNTHP_CTL_write
          (_update_CNTHP_CTL_Type_ISTATUS w__23
            (if (status : Bool)
            then 1#1
            else 0#1)))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__24 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  if (((_get_CNTV_CTL_EL0_Type_ENABLE w__24) == 1#1) : Bool)
  then
    (do
      let w__25 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
      let w__26 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
      let w__27 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
      let status ← (( do
        (IsTimerConditionMet w__25 w__26 (_get_CNTV_CTL_EL0_Type_IMASK w__27) InterruptID_CNTV) ) :
        SailM Bool )
      let w__28 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
      writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__28 2 2
        (if (status : Bool)
        then 1#1
        else 0#1)))
  else (pure (()))


def PtrHasUpperAndLowerAddRanges (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let regime ← (( do (TranslationRegime w__0.EL) ) : SailM Regime )
  (pure ((HasUnprivileged regime)))


def AArch64_AllocationTagAccessIsEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
          (pure ((((_get_SCR_EL3_Type_ATA w__0) == 0#1) : Bool)))) && (((el == EL0) || ((el == EL1) || (el == EL2))) : Bool)))
    ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (false))
  else
    (do
      let w__8 ← (( do
        if ((← do
             if ((← do
                  (pure ((← do
                        let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_ATA w__2) == 0#1) : Bool)))) && (((el == EL0) || (el == EL1)) : Bool)))) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure (((((_get_HCR_EL2_Type_E2H w__6) +++ (_get_HCR_EL2_Type_TGE w__7)) != 0b11#2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then (pure (false))
      else
        (do
          let regime ← (( do (TranslationRegime el) ) : SailM Regime )
          match regime with
          | .Regime_EL3 =>
            (do
              let w__9 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
              (pure (((_get_SCTLR_EL3_Type_ATA w__9) == 1#1))))
          | .Regime_EL2 =>
            (do
              let w__10 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
              (pure (((_get_SCTLR_EL2_Type_ATA w__10) == 1#1))))
          | .Regime_EL20 =>
            (do
              if ((el == EL0) : Bool)
              then
                (do
                  let w__11 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                  (pure (((_get_SCTLR_EL2_Type_ATA0 w__11) == 1#1))))
              else
                (do
                  let w__12 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                  (pure (((_get_SCTLR_EL2_Type_ATA w__12) == 1#1)))))
          | .Regime_EL10 =>
            (do
              if ((el == EL0) : Bool)
              then
                (do
                  let w__14 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
                  (pure (((_get_SCTLR_EL1_Type_ATA0 w__14) == 1#1))))
              else
                (do
                  let w__15 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
                  (pure (((_get_SCTLR_EL1_Type_ATA w__15) == 1#1)))))
          | _ =>
            (do
              (Unreachable ())
              (undefined_bool_at (← occLabel 1347) ()))))


def AArch64_EffectiveTCF (el : (BitVec 2)) : SailM (BitVec 2) := do
  let tcf ← (( do (undefined_bitvector_at (← occLabel 1358) 2) ) : SailM (BitVec 2) )
  let regime ← (( do (TranslationRegime el) ) : SailM Regime )
  let tcf ← (( do
    match regime with
    | .Regime_EL3 =>
      (do
        let w__0 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
        let tcf := ((_get_SCTLR_EL3_Type_TCF w__0) : (BitVec 2))
        (pure (tcf)))
    | .Regime_EL2 =>
      (do
        let w__1 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
        let tcf := ((_get_SCTLR_EL2_Type_TCF w__1) : (BitVec 2))
        (pure (tcf)))
    | .Regime_EL20 =>
      (do
        if ((el == EL0) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL2_Type_TCF0 w__2))))
        else
          (do
            let w__3 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL2_Type_TCF w__3)))))
    | .Regime_EL10 =>
      (do
        if ((el == EL0) : Bool)
        then
          (do
            let w__5 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL1_Type_TCF0 w__5))))
        else
          (do
            let w__6 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            (pure ((_get_SCTLR_EL1_Type_TCF w__6)))))
    | _ =>
      (do
        (Unreachable ())
        (pure (tcf))) ) : SailM (BitVec 2) )
  if ((tcf == 0b11#2) : Bool)
  then
    (do
      let w__8 ← (( do (HaveMTEAsymFaultExt ()) ) : SailM Bool )
      if ((! w__8) : Bool)
      then
        (do
          let (_, __tup_1) ← (( do (ConstrainUnpredictableBits Unpredictable_RESTCF 2) ) : SailM
            (Constraint × (BitVec 2)) )
          (pure (__tup_1)))
      else (pure (tcf)))
  else (pure (tcf))


def HaltOnBreakpointOrWatchpoint (_ : Unit) : SailM Bool := do
  if ((← do
       if ((← do
            (HaltingAllowed ())) : Bool)
       then
         (do
           let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
           (pure ((((_get_EDSCR_Type_HDE w__1) == 1#1) : Bool))))
       else (pure false)) : Bool)
  then
    (do
      let w__3 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
      (pure ((((_get_OSLSR_EL1_Type_OSLK w__3) == 0#1) : Bool))))
  else (pure false)


def AArch64_S1ComputePermissions (regime : Regime) (walkstate : TTWState) (walkparams : S1TTWParams) (accdesc : AccessDescriptor) : SailM S1AccessControls := do
  let s1overlay_perms ← (( do (undefined_S1AccessControls (← occLabel 1454) ()) ) : SailM
    S1AccessControls )
  let permissions : Permissions := walkstate.permissions
  let s1perms ← (( do (undefined_S1AccessControls (← occLabel 1455) ()) ) : SailM
    S1AccessControls )
  let s1perms ← (( do
    if ((walkparams.pie == 1#1) : Bool)
    then
      (do
        (AArch64_S1IndirectBasePermissions regime walkstate walkparams accdesc))
    else
      (do
        (AArch64_S1DirectBasePermissions regime walkstate walkparams accdesc)) ) : SailM
    S1AccessControls )
  let w__3 ← (( do
    if (((accdesc.el == EL0) : Bool) : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_S1E0POEnabled regime walkparams.nv1) ) : SailM Bool )
        (pure (((! w__2) : Bool))))
    else (pure false) ) : SailM Bool )
  let s1perms ← (( do
    if (w__3 : Bool)
    then
      (let s1perms : S1AccessControls := { s1perms with overlay := false }
      (pure (s1perms)))
    else
      (do
        let w__5 ← (( do
          if (((accdesc.el != EL0) : Bool) : Bool)
          then
            (do
              let w__4 ← (( do (AArch64_S1POEnabled regime) ) : SailM Bool )
              (pure (((! w__4) : Bool))))
          else (pure false) ) : SailM Bool )
        let s1perms : S1AccessControls :=
          if (w__5 : Bool)
          then { s1perms with overlay := false }
          else s1perms
        (pure (s1perms))) ) : SailM S1AccessControls )
  let s1perms ← (( do
    if (s1perms.overlay : Bool)
    then
      (do
        let s1overlay_perms ← (( do (AArch64_S1OverlayPermissions regime walkstate accdesc) ) :
          SailM S1AccessControls )
        let s1perms : S1AccessControls := { s1perms with or := s1overlay_perms.or }
        let s1perms : S1AccessControls := { s1perms with ow := s1overlay_perms.ow }
        let s1perms : S1AccessControls := { s1perms with ox := s1overlay_perms.ox }
        (pure (s1perms)))
    else (pure (s1perms)) ) : SailM S1AccessControls )
  let s1perms : S1AccessControls :=
    if (((s1perms.overlay && (s1perms.wxn == 1#1)) && (s1perms.ox == 1#1)) : Bool)
    then { s1perms with ow := 0#1 }
    else
      (if ((s1perms.wxn == 1#1) : Bool)
      then { s1perms with x := 0#1 }
      else s1perms)
  (pure (s1perms))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S1ApplyOutputPerms (permissions_in : Permissions) (descriptor : (BitVec k_N)) (regime : Regime) (walkparams : S1TTWParams) : SailM Permissions := do
  let bit_index ← (( do (undefined_int_at (← occLabel 1484) ()) ) : SailM Int )
  let permissions : Permissions := permissions_in
  let pi_index ← (( do (undefined_bitvector_at (← occLabel 1485) 4) ) : SailM (BitVec 4) )
  let permissions ← (( do
    if ((walkparams.pie == 1#1) : Bool)
    then
      (do
        let pi_index ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (118 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25378.39-25378.40"
              let pi_index : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 118 115)
              (pure (pi_index)))
          else
            (do
              ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25381.38-25381.39"
              let pi_index : (BitVec 4) :=
                (((Sail.BitVec.extractLsb descriptor 54 53) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        descriptor 51)]))) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                      descriptor 6)])))
              (pure (pi_index))) ) : SailM (BitVec 4) )
        let bit_index : Int := (4 *i (BitVec.toNat pi_index))
        let permissions : Permissions :=
          { permissions with ppi := (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
              walkparams.pir (Sail.Int.toNatChecked ((bit_index +i 3)))
              (Sail.Int.toNatChecked (bit_index)))) }
        let permissions : Permissions :=
          { permissions with upi := (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
              walkparams.pire0 (Sail.Int.toNatChecked ((bit_index +i 3)))
              (Sail.Int.toNatChecked (bit_index)))) }
        ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25387.33-25387.34"
        let permissions : Permissions :=
          { permissions with ndirty := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 7)])) }
        (pure (permissions)))
    else
      (do
        let w__2 ← (( do
          (pure ((← do
                if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                then
                  (do
                    (EL2Enabled ()))
                else (pure false)) && ((walkparams.nv1 == 1#1) : Bool))) ) : SailM Bool )
        let permissions ← (( do
          if (w__2 : Bool)
          then
            (do
              ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25391.37-25391.38"
              let permissions : Permissions :=
                { permissions with ap := (Sail.BitVec.updateSubrange permissions.ap 2 1
                    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 7)])) +++ 0#1)) }
              ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25393.38-25393.39"
              let permissions : Permissions :=
                { permissions with pxn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                      descriptor 54)])) }
              (pure (permissions)))
          else
            (do
              if ((HasUnprivileged regime) : Bool)
              then
                (do
                  ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25396.37-25396.38"
                  let permissions : Permissions :=
                    { permissions with ap := (Sail.BitVec.updateSubrange permissions.ap 2 1
                        (Sail.BitVec.extractLsb descriptor 7 6)) }
                  ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25398.38-25398.39"
                  let permissions : Permissions :=
                    { permissions with uxn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 54)])) }
                  let permissions : Permissions :=
                    { permissions with pxn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 53)])) }
                  (pure (permissions)))
              else
                (do
                  ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25402.37-25402.38"
                  let permissions : Permissions :=
                    { permissions with ap := (Sail.BitVec.updateSubrange permissions.ap 2 1
                        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 7)])) +++ 1#1)) }
                  ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25404.38-25404.39"
                  let permissions : Permissions :=
                    { permissions with xn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 54)])) }
                  (pure (permissions)))) ) : SailM Permissions )
        ArmFull.assert (51 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25407.34-25407.35"
        let permissions : Permissions :=
          if ((((walkparams.ha == 1#1) && (walkparams.hd == 1#1)) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                     descriptor 51)])) == 1#1)) : Bool)
          then { permissions with ap := (BitVec.update permissions.ap 2 (Bit 0#1)) }
          else permissions
        (pure (permissions))) ) : SailM Permissions )
  let poe ← (( do (AArch64_S1POEnabled regime) ) : SailM Bool )
  let e0poe ← (( do
    if (((HasUnprivileged regime) : Bool) : Bool)
    then
      (do
        (AArch64_S1E0POEnabled regime walkparams.nv1))
    else (pure false) ) : SailM Bool )
  if ((poe || e0poe) : Bool)
  then
    (do
      if ((walkparams.d128 == 1#1) : Bool)
      then
        (do
          ArmFull.assert (124 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25417.39-25417.40"
          let permissions : Permissions :=
            { permissions with po_index := (Sail.BitVec.extractLsb descriptor 124 121) }
          (pure (permissions)))
      else
        (do
          ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25420.38-25420.39"
          let permissions : Permissions :=
            { permissions with po_index := (0#1 +++ (Sail.BitVec.extractLsb descriptor 62 60)) }
          (pure (permissions))))
  else (pure (permissions))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_GetS2TTWParams (ss : SecurityState) (ipaspace : PASpace) (s1aarch64 : Bool) : SailM S2TTWParams := do
  let walkparams ← (( do (undefined_S2TTWParams (← occLabel 1508) ()) ) : SailM S2TTWParams )
  if ((BEq.beq ss SS_NonSecure) : Bool)
  then
    (do
      (AArch64_NSS2TTWParams s1aarch64))
  else
    (do
      let w__2 ← (( do
        (pure ((← do
              (HaveSecureEL2Ext ())) && ((BEq.beq ss SS_Secure) : Bool))) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          (AArch64_SS2TTWParams ipaspace s1aarch64))
      else
        (do
          if ((BEq.beq ss SS_Realm) : Bool)
          then
            (do
              (AArch64_RLS2TTWParams s1aarch64))
          else
            (do
              (Unreachable ())
              (pure (walkparams)))))


end ArmFull.Functions
