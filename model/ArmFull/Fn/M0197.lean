module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0188 set_option backward.proofsInPublic true @[expose] public section

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

def AArch64_RouteToSErrorOffset (target_el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let ease_bit ← (( do (undefined_bitvector_at (← occLabel 865) 1) ) : SailM (BitVec 1) )
      let questionMark := target_el
      let ease_bit ← (( do
        if ((questionMark == EL3) : Bool)
        then
          (do
            let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
            let ease_bit := ((_get_SCR_EL3_Type_EASE w__1) : (BitVec 1))
            (pure (ease_bit)))
        else
          (do
            if ((questionMark == EL2) : Bool)
            then
              (do
                let w__4 ← (( do
                  if ((← do
                       (HaveDoubleFault2Ext ())) : Bool)
                  then
                    (do
                      (IsSCTLR2EL2Enabled ()))
                  else (pure false) ) : SailM Bool )
                if (w__4 : Bool)
                then
                  (do
                    let w__5 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
                    let ease_bit := ((_get_SCTLR2_EL2_Type_EASE w__5) : (BitVec 1))
                    (pure (ease_bit)))
                else (pure (0#1)))
            else
              (do
                if ((questionMark == EL1) : Bool)
                then
                  (do
                    let w__8 ← (( do
                      if ((← do
                           (HaveDoubleFault2Ext ())) : Bool)
                      then
                        (do
                          (IsSCTLR2EL1Enabled ()))
                      else (pure false) ) : SailM Bool )
                    if (w__8 : Bool)
                    then
                      (do
                        let w__9 ← (( do readReg SCTLR2_EL1 ) : SailM (BitVec 64) )
                        let ease_bit := ((_get_SCTLR2_EL1_Type_EASE w__9) : (BitVec 1))
                        (pure (ease_bit)))
                    else (pure (0#1)))
                else (pure (ease_bit)))) ) : SailM (BitVec 1) )
      (pure ((ease_bit == 1#1))))


def AArch64_SyncExternalAbortTarget (fault : FaultRecord) : SailM (BitVec 2) := do
  let route_to_el3 ← (( do (undefined_bool_at (← occLabel 866) ()) ) : SailM Bool )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let route_to_el3 ← (( do
    if ((w__0.EL != EL3) : Bool)
    then
      (do
        if ((← do
             (HaveEL EL3)) : Bool)
        then
          (do
            let w__2 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
            (pure (((w__2 == 1#1) : Bool))))
        else (pure false))
    else (pure (false)) ) : SailM Bool )
  let w__4 ← (( do (HaveRASExt ()) ) : SailM Bool )
  let tea_bit ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((_get_HCR_EL2_Type_TEA w__5))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let route_to_el2 ← (( do (undefined_bool_at (← occLabel 867) ()) ) : SailM Bool )
  let w__9 ← (( do
    if ((← do
         if (((! route_to_el3) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__8.EL == EL1) : Bool))))
    else (pure false) ) : SailM Bool )
  let route_to_el2 ← (( do
    if (w__9 : Bool)
    then
      (do
        if ((((tea_bit == 1#1) || (BEq.beq fault.access.acctype AccessType_NV2)) : Bool) : Bool)
        then (pure true)
        else
          (do
            (IsSecondStage fault)))
    else
      (do
        let w__15 ← (( do
          if ((← do
               if (((! route_to_el3) : Bool) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__14.EL == EL0) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__15 : Bool)
        then
          (do
            if ((← do
                 let w__16 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__16) : Bool)))) : Bool)
            then
              (do
                if ((← do
                     (pure ((← do
                           let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_HCR_EL2_Type_TGE w__17) == 1#1) : Bool)))) || ((tea_bit == 1#1) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    (IsSecondStage fault)))
            else (pure false))
        else (pure (false))) ) : SailM Bool )
  let route_masked_to_el3 ← (( do (undefined_bool_at (← occLabel 868) ()) ) : SailM Bool )
  let route_masked_to_el2 ← (( do (undefined_bool_at (← occLabel 869) ()) ) : SailM Bool )
  let w__22 ← (( do (HaveDoubleFault2Ext ()) ) : SailM Bool )
  let (route_masked_to_el2, route_masked_to_el3) ← (( do
    if (w__22 : Bool)
    then
      (do
        let w__32 ← (( do
          if ((← do
               if ((← do
                    if ((← do
                         (pure ((← do
                               (EL2Enabled ())) && ((! route_to_el3) : Bool)))) : Bool)
                    then
                      (do
                        if ((← do
                             let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__25.EL == EL1) : Bool)))) : Bool)
                        then
                          (do
                            let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__26.A == 1#1) : Bool))))
                        else (pure false))
                    else (pure false)) : Bool)
               then
                 (do
                   (IsHCRXEL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__31 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCRX_EL2_Type_TMEA w__31) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let route_masked_to_el2 := (w__32 : Bool)
        let w__42 ← (( do
          if ((← do
               if ((← do
                    (pure ((← do
                          (HaveEL EL3)) && ((! (route_to_el2 || route_masked_to_el2)) : Bool)))) : Bool)
               then
                 (do
                   if ((← do
                        if ((← do
                             let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__35.EL == EL2) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__36.EL == EL1) : Bool))))) : Bool)
                   then
                     (do
                       let w__38 ← (( do readReg PSTATE ) : SailM ProcState )
                       (pure (((w__38.A == 1#1) : Bool))))
                   else (pure false))
               else (pure false)) : Bool)
          then
            (do
              let w__41 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_TMEA w__41) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let route_masked_to_el3 := (w__42 : Bool)
        (pure ((route_masked_to_el2, route_masked_to_el3))))
    else
      (let route_masked_to_el2 : Bool := false
      let route_masked_to_el3 : Bool := false
      (pure ((route_masked_to_el2, route_masked_to_el3)))) ) : SailM (Bool × Bool) )
  let w__43 ← (( do readReg PSTATE ) : SailM ProcState )
  let take_in_el3 : Bool := (w__43.EL == EL3)
  let take_in_el2_0 ← (( do
    (pure ((← do
          if ((← do
               let w__44 ← (( do readReg PSTATE ) : SailM ProcState )
               (pure (((w__44.EL == EL2) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              (IsInHost ()))) && ((! (route_to_el3 || route_masked_to_el3)) : Bool))) ) : SailM Bool
    )
  let take_in_el1_0 ← (( do
    (pure ((← do
          (pure ((← do
                if ((← do
                     let w__47 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((w__47.EL == EL1) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    if ((← do
                         let w__48 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__48.EL == EL0) : Bool)))) : Bool)
                    then
                      (do
                        let w__49 ← (( do (IsInHost ()) ) : SailM Bool )
                        (pure (((! w__49) : Bool))))
                    else (pure false))) && ((! (route_to_el2 || route_masked_to_el2)) : Bool)))) && ((! (route_to_el3 || route_masked_to_el3)) : Bool)))
    ) : SailM Bool )
  let target_el ← (( do (undefined_bitvector_at (← occLabel 870) 2) ) : SailM (BitVec 2) )
  if (((take_in_el3 || route_to_el3) || route_masked_to_el3) : Bool)
  then (pure (EL3))
  else
    (do
      if (((take_in_el2_0 || route_to_el2) || route_masked_to_el2) : Bool)
      then (pure (EL2))
      else
        (do
          if (take_in_el1_0 : Bool)
          then (pure (EL1))
          else
            (do
              ArmFull.assert false "sail-inputs/03-v8_base.sail:14983.20-14983.21"
              throw Error.Exit)))


def IsFullA64Enabled (_ : Unit) : SailM Bool := SailME.run do
  let w__0 ← (( do (HaveSMEFullA64 ()) ) : SailME Bool Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let w__5 ← (( do
        if ((← do
             if ((← do
                  let w__1 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                  (pure (((w__1.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__2 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                 (pure (((w__2.EL == EL1) : Bool))))) : Bool)
        then
          (do
            let w__4 ← (( do (IsInHost ()) ) : SailME Bool Bool )
            (pure (((! w__4) : Bool))))
        else (pure false) ) : SailME Bool Bool )
      if (w__5 : Bool)
      then
        (do
          let w__6 ← (( do readReg SMCR_EL1 ) : SailME Bool (BitVec 64) )
          if (((_get_SMCR_EL1_Type_FA64 w__6) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      let w__13 ← (( do
        if ((← do
             if ((← do
                  let w__7 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                  (pure (((w__7.EL == EL0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 if ((← do
                      let w__8 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                      (pure (((w__8.EL == EL1) : Bool)))) : Bool)
                 then (pure true)
                 else
                   (do
                     let w__9 ← (( do readReg PSTATE ) : SailME Bool ProcState )
                     (pure (((w__9.EL == EL2) : Bool)))))) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailME Bool Bool )
      if (w__13 : Bool)
      then
        (do
          let w__14 ← (( do readReg SMCR_EL2 ) : SailME Bool (BitVec 64) )
          if (((_get_SMCR_EL2_Type_FA64 w__14) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      let w__15 ← (( do (HaveEL EL3) ) : SailME Bool Bool )
      if (w__15 : Bool)
      then
        (do
          let w__16 ← (( do readReg SMCR_EL3 ) : SailME Bool (BitVec 64) )
          if (((_get_SMCR_EL3_Type_FA64 w__16) == 0#1) : Bool)
          then
            (do
              SailME.throw (false : Bool))
          else (pure (())))
      else (pure (()))
      (pure (true)))


def CNTP_CTL_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_CNTP_CTL_Type (← occLabel 1159) ()) ) : SailM CNTP_CTL_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg CNTP_CTL_S)
  else
    (do
      (CNTP_CTL_NS_read ()))


def CNTP_CTL_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : CNTP_CTL_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg CNTP_CTL_S r)
  else
    (do
      (CNTP_CTL_NS_write r))


def CNTP_CVAL_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do (undefined_CNTP_CVAL_Type (← occLabel 1162) ()) ) : SailM CNTP_CVAL_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg CNTP_CVAL_S)
  else
    (do
      (CNTP_CVAL_NS_read ()))


def AArch64_CheckTimerConditions (_ : Unit) : SailM Unit := do
  let status ← (( do (undefined_bool_at (.site 1174) ()) ) : SailM Bool )
  let offset ← (( do (undefined_bitvector_at (.site 1175) 64) ) : SailM (BitVec 64) )
  let imask ← (( do (undefined_bitvector_at (.site 1176) 1) ) : SailM (BitVec 1) )
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let ecv : Bool := false
  let w__0 ← (( do (HaveECVExt ()) ) : SailM Bool )
  let ecv ← (( do
    if (w__0 : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__1 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_CNTHCTL_EL2_Type_ECV w__1) == 1#1) : Bool)))) : Bool)
             then
               (do
                 let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                 (pure ((((_get_SCR_EL3_Type_ECVEn w__2) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false))
    else (pure (ecv)) ) : SailM Bool )
  let offset ← (( do
    if (ecv : Bool)
    then
      (do
        readReg CNTPOFF_EL2)
    else
      (let offset : (BitVec 64) := (Zeros (n := 64))
      (pure (offset))) ) : SailM (BitVec 64) )
  let w__7 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  let (imask, status) ← (( do
    if (((_get_CNTP_CTL_EL0_Type_ENABLE w__7) == 1#1) : Bool)
    then
      (do
        let w__8 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
        let imask := ((_get_CNTP_CTL_EL0_Type_IMASK w__8) : (BitVec 1))
        let w__12 ← (( do
          if ((← do
               (pure ((← do
                     (HaveRME ())) && (((BEq.beq ss SS_Root) || (BEq.beq ss SS_Realm)) : Bool)))) : Bool)
          then
            (do
              let w__11 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTHCTL_EL2_Type_CNTPMASK w__11) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let imask : (BitVec 1) :=
          if (w__12 : Bool)
          then 1#1
          else imask
        let w__13 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
        let w__14 ← (( do (IsTimerConditionMet offset w__13 imask InterruptID_CNTP) ) : SailM Bool
          )
        let status := (w__14 : Bool)
        let w__15 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
        writeReg CNTP_CTL_EL0 (Sail.BitVec.updateSubrange w__15 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure ((imask, status))))
    else (pure ((imask, status))) ) : SailM ((BitVec 1) × Bool) )
  let w__22 ← (( do
    if ((← do
         if ((← do
              (HaveEL EL3)) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  (HaveEL EL2)) : Bool)
             then
               (do
                 let w__18 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                 (pure (((! w__18) : Bool))))
             else (pure false))) : Bool)
    then
      (do
        let w__21 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHP_CTL_EL2_Type_ENABLE w__21) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__22 : Bool)
    then
      (do
        let w__23 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__24 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        let w__25 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__23 (_get_CNTHP_CTL_EL2_Type_IMASK w__24)
            InterruptID_CNTHP) ) : SailM Bool )
        let status := (w__25 : Bool)
        let w__26 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange w__26 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__31 ← (( do
    if ((← do
         if ((← do
              (HaveEL EL2)) : Bool)
         then
           (do
             (HaveSecureEL2Ext ()))
         else (pure false)) : Bool)
    then
      (do
        let w__30 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHPS_CTL_EL2_Type_ENABLE w__30) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__31 : Bool)
    then
      (do
        let w__32 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__33 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        let w__34 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__32 (_get_CNTHPS_CTL_EL2_Type_IMASK w__33)
            InterruptID_CNTHPS) ) : SailM Bool )
        let status := (w__34 : Bool)
        let w__35 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange w__35 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__36 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
  let status ← (( do
    if (((_get_CNTPS_CTL_EL1_Type_ENABLE w__36) == 1#1) : Bool)
    then
      (do
        let w__37 ← (( do readReg CNTPS_CVAL_EL1 ) : SailM (BitVec 64) )
        let w__38 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
        let w__39 ← (( do
          (IsTimerConditionMet offset w__37 (_get_CNTPS_CTL_EL1_Type_IMASK w__38) InterruptID_CNTPS)
          ) : SailM Bool )
        let status := (w__39 : Bool)
        let w__40 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
        writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange w__40 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__41 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  let status ← (( do
    if (((_get_CNTV_CTL_EL0_Type_ENABLE w__41) == 1#1) : Bool)
    then
      (do
        let w__42 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
        let imask : (BitVec 1) := ((_get_CNTV_CTL_EL0_Type_IMASK w__42) : (BitVec 1))
        let w__46 ← (( do
          if ((← do
               (pure ((← do
                     (HaveRME ())) && (((BEq.beq ss SS_Root) || (BEq.beq ss SS_Realm)) : Bool)))) : Bool)
          then
            (do
              let w__45 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_CNTHCTL_EL2_Type_CNTVMASK w__45) == 1#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let imask : (BitVec 1) :=
          if (w__46 : Bool)
          then 1#1
          else imask
        let w__47 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
        let w__48 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
        let w__49 ← (( do (IsTimerConditionMet w__47 w__48 imask InterruptID_CNTV) ) : SailM Bool
          )
        let status := (w__49 : Bool)
        let w__50 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
        writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__50 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__57 ← (( do
    if ((← do
         if ((← do
              (HaveVirtHostExt ())) : Bool)
         then
           (do
             if ((← do
                  (HaveEL EL3)) : Bool)
             then (pure true)
             else
               (do
                 let w__53 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                 (pure (((! w__53) : Bool)))))
         else (pure false)) : Bool)
    then
      (do
        let w__56 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHV_CTL_EL2_Type_ENABLE w__56) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let status ← (( do
    if (w__57 : Bool)
    then
      (do
        let w__58 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
        let w__59 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        let w__60 ← (( do
          (IsTimerConditionMet (Zeros (n := 64)) w__58 (_get_CNTHV_CTL_EL2_Type_IMASK w__59)
            InterruptID_CNTHV) ) : SailM Bool )
        let status := (w__60 : Bool)
        let w__61 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
        writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange w__61 2 2
          (if (status : Bool)
          then 1#1
          else 0#1))
        (pure (status)))
    else (pure (status)) ) : SailM Bool )
  let w__66 ← (( do
    if ((← do
         if ((← do
              (HaveSecureEL2Ext ())) : Bool)
         then
           (do
             (HaveVirtHostExt ()))
         else (pure false)) : Bool)
    then
      (do
        let w__65 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_CNTHVS_CTL_EL2_Type_ENABLE w__65) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__66 : Bool)
  then
    (do
      let w__67 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
      let w__68 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
      let status ← (( do
        (IsTimerConditionMet (Zeros (n := 64)) w__67 (_get_CNTHVS_CTL_EL2_Type_IMASK w__68)
          InterruptID_CNTHVS) ) : SailM Bool )
      let w__69 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
      writeReg CNTHVS_CTL_EL2 (Sail.BitVec.updateSubrange w__69 2 2
        (if (status : Bool)
        then 1#1
        else 0#1)))
  else (pure (()))


end ArmFull.Functions
