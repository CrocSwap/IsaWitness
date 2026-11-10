import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0044
import ArmFull.Fn.M0052
import ArmFull.Fn.M0092
import ArmFull.Fn.M0098
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0184
import ArmFull.Fn.M0185
import ArmFull.Fn.M0254

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

/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1IS_SysOpsWrite128_60f538ade9f32bfe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__2)
  let w__3 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVAALE1IS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVAALE1IS w__4)
  let w__5 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__7 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__9 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TTLBIS == 1#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 (IsFeatureImplemented FEAT_FGT))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            if (((! (HaveEL EL3)) : Bool) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__13 ← (( do readReg SCR_EL3 ) : SailM
                                                  (BitVec 64) )
                                                (pure ((((_get_SCR_EL3_Type_FGTEn w__13) == 1#1) : Bool)))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__18 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                        (pure (((! w__18) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_TLBIVAALE1IS == 1#1) : Bool))) )
                        : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__22 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__23 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__24 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__22 Regime_EL10 w__23 Shareability_ISH TLBILevel_Last
                            TLBI_ExcludeXS (w__24 +++ w__25))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE w__27)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__28 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__29 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__28 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS (w__29 +++ w__30)))
                  else
                    (do
                      let w__31 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__32 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__33 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__31 Regime_EL10 w__32 Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS (w__33 +++ w__34))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__35) +++ (_get_HCR_EL2_Type_TGE w__36)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__37 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__38 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__37 Regime_EL20 VMID_NONE Shareability_ISH
                            TLBILevel_Last TLBI_ExcludeXS (w__38 +++ w__39)))
                      else
                        (do
                          let w__40 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__41 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__42 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__40 Regime_EL10 w__41 Shareability_ISH TLBILevel_Last
                            TLBI_ExcludeXS (w__42 +++ w__43))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1OS_SysOpsWrite128_323a394d866290cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBOS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBOS w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVAALE1OS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVAALE1OS w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else
            (do
              let w__9 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLBOS == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_TLBIVAALE1OS == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (IsFeatureImplemented FEAT_XS)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (IsHCRXEL2Enabled ()))
                              else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          let w__21 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__22 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__23 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__21 Regime_EL10 w__22 Shareability_OSH TLBILevel_Last
                            TLBI_ExcludeXS (w__23 +++ w__24)))
                      else
                        (do
                          let w__25 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__26 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__27 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__25 Regime_EL10 w__26 Shareability_OSH TLBILevel_Last
                            TLBI_AllAttr (w__27 +++ w__28)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__29) +++ (_get_HCR_EL2_Type_TGE w__30)) == 0b11#2) : Bool)
              then
                (do
                  let w__31 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__32 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__33 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VAA w__31 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr (w__32 +++ w__33)))
              else
                (do
                  let w__34 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__35 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__36 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VAA w__34 Regime_EL10 w__35 Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr (w__36 +++ w__37))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__38) +++ (_get_HCR_EL2_Type_TGE w__39)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__40 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__41 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__40 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last
                        TLBI_AllAttr (w__41 +++ w__42)))
                  else
                    (do
                      let w__43 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__44 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__45 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__46 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__43 Regime_EL10 w__44 Shareability_OSH TLBILevel_Last
                        TLBI_AllAttr (w__45 +++ w__46))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1OS_SysOpsWrite128_4c241ac6279d85ce (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBOS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBOS w__2)
  let w__3 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVAALE1OS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVAALE1OS w__4)
  let w__5 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__7 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__9 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TTLBOS == 1#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             if ((← do
                                                  (EL2Enabled ())) : Bool)
                                             then
                                               (do
                                                 (IsFeatureImplemented FEAT_FGT))
                                             else (pure false)) : Bool)
                                        then
                                          (do
                                            if (((! (HaveEL EL3)) : Bool) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__13 ← (( do readReg SCR_EL3 ) : SailM
                                                  (BitVec 64) )
                                                (pure ((((_get_SCR_EL3_Type_FGTEn w__13) == 1#1) : Bool)))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__18 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                        (pure (((! w__18) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_TLBIVAALE1OS == 1#1) : Bool))) )
                        : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__22 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__23 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__24 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__22 Regime_EL10 w__23 Shareability_OSH TLBILevel_Last
                            TLBI_ExcludeXS (w__24 +++ w__25))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE w__27)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__28 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__29 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__28 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS (w__29 +++ w__30)))
                  else
                    (do
                      let w__31 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__32 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__33 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__31 Regime_EL10 w__32 Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS (w__33 +++ w__34))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__35 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__35) +++ (_get_HCR_EL2_Type_TGE w__36)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__37 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__38 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__37 Regime_EL20 VMID_NONE Shareability_OSH
                            TLBILevel_Last TLBI_ExcludeXS (w__38 +++ w__39)))
                      else
                        (do
                          let w__40 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__41 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__42 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__40 Regime_EL10 w__41 Shareability_OSH TLBILevel_Last
                            TLBI_ExcludeXS (w__42 +++ w__43))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1_SysOpsWrite128_9ce40ceffd0fb221 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVAALE1 : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVAALE1 w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FB : (BitVec 1) := (_get_HCR_EL2_Type_FB w__4)
  let w__5 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__5) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__7 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             (IsFeatureImplemented FEAT_FGT))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        if (((! (HaveEL EL3)) : Bool) : Bool)
                                        then (pure true)
                                        else
                                          (do
                                            let w__11 ← (( do readReg SCR_EL3 ) : SailM
                                              (BitVec 64) )
                                            (pure ((((_get_SCR_EL3_Type_FGTEn w__11) == 1#1) : Bool)))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_HCX))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__16 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                    (pure (((! w__16) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                          else (pure false)) && ((__HFGITR_EL2_TLBIVAALE1 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          let w__22 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__23 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__24 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__22 Regime_EL10 w__23 Shareability_ISH TLBILevel_Last
                            TLBI_ExcludeXS (w__24 +++ w__25)))
                      else
                        (do
                          let w__26 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__27 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__28 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__29 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__26 Regime_EL10 w__27 Shareability_NSH TLBILevel_Last
                            TLBI_ExcludeXS (w__28 +++ w__29))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__30) +++ (_get_HCR_EL2_Type_TGE w__31)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__32 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__33 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__32 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS (w__33 +++ w__34)))
                  else
                    (do
                      let w__35 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__36 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__37 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__35 Regime_EL10 w__36 Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS (w__37 +++ w__38))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__39) +++ (_get_HCR_EL2_Type_TGE w__40)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__41 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__42 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__41 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBILevel_Last TLBI_ExcludeXS (w__42 +++ w__43)))
                      else
                        (do
                          let w__44 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__45 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__46 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__47 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__44 Regime_EL10 w__45 Shareability_NSH TLBILevel_Last
                            TLBI_ExcludeXS (w__46 +++ w__47))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_VAALE1_SysOpsWrite128_ff6dfd8757e0cbb3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVAALE1 : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVAALE1 w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FB : (BitVec 1) := (_get_HCR_EL2_Type_FB w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_TLBIVAALE1 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (IsFeatureImplemented FEAT_XS)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (IsHCRXEL2Enabled ()))
                              else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          let w__21 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__22 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__23 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__21 Regime_EL10 w__22 Shareability_ISH TLBILevel_Last
                            TLBI_ExcludeXS (w__23 +++ w__24)))
                      else
                        (do
                          let w__25 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__26 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__27 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__25 Regime_EL10 w__26 Shareability_ISH TLBILevel_Last
                            TLBI_AllAttr (w__27 +++ w__28))))
                  else
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (IsFeatureImplemented FEAT_XS)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (IsHCRXEL2Enabled ()))
                              else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__34 : Bool)
                      then
                        (do
                          let w__35 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__36 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__37 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__35 Regime_EL10 w__36 Shareability_NSH TLBILevel_Last
                            TLBI_ExcludeXS (w__37 +++ w__38)))
                      else
                        (do
                          let w__39 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__40 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__41 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_VAA w__39 Regime_EL10 w__40 Shareability_NSH TLBILevel_Last
                            TLBI_AllAttr (w__41 +++ w__42)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__43 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__43) +++ (_get_HCR_EL2_Type_TGE w__44)) == 0b11#2) : Bool)
              then
                (do
                  let w__45 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__46 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__47 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VAA w__45 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr (w__46 +++ w__47)))
              else
                (do
                  let w__48 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__49 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__50 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__51 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_VAA w__48 Regime_EL10 w__49 Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr (w__50 +++ w__51))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__52 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__53 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__52) +++ (_get_HCR_EL2_Type_TGE w__53)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__54 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__55 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__56 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__54 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                        TLBI_AllAttr (w__55 +++ w__56)))
                  else
                    (do
                      let w__57 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__58 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__59 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__60 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_VAA w__57 Regime_EL10 w__58 Shareability_NSH TLBILevel_Last
                        TLBI_AllAttr (w__59 +++ w__60))))
              else (pure (())))))


end ArmFull.Functions
