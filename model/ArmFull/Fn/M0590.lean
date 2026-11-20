module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0158
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0252 set_option backward.proofsInPublic true @[expose] public section

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
def TLBIP_RVAALE1_SysOpsWrite128_af1f37b9406d3bd8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIRVAALE1 : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIRVAALE1 w__3)
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
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__11 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__11) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGITR_EL2_TLBIRVAALE1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_FB == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      let w__22 ← (( do
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
                      if (w__22 : Bool)
                      then
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__25 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVAA w__23 Regime_EL10 w__24 Shareability_ISH
                            TLBILevel_Last TLBI_ExcludeXS (w__25 +++ w__26)))
                      else
                        (do
                          let w__27 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__28 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__29 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVAA w__27 Regime_EL10 w__28 Shareability_ISH
                            TLBILevel_Last TLBI_AllAttr (w__29 +++ w__30))))
                  else
                    (do
                      let w__36 ← (( do
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
                      if (w__36 : Bool)
                      then
                        (do
                          let w__37 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__38 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__39 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVAA w__37 Regime_EL10 w__38 Shareability_NSH
                            TLBILevel_Last TLBI_ExcludeXS (w__39 +++ w__40)))
                      else
                        (do
                          let w__41 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__42 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__43 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVAA w__41 Regime_EL10 w__42 Shareability_NSH
                            TLBILevel_Last TLBI_AllAttr (w__43 +++ w__44)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__45) +++ (_get_HCR_EL2_Type_TGE w__46)) == 0b11#2) : Bool)
              then
                (do
                  let w__47 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__48 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__49 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RVAA w__47 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr (w__48 +++ w__49)))
              else
                (do
                  let w__50 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__51 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__52 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__53 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RVAA w__50 Regime_EL10 w__51 Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr (w__52 +++ w__53))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__54 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__55 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__54) +++ (_get_HCR_EL2_Type_TGE w__55)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__56 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__57 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__58 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVAA w__56 Regime_EL20 VMID_NONE Shareability_NSH
                        TLBILevel_Last TLBI_AllAttr (w__57 +++ w__58)))
                  else
                    (do
                      let w__59 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__60 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__61 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__62 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVAA w__59 Regime_EL10 w__60 Shareability_NSH TLBILevel_Last
                        TLBI_AllAttr (w__61 +++ w__62))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1IS_SysOpsWrite128_07c7343c7a06f43b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIRVAE1IS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIRVAE1IS w__4)
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
                      (EL2Enabled ())) && ((__HCR_EL2_TTLBIS == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__13) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGITR_EL2_TLBIRVAE1IS == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                      if (w__22 : Bool)
                      then
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__25 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__23 Regime_EL10 w__24 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS (w__25 +++ w__26)))
                      else
                        (do
                          let w__27 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__28 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__29 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__27 Regime_EL10 w__28 Shareability_ISH TLBILevel_Any
                            TLBI_AllAttr (w__29 +++ w__30)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__31) +++ (_get_HCR_EL2_Type_TGE w__32)) == 0b11#2) : Bool)
              then
                (do
                  let w__33 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__34 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RVA w__33 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr (w__34 +++ w__35)))
              else
                (do
                  let w__36 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__37 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__38 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RVA w__36 Regime_EL10 w__37 Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr (w__38 +++ w__39))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE w__41)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__42 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__43 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__42 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any
                        TLBI_AllAttr (w__43 +++ w__44)))
                  else
                    (do
                      let w__45 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__46 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__47 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__48 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__45 Regime_EL10 w__46 Shareability_ISH TLBILevel_Any
                        TLBI_AllAttr (w__47 +++ w__48))))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1IS_SysOpsWrite128_7b5e59f759169cbe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__2)
  let w__3 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIRVAE1IS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIRVAE1IS w__4)
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
                      let w__22 ← (( do
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
                                            if ((← do
                                                 let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                 (pure (((! w__13) : Bool)))) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__14 ← (( do readReg SCR_EL3 ) : SailM
                                                  (BitVec 64) )
                                                (pure ((((_get_SCR_EL3_Type_FGTEn w__14) == 1#1) : Bool)))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__19 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_TLBIRVAE1IS == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__25 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__23 Regime_EL10 w__24 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS (w__25 +++ w__26))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE w__28)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__29 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__30 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__29 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS (w__30 +++ w__31)))
                  else
                    (do
                      let w__32 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__33 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__34 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__32 Regime_EL10 w__33 Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS (w__34 +++ w__35))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__36) +++ (_get_HCR_EL2_Type_TGE w__37)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__38 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__39 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__38 Regime_EL20 VMID_NONE Shareability_ISH
                            TLBILevel_Any TLBI_ExcludeXS (w__39 +++ w__40)))
                      else
                        (do
                          let w__41 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__42 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__43 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__41 Regime_EL10 w__42 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS (w__43 +++ w__44))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1OS_SysOpsWrite128_52f9177ad8036aaf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBOS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBOS w__2)
  let w__3 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIRVAE1OS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIRVAE1OS w__4)
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
                      let w__22 ← (( do
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
                                            if ((← do
                                                 let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                                 (pure (((! w__13) : Bool)))) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__14 ← (( do readReg SCR_EL3 ) : SailM
                                                  (BitVec 64) )
                                                (pure ((((_get_SCR_EL3_Type_FGTEn w__14) == 1#1) : Bool)))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_HCX))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__19 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                        (pure (((! w__19) : Bool)))) || ((__HCRX_EL2_FGTnXS == 0#1) : Bool))))
                              else (pure false)) && ((__HFGITR_EL2_TLBIRVAE1OS == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                      else
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__25 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__23 Regime_EL10 w__24 Shareability_OSH TLBILevel_Any
                            TLBI_ExcludeXS (w__25 +++ w__26))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE w__28)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__29 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__30 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__29 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any
                        TLBI_ExcludeXS (w__30 +++ w__31)))
                  else
                    (do
                      let w__32 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__33 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__34 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__32 Regime_EL10 w__33 Shareability_OSH TLBILevel_Any
                        TLBI_ExcludeXS (w__34 +++ w__35))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__36) +++ (_get_HCR_EL2_Type_TGE w__37)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__38 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__39 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__38 Regime_EL20 VMID_NONE Shareability_OSH
                            TLBILevel_Any TLBI_ExcludeXS (w__39 +++ w__40)))
                      else
                        (do
                          let w__41 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__42 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__43 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__41 Regime_EL10 w__42 Shareability_OSH TLBILevel_Any
                            TLBI_ExcludeXS (w__43 +++ w__44))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int, t2 : Int -/
def TLBIP_RVAE1OS_SysOpsWrite128_953ff681e796131f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBOS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBOS w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIRVAE1OS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIRVAE1OS w__4)
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
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__13) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HFGITR_EL2_TLBIRVAE1OS == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x14#8)))
                  else
                    (do
                      let w__22 ← (( do
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
                      if (w__22 : Bool)
                      then
                        (do
                          let w__23 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__24 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__25 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__23 Regime_EL10 w__24 Shareability_OSH TLBILevel_Any
                            TLBI_ExcludeXS (w__25 +++ w__26)))
                      else
                        (do
                          let w__27 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__28 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__29 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                          let w__30 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBIP_RVA w__27 Regime_EL10 w__28 Shareability_OSH TLBILevel_Any
                            TLBI_AllAttr (w__29 +++ w__30)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__31) +++ (_get_HCR_EL2_Type_TGE w__32)) == 0b11#2) : Bool)
              then
                (do
                  let w__33 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__34 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RVA w__33 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any
                    TLBI_AllAttr (w__34 +++ w__35)))
              else
                (do
                  let w__36 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__37 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__38 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBIP_RVA w__36 Regime_EL10 w__37 Shareability_OSH TLBILevel_Any
                    TLBI_AllAttr (w__38 +++ w__39))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE w__41)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__42 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__43 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__42 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any
                        TLBI_AllAttr (w__43 +++ w__44)))
                  else
                    (do
                      let w__45 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__46 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__47 ← (( do (X_read t2 64) ) : SailM (BitVec 64) )
                      let w__48 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBIP_RVA w__45 Regime_EL10 w__46 Shareability_OSH TLBILevel_Any
                        TLBI_AllAttr (w__47 +++ w__48))))
              else (pure (())))))


end ArmFull.Functions
