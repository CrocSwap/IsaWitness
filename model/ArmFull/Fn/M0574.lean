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
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0171
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

/-- Type quantifiers: t : Int -/
def TLBI_RVALE1_SysOpsWrite_cc74fa175b762bc3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIRVALE1 : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIRVALE1 w__3)
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
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
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
                      else (pure false)) && ((__HFGITR_EL2_TLBIRVALE1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
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
                          let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__23 Regime_EL10 w__24 Shareability_ISH TLBILevel_Last
                            TLBI_ExcludeXS w__25))
                      else
                        (do
                          let w__26 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__27 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__26 Regime_EL10 w__27 Shareability_ISH TLBILevel_Last
                            TLBI_AllAttr w__28)))
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
                          let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__35 Regime_EL10 w__36 Shareability_NSH TLBILevel_Last
                            TLBI_ExcludeXS w__37))
                      else
                        (do
                          let w__38 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__39 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__38 Regime_EL10 w__39 Shareability_NSH TLBILevel_Last
                            TLBI_AllAttr w__40))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              let w__42 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
              if ((((_get_HCR_EL2_Type_E2H w__41) +++ (_get_HCR_EL2_Type_TGE w__42)) == 0b11#2) : Bool)
              then
                (do
                  let w__43 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__43 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__44))
              else
                (do
                  let w__45 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__46 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__47 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__45 Regime_EL10 w__46 Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__47)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__48 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__49 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__48) +++ (_get_HCR_EL2_Type_TGE w__49)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__50 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__51 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__50 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                        TLBI_AllAttr w__51))
                  else
                    (do
                      let w__52 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__53 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__54 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__52 Regime_EL10 w__53 Shareability_NSH TLBILevel_Last
                        TLBI_AllAttr w__54)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE2IS_SysOpsWrite_c832bf01bcbc2cc0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__5 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last
                    TLBI_AllAttr w__6))
              else
                (do
                  let w__7 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__8 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__7 Regime_EL2 w__8 Shareability_ISH TLBILevel_Last
                    TLBI_AllAttr w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__10) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__11 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__11 Regime_EL20 VMID_NONE Shareability_ISH
                            TLBILevel_Last TLBI_AllAttr w__12))
                      else
                        (do
                          let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__14 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__13 Regime_EL2 w__14 Shareability_ISH TLBILevel_Last
                            TLBI_AllAttr w__15))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE2IS_SysOpsWrite_ca640565cc2dea92 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__3) : Bool)
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
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then
                    (do
                      let w__6 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__6 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS w__7))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__8 Regime_EL2 w__9 Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS w__10)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__11) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then
                            (do
                              let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_RVA w__12 Regime_EL20 VMID_NONE Shareability_ISH
                                TLBILevel_Last TLBI_ExcludeXS w__13))
                          else
                            (do
                              let w__14 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__15 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                              let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_RVA w__14 Regime_EL2 w__15 Shareability_ISH
                                TLBILevel_Last TLBI_ExcludeXS w__16))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE2OS_SysOpsWrite_0b11b74e4b3a3cfe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__3) : Bool)
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
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then
                    (do
                      let w__6 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__6 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS w__7))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__8 Regime_EL2 w__9 Shareability_OSH TLBILevel_Last
                        TLBI_ExcludeXS w__10)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__11) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then
                            (do
                              let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_RVA w__12 Regime_EL20 VMID_NONE Shareability_OSH
                                TLBILevel_Last TLBI_ExcludeXS w__13))
                          else
                            (do
                              let w__14 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__15 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                              let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_RVA w__14 Regime_EL2 w__15 Shareability_OSH
                                TLBILevel_Last TLBI_ExcludeXS w__16))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE2OS_SysOpsWrite_36a17e51dcbb19d2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__5 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr w__6))
              else
                (do
                  let w__7 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__8 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__7 Regime_EL2 w__8 Shareability_OSH TLBILevel_Last
                    TLBI_AllAttr w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__10) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__11 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__11 Regime_EL20 VMID_NONE Shareability_OSH
                            TLBILevel_Last TLBI_AllAttr w__12))
                      else
                        (do
                          let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__14 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__13 Regime_EL2 w__14 Shareability_OSH TLBILevel_Last
                            TLBI_AllAttr w__15))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE2_SysOpsWrite_a051bc1bccde7cd9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__3) : Bool)
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
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then
                    (do
                      let w__6 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__6 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS w__7))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_RVA w__8 Regime_EL2 w__9 Shareability_NSH TLBILevel_Last
                        TLBI_ExcludeXS w__10)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__11 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__11) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          if ((__HCR_EL2_E2H == 1#1) : Bool)
                          then
                            (do
                              let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_RVA w__12 Regime_EL20 VMID_NONE Shareability_NSH
                                TLBILevel_Last TLBI_ExcludeXS w__13))
                          else
                            (do
                              let w__14 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__15 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                              let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_RVA w__14 Regime_EL2 w__15 Shareability_NSH
                                TLBILevel_Last TLBI_ExcludeXS w__16))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_RVALE2_SysOpsWrite_be8d66432234a830 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__5 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__6))
              else
                (do
                  let w__7 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__8 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RVA w__7 Regime_EL2 w__8 Shareability_NSH TLBILevel_Last
                    TLBI_AllAttr w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__10) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__11 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__11 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBILevel_Last TLBI_AllAttr w__12))
                      else
                        (do
                          let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__14 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_RVA w__13 Regime_EL2 w__14 Shareability_NSH TLBILevel_Last
                            TLBI_AllAttr w__15))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VAAE1IS_SysOpsWrite_b0e95e7b2139780d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVAAE1IS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVAAE1IS w__4)
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
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__9 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TTLBIS == 1#1) : Bool))) ) : SailM Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
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
                          else (pure false)) && ((__HFGITR_EL2_TLBIVAAE1IS == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
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
                          let w__25 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VAA w__23 Regime_EL10 w__24 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS w__25))
                      else
                        (do
                          let w__26 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__27 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VAA w__26 Regime_EL10 w__27 Shareability_ISH TLBILevel_Any
                            TLBI_AllAttr w__28))))))
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
                  let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VAA w__31 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr w__32))
              else
                (do
                  let w__33 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__34 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VAA w__33 Regime_EL10 w__34 Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr w__35)))
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
                      let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VAA w__38 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any
                        TLBI_AllAttr w__39))
                  else
                    (do
                      let w__40 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__41 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VAA w__40 Regime_EL10 w__41 Shareability_ISH TLBILevel_Any
                        TLBI_AllAttr w__42)))
              else (pure (())))))


end ArmFull.Functions
