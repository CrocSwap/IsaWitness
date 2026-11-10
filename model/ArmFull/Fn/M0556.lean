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

/-- Type quantifiers: t : Int -/
def TLBI_VAE1_SysOpsWrite_cdcaa8b8b8d87463 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVAE1 : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVAE1 w__3)
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
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
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
                          else (pure false)) && ((__HFGITR_EL2_TLBIVAE1 == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
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
                          let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__22 Regime_EL10 w__23 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS w__24))
                      else
                        (do
                          let w__25 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__26 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__25 Regime_EL10 w__26 Shareability_NSH TLBILevel_Any
                            TLBI_ExcludeXS w__27)))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE w__29)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__30 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__30 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any
                        TLBI_ExcludeXS w__31))
                  else
                    (do
                      let w__32 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__33 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__32 Regime_EL10 w__33 Shareability_NSH TLBILevel_Any
                        TLBI_ExcludeXS w__34)))
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
                          let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__37 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBILevel_Any TLBI_ExcludeXS w__38))
                      else
                        (do
                          let w__39 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__40 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__39 Regime_EL10 w__40 Shareability_NSH TLBILevel_Any
                            TLBI_ExcludeXS w__41)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE2IS_SysOpsWrite_b944414311b6f47e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      (AArch64_TLBI_VA w__6 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS w__7))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__8 Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any
                        TLBI_ExcludeXS w__9)))
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
                              (AArch64_TLBI_VA w__11 Regime_EL20 VMID_NONE Shareability_ISH
                                TLBILevel_Any TLBI_ExcludeXS w__12))
                          else
                            (do
                              let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_VA w__13 Regime_EL2 VMID_NONE Shareability_ISH
                                TLBILevel_Any TLBI_ExcludeXS w__14))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE2IS_SysOpsWrite_ba6a5005f8e50b0a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_VA w__5 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr w__6))
              else
                (do
                  let w__7 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__7 Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any
                    TLBI_AllAttr w__8)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__9) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__10 Regime_EL20 VMID_NONE Shareability_ISH
                            TLBILevel_Any TLBI_AllAttr w__11))
                      else
                        (do
                          let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__12 Regime_EL2 VMID_NONE Shareability_ISH TLBILevel_Any
                            TLBI_AllAttr w__13))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE2OS_SysOpsWrite_6f840e706adb25b2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      (AArch64_TLBI_VA w__6 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any
                        TLBI_ExcludeXS w__7))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__8 Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any
                        TLBI_ExcludeXS w__9)))
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
                              (AArch64_TLBI_VA w__11 Regime_EL20 VMID_NONE Shareability_OSH
                                TLBILevel_Any TLBI_ExcludeXS w__12))
                          else
                            (do
                              let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_VA w__13 Regime_EL2 VMID_NONE Shareability_OSH
                                TLBILevel_Any TLBI_ExcludeXS w__14))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE2OS_SysOpsWrite_f8b097ac65738708 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_VA w__5 Regime_EL20 VMID_NONE Shareability_OSH TLBILevel_Any
                    TLBI_AllAttr w__6))
              else
                (do
                  let w__7 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__7 Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any
                    TLBI_AllAttr w__8)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__9) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__10 Regime_EL20 VMID_NONE Shareability_OSH
                            TLBILevel_Any TLBI_AllAttr w__11))
                      else
                        (do
                          let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__12 Regime_EL2 VMID_NONE Shareability_OSH TLBILevel_Any
                            TLBI_AllAttr w__13))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE2_SysOpsWrite_23241f5754371907 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (AArch64_TLBI_VA w__5 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any
                    TLBI_AllAttr w__6))
              else
                (do
                  let w__7 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_VA w__7 Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any
                    TLBI_AllAttr w__8)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__9 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__9) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__10 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__10 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBILevel_Any TLBI_AllAttr w__11))
                      else
                        (do
                          let w__12 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__12 Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any
                            TLBI_AllAttr w__13))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_VAE2_SysOpsWrite_ab883e6d7c8e2e48 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      (AArch64_TLBI_VA w__6 Regime_EL20 VMID_NONE Shareability_NSH TLBILevel_Any
                        TLBI_ExcludeXS w__7))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__8 Regime_EL2 VMID_NONE Shareability_NSH TLBILevel_Any
                        TLBI_ExcludeXS w__9)))
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
                              (AArch64_TLBI_VA w__11 Regime_EL20 VMID_NONE Shareability_NSH
                                TLBILevel_Any TLBI_ExcludeXS w__12))
                          else
                            (do
                              let w__13 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                              let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (AArch64_TLBI_VA w__13 Regime_EL2 VMID_NONE Shareability_NSH
                                TLBILevel_Any TLBI_ExcludeXS w__14))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_VALE1IS_SysOpsWrite_0978356bc7a2174b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLBIS : (BitVec 1) := (_get_HCR_EL2_Type_TTLBIS w__2)
  let w__3 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__3)
  let w__4 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIVALE1IS : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIVALE1IS w__4)
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
                              else (pure false)) && ((__HFGITR_EL2_TLBIVALE1IS == 1#1) : Bool))) ) :
                        SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__22 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__23 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__24 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__22 Regime_EL10 w__23 Shareability_ISH TLBILevel_Last
                            TLBI_ExcludeXS w__24)))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  if ((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE w__26)) == 0b11#2) : Bool)
                  then
                    (do
                      let w__27 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                      let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__27 Regime_EL20 VMID_NONE Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS w__28))
                  else
                    (do
                      let w__29 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__30 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_VA w__29 Regime_EL10 w__30 Shareability_ISH TLBILevel_Last
                        TLBI_ExcludeXS w__31)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__32 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if ((((_get_HCR_EL2_Type_E2H w__32) +++ (_get_HCR_EL2_Type_TGE w__33)) == 0b11#2) : Bool)
                      then
                        (do
                          let w__34 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
                          let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__34 Regime_EL20 VMID_NONE Shareability_ISH
                            TLBILevel_Last TLBI_ExcludeXS w__35))
                      else
                        (do
                          let w__36 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__37 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_VA w__36 Regime_EL10 w__37 Shareability_ISH TLBILevel_Last
                            TLBI_ExcludeXS w__38)))
                  else (pure (()))))))


end ArmFull.Functions
