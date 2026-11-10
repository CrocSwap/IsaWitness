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
import ArmFull.Fn.M0051
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
def TLBI_ASIDE1_SysOpsWrite_43318f45323f6d95 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__1)
  let w__2 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FGTnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FGTnXS w__2)
  let w__3 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_TLBIASIDE1 : (BitVec 1) := (_get_HFGITR_EL2_Type_TLBIASIDE1 w__3)
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
                          else (pure false)) && ((__HFGITR_EL2_TLBIASIDE1 == 1#1) : Bool))) ) :
                    SailM Bool )
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
                          (AArch64_TLBI_ASID w__22 Regime_EL10 w__23 Shareability_ISH TLBI_ExcludeXS
                            w__24))
                      else
                        (do
                          let w__25 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__26 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_ASID w__25 Regime_EL10 w__26 Shareability_NSH TLBI_ExcludeXS
                            w__27)))))
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
                      (AArch64_TLBI_ASID w__30 Regime_EL20 VMID_NONE Shareability_NSH TLBI_ExcludeXS
                        w__31))
                  else
                    (do
                      let w__32 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__33 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__34 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_ASID w__32 Regime_EL10 w__33 Shareability_NSH TLBI_ExcludeXS
                        w__34)))
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
                          (AArch64_TLBI_ASID w__37 Regime_EL20 VMID_NONE Shareability_NSH
                            TLBI_ExcludeXS w__38))
                      else
                        (do
                          let w__39 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__40 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_ASID w__39 Regime_EL10 w__40 Shareability_NSH TLBI_ExcludeXS
                            w__41)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1IS_SysOpsWrite_4c58dae59e564c5f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__2) : Bool)
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
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_IPAS2 w__5 Regime_EL10 w__6 Shareability_ISH TLBILevel_Any
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_IPAS2 w__9 Regime_EL10 w__10 Shareability_ISH TLBILevel_Any
                            TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1IS_SysOpsWrite_ccc65f430a044914 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_IPAS2 w__4 Regime_EL10 w__5 Shareability_ISH TLBILevel_Any TLBI_AllAttr
                w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_IPAS2 w__8 Regime_EL10 w__9 Shareability_ISH TLBILevel_Any
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1OS_SysOpsWrite_309d90a600b530a7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_IPAS2 w__4 Regime_EL10 w__5 Shareability_OSH TLBILevel_Any TLBI_AllAttr
                w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_IPAS2 w__8 Regime_EL10 w__9 Shareability_OSH TLBILevel_Any
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1OS_SysOpsWrite_39b2c10069047b39 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__2) : Bool)
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
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_IPAS2 w__5 Regime_EL10 w__6 Shareability_OSH TLBILevel_Any
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_IPAS2 w__9 Regime_EL10 w__10 Shareability_OSH TLBILevel_Any
                            TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1_SysOpsWrite_97895c8e9b4d80f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_IPAS2 w__4 Regime_EL10 w__5 Shareability_NSH TLBILevel_Any TLBI_AllAttr
                w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_IPAS2 w__8 Regime_EL10 w__9 Shareability_NSH TLBILevel_Any
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2E1_SysOpsWrite_b3136916ac77cb10 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__2) : Bool)
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
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_IPAS2 w__5 Regime_EL10 w__6 Shareability_NSH TLBILevel_Any
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_IPAS2 w__9 Regime_EL10 w__10 Shareability_NSH TLBILevel_Any
                            TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1IS_SysOpsWrite_48fbca66415d71e4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__2) : Bool)
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
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_IPAS2 w__5 Regime_EL10 w__6 Shareability_ISH TLBILevel_Last
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_IPAS2 w__9 Regime_EL10 w__10 Shareability_ISH TLBILevel_Last
                            TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1IS_SysOpsWrite_9d56cb10a3da298e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_IPAS2 w__4 Regime_EL10 w__5 Shareability_ISH TLBILevel_Last TLBI_AllAttr
                w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_IPAS2 w__8 Regime_EL10 w__9 Shareability_ISH TLBILevel_Last
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1OS_SysOpsWrite_41165e80f36dc5fa (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__5 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_TLBI_IPAS2 w__4 Regime_EL10 w__5 Shareability_OSH TLBILevel_Last TLBI_AllAttr
                w__6))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do (EL2Enabled ()) ) : SailM Bool )
                  if ((! w__7) : Bool)
                  then (pure (()))
                  else
                    (do
                      let w__8 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                      let w__9 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_TLBI_IPAS2 w__8 Regime_EL10 w__9 Shareability_OSH TLBILevel_Last
                        TLBI_AllAttr w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_IPAS2LE1OS_SysOpsWrite_f065e8faf0d6b28c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (IsFeatureImplemented FEAT_XS) ) : SailM Bool )
  if ((! w__2) : Bool)
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
                  let w__5 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                  let w__6 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_IPAS2 w__5 Regime_EL10 w__6 Shareability_OSH TLBILevel_Last
                    TLBI_ExcludeXS w__7))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__8 ← (( do (EL2Enabled ()) ) : SailM Bool )
                      if ((! w__8) : Bool)
                      then (pure (()))
                      else
                        (do
                          let w__9 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                          let w__10 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          (AArch64_TLBI_IPAS2 w__9 Regime_EL10 w__10 Shareability_OSH TLBILevel_Last
                            TLBI_ExcludeXS w__11)))
                  else (pure (()))))))


end ArmFull.Functions
