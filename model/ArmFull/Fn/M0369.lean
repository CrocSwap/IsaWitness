import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0047
import ArmFull.Fn.M0064
import ArmFull.Fn.M0073
import ArmFull.Fn.M0075
import ArmFull.Fn.M0086
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
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
def PMEVCNTR_EL0_SysRegRead_ef3a8d2a7921c11c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__12 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         (pure ((← do
                               (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__12 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__22 ← (( do
            if ((← do
                 if ((← do
                      (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                 then
                   (do
                     let w__14 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     let w__15 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     let w__16 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     (pure (((((_get_PMUSERENR_EL0_Type_UEN w__14) +++ ((_get_PMUSERENR_EL0_Type_ER
                               w__15) +++ (_get_PMUSERENR_EL0_Type_EN w__16))) == 0b000#3) : Bool))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     let w__18 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                     (pure (((! w__18) : Bool)))) : Bool)
                then
                  (do
                    let w__19 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                    let w__20 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                    (pure (((((_get_PMUSERENR_EL0_Type_ER w__19) +++ (_get_PMUSERENR_EL0_Type_EN
                            w__20)) == 0b00#2) : Bool))))
                else (pure false)) ) : SailM Bool )
          if (w__22 : Bool)
          then
            (do
              let w__24 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__32 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE
                                             w__27)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__32 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__34 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__34 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__36 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((17 ≥b w__36) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          let w__38 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__38) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              let w__40 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__40 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__41 ← (( do readReg PMEVCNTR_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              (X_set t 64 (GetElem?.getElem! w__41 17)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__47 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__47 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__52 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__52 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__54 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__54 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__57 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__56 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((17 ≥b w__56) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__57 : Bool)
                      then
                        (do
                          let w__58 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__58) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              let w__60 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__60 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__61 ← (( do readReg PMEVCNTR_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              (X_set t 64 (GetElem?.getElem! w__61 17))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__67 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__67 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                  then
                    (do
                      let w__69 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__69 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__70 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
                      (X_set t 64 (GetElem?.getElem! w__70 17)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__71 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
                  (X_set t 64 (GetElem?.getElem! w__71 17)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMEVCNTR_EL0_SysRegRead_fccbe0710386c98a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMEVCNTRn_EL0 w__5)
  let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__12 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         (pure ((← do
                               (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__12 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__22 ← (( do
            if ((← do
                 if ((← do
                      (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                 then
                   (do
                     let w__14 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     let w__15 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     let w__16 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     (pure (((((_get_PMUSERENR_EL0_Type_UEN w__14) +++ ((_get_PMUSERENR_EL0_Type_ER
                               w__15) +++ (_get_PMUSERENR_EL0_Type_EN w__16))) == 0b000#3) : Bool))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     let w__18 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                     (pure (((! w__18) : Bool)))) : Bool)
                then
                  (do
                    let w__19 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                    let w__20 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                    (pure (((((_get_PMUSERENR_EL0_Type_ER w__19) +++ (_get_PMUSERENR_EL0_Type_EN
                            w__20)) == 0b00#2) : Bool))))
                else (pure false)) ) : SailM Bool )
          if (w__22 : Bool)
          then
            (do
              let w__24 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__32 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE
                                             w__27)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__32 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__34 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__34 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__36 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((25 ≥b w__36) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          let w__38 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__38) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              let w__40 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__40 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__41 ← (( do readReg PMEVCNTR_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              (X_set t 64 (GetElem?.getElem! w__41 25)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__47 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__47 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__52 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__52 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__54 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__54 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__57 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__56 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((25 ≥b w__56) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__57 : Bool)
                      then
                        (do
                          let w__58 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__58) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                          then
                            (do
                              let w__60 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__60 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__61 ← (( do readReg PMEVCNTR_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              (X_set t 64 (GetElem?.getElem! w__61 25))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__67 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__67 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                  then
                    (do
                      let w__69 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__69 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__70 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
                      (X_set t 64 (GetElem?.getElem! w__70 25)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__71 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
                  (X_set t 64 (GetElem?.getElem! w__71 25)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMEVCNTSVR_EL1_SysRegRead_0219fbdb2658ca68 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPMSS : (BitVec 1) := (_get_MDCR_EL3_Type_EnPMSS w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__3)
  let w__4 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR2_EL2_nPMSSDATA : (BitVec 1) := (_get_HDFGRTR2_EL2_Type_nPMSSDATA w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_EnPMSS == 0#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT2))
                            else (pure false)) && ((HaveEL EL3) : Bool)))) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGRTR2_EL2_nPMSSDATA == 0#1) : Bool))) ) :
                    SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                      then
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__21 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__22 ← (( do readReg PMEVCNTSVR_EL1 ) : SailM
                            (Vector (BitVec 64) 31) )
                          (X_set t 64 (GetElem?.getElem! w__22 26)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__28 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPMSS == 0#1) : Bool))) ) : SailM Bool )
              if (w__28 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_EnPMSS == 0#1)) : Bool)
                  then
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__30 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__31 ← (( do readReg PMEVCNTSVR_EL1 ) : SailM (Vector (BitVec 64) 31) )
                      (X_set t 64 (GetElem?.getElem! w__31 26)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__32 ← (( do readReg PMEVCNTSVR_EL1 ) : SailM (Vector (BitVec 64) 31) )
                  (X_set t 64 (GetElem?.getElem! w__32 26)))
              else (pure (())))))


end ArmFull.Functions
