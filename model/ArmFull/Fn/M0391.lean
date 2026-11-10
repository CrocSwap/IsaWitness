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
import ArmFull.Fn.M0041
import ArmFull.Fn.M0047
import ArmFull.Fn.M0064
import ArmFull.Fn.M0071
import ArmFull.Fn.M0073
import ArmFull.Fn.M0086
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0139
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
def PMXEVTYPER_EL0_SysRegRead_822f8e38c465529c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TPM : (BitVec 1) := (_get_MDCR_EL3_Type_TPM w__2)
  let w__3 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __PMUSERENR_EL0_EN : (BitVec 1) := (_get_PMUSERENR_EL0_Type_EN w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGRTR_EL2_PMEVTYPERn_EL0 : (BitVec 1) := (_get_HDFGRTR_EL2_Type_PMEVTYPERn_EL0 w__6)
  let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__7)
  let w__10 ← (( do
    if ((← do
         let w__8 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
         (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__8)) != 31) : Bool)))) : Bool)
    then
      (do
        let w__9 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
        (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__9)) ≥b 31) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__10 : Bool)
  then
    (do
      let w__11 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
      if (w__11 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__17 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__24 ← (( do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__19 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__20 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__19) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__20)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__22 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__22) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))) )
                : SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__34 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                         let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                         (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                                 w__29)) != 0b11#2) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__34 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__36 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__42 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__38 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                     (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__38)) != 31) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__40 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                let w__41 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) :
                                  SailM Int )
                                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__40)) ≥b w__41) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__42 : Bool)
                          then
                            (do
                              let w__43 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                              if ((! w__43) : Bool)
                              then
                                (pure ((ConstrainUnpredictableProcedure
                                    Unpredictable_PMUEVENTCOUNTER)))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  let w__45 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__45 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__46 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                  if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__46)) == 31) : Bool)
                                  then
                                    (do
                                      let w__47 ← (( do readReg PMCCFILTR_EL0 ) : SailM
                                        (BitVec 64) )
                                      (X_set t 64 (__get_PMCCFILTR_EL0 w__47)))
                                  else
                                    (do
                                      let w__48 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                        (Vector (BitVec 64) 32) )
                                      let w__49 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                      (X_set t 64
                                        (__get_PMEVTYPER_EL0
                                          (GetElem?.getElem! w__48
                                            (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__49)))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__55 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__55 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__60 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGRTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__60 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__62 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__62 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__68 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__64 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                     (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__64)) != 31) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__66 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                let w__67 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) :
                                  SailM Int )
                                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__66)) ≥b w__67) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__68 : Bool)
                          then
                            (do
                              let w__69 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                              if ((! w__69) : Bool)
                              then
                                (pure ((ConstrainUnpredictableProcedure
                                    Unpredictable_PMUEVENTCOUNTER)))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                              then
                                (do
                                  let w__71 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__71 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__72 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                  if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__72)) == 31) : Bool)
                                  then
                                    (do
                                      let w__73 ← (( do readReg PMCCFILTR_EL0 ) : SailM
                                        (BitVec 64) )
                                      (X_set t 64 (__get_PMCCFILTR_EL0 w__73)))
                                  else
                                    (do
                                      let w__74 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                        (Vector (BitVec 64) 32) )
                                      let w__75 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                      (X_set t 64
                                        (__get_PMEVTYPER_EL0
                                          (GetElem?.getElem! w__74
                                            (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__75))))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__81 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__81 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__MDCR_EL3_TPM == 1#1)) : Bool)
                      then
                        (do
                          let w__83 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__83 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__84 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                          if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__84)) == 31) : Bool)
                          then
                            (do
                              let w__85 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64 (__get_PMCCFILTR_EL0 w__85)))
                          else
                            (do
                              let w__86 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              let w__87 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_PMEVTYPER_EL0
                                  (GetElem?.getElem! w__86
                                    (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__87)))))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__88 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                      if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__88)) == 31) : Bool)
                      then
                        (do
                          let w__89 ← (( do readReg PMCCFILTR_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_PMCCFILTR_EL0 w__89)))
                      else
                        (do
                          let w__90 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                            (Vector (BitVec 64) 32) )
                          let w__91 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_PMEVTYPER_EL0
                              (GetElem?.getElem! w__90
                                (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__91)))))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def POR_EL0_SysRegRead_b50bc065c1491be2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_PIEn : (BitVec 1) := (_get_SCR_EL3_Type_PIEn w__2)
  let w__3 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  let __CPACR_EL1_E0POE : (BitVec 1) := (_get_CPACR_EL1_Type_E0POE w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TRVM : (BitVec 1) := (_get_HCR_EL2_Type_TRVM w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_nPOR_EL0 : (BitVec 1) := (_get_HFGRTR_EL2_Type_nPOR_EL0 w__7)
  let w__8 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_E0POE : (BitVec 1) := (_get_CPTR_EL2_Type_E0POE w__8)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__14 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         (pure ((← do
                               (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__19 ← (( do
            (pure ((← do
                  let w__18 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__16) +++ (_get_HCR_EL2_Type_TGE w__17)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__18) : Bool)))) && ((__CPACR_EL1_E0POE == 0#1) : Bool))) ) : SailM
            Bool )
          if (w__19 : Bool)
          then
            (do
              let w__21 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__21 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE w__24)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__HCR_EL2_TRVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__34 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                         let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                         (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                                 w__29)) != 0b11#2) : Bool))))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGRTR_EL2_nPOR_EL0 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__34 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__39 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__36 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__36) +++ (_get_HCR_EL2_Type_TGE
                                          w__37)) == 0b11#2) : Bool))))
                              else (pure false)) && ((__CPTR_EL2_E0POE == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__39 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                          then
                            (do
                              let w__41 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__41 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__42 ← (( do readReg POR_EL0 ) : SailM (BitVec 64) )
                              (X_set t 64 w__42))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__48 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__48 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__50 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TRVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__50 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__55 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGRTR_EL2_nPOR_EL0 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__55 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                      then
                        (do
                          let w__57 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__57 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__58 ← (( do readReg POR_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 w__58))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__64 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__64 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      let w__66 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__66 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__67 ← (( do readReg POR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 w__67))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__68 ← (( do readReg POR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 w__68))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def POR_EL2_SysRegRead_b9e6082fd3098e22 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_PIEn : (BitVec 1) := (_get_SCR_EL3_Type_PIEn w__3)
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
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      let w__13 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__13 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__14 ← (( do readReg POR_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__14))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do readReg POR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__15))
              else (pure (())))))


end ArmFull.Functions
