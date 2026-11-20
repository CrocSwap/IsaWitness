module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0064
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
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
def PMEVTYPER_EL0_SysRegWrite_bd30e84b2c72691b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__6 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 w__6)
  let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__14 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         if ((← do
                              (Halted ())) : Bool)
                         then
                           (do
                             (HaveEL EL3))
                         else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__21 ← (( do
            if ((← do
                 if ((← do
                      (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                 then
                   (do
                     let w__16 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     let w__17 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     (pure (((((_get_PMUSERENR_EL0_Type_UEN w__16) +++ (_get_PMUSERENR_EL0_Type_EN
                             w__17)) == 0b00#2) : Bool))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                (pure ((← do
                      let w__19 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                      (pure (((! w__19) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))) ) :
            SailM Bool )
          if (w__21 : Bool)
          then
            (do
              let w__23 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__23 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__33 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE
                                            w__26)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__30 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__30) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool))) ) :
                SailM Bool )
              if (w__33 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__38 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__37 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((19 ≥b w__37) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__38 : Bool)
                      then
                        (do
                          let w__39 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__39) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__41 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__41 : Bool)
                          then
                            (do
                              let w__43 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__43 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__44 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMEVTYPER_EL0 (vectorUpdate w__44 19
                                (Mk_PMEVTYPER_EL0_Type w__45)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__52 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             if ((← do
                                  (Halted ())) : Bool)
                             then
                               (do
                                 (HaveEL EL3))
                             else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__52 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__59 ← (( do
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
                                let w__56 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__56) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool))) ) :
                SailM Bool )
              if (w__59 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__61 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__61 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__64 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__63 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((19 ≥b w__63) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__64 : Bool)
                      then
                        (do
                          let w__65 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__65) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__67 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__67 : Bool)
                          then
                            (do
                              let w__69 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__69 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__70 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              let w__71 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMEVTYPER_EL0 (vectorUpdate w__70 19
                                (Mk_PMEVTYPER_EL0_Type w__71))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__78 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__78 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__80 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__80 : Bool)
                  then
                    (do
                      let w__82 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__82 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__83 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
                      let w__84 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMEVTYPER_EL0 (vectorUpdate w__83 19 (Mk_PMEVTYPER_EL0_Type w__84)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__85 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
                  let w__86 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PMEVTYPER_EL0 (vectorUpdate w__85 19 (Mk_PMEVTYPER_EL0_Type w__86)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMEVTYPER_EL0_SysRegWrite_bee5b17c9678351b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__6 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMEVTYPERn_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMEVTYPERn_EL0 w__6)
  let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__14 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         if ((← do
                              (Halted ())) : Bool)
                         then
                           (do
                             (HaveEL EL3))
                         else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__21 ← (( do
            if ((← do
                 if ((← do
                      (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                 then
                   (do
                     let w__16 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     let w__17 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     (pure (((((_get_PMUSERENR_EL0_Type_UEN w__16) +++ (_get_PMUSERENR_EL0_Type_EN
                             w__17)) == 0b00#2) : Bool))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                (pure ((← do
                      let w__19 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                      (pure (((! w__19) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))) ) :
            SailM Bool )
          if (w__21 : Bool)
          then
            (do
              let w__23 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__23 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__33 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE
                                            w__26)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT))
                           else (pure false)) : Bool)
                      then
                        (do
                          (pure ((← do
                                let w__30 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__30) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool))) ) :
                SailM Bool )
              if (w__33 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__38 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__37 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((21 ≥b w__37) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__38 : Bool)
                      then
                        (do
                          let w__39 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__39) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__41 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__41 : Bool)
                          then
                            (do
                              let w__43 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__43 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__44 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMEVTYPER_EL0 (vectorUpdate w__44 21
                                (Mk_PMEVTYPER_EL0_Type w__45)))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__52 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             if ((← do
                                  (Halted ())) : Bool)
                             then
                               (do
                                 (HaveEL EL3))
                             else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
          if (w__52 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__59 ← (( do
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
                                let w__56 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__56) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool))) ) :
                SailM Bool )
              if (w__59 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__61 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__61 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__64 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            let w__63 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) : SailM
                              Int )
                            (pure (((21 ≥b w__63) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__64 : Bool)
                      then
                        (do
                          let w__65 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                          if ((! w__65) : Bool)
                          then
                            (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER)))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__67 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__67 : Bool)
                          then
                            (do
                              let w__69 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__69 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__70 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              let w__71 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMEVTYPER_EL0 (vectorUpdate w__70 21
                                (Mk_PMEVTYPER_EL0_Type w__71))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__78 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
              if (w__78 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__80 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__80 : Bool)
                  then
                    (do
                      let w__82 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__82 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__83 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
                      let w__84 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMEVTYPER_EL0 (vectorUpdate w__83 21 (Mk_PMEVTYPER_EL0_Type w__84)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__85 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
                  let w__86 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PMEVTYPER_EL0 (vectorUpdate w__85 21 (Mk_PMEVTYPER_EL0_Type w__86)))
              else (pure (())))))


end ArmFull.Functions
