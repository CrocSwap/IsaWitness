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
public import ArmFull.Fn.M0071
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
def PMXEVCNTR_EL0_SysRegWrite_d3c59aa061d63534 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __HDFGWTR_EL2_PMEVCNTRn_EL0 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMEVCNTRn_EL0 w__6)
  let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TPM : (BitVec 1) := (_get_MDCR_EL2_Type_TPM w__7)
  let w__8 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
  if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__8)) ≥b 31) : Bool)
  then
    (do
      let w__9 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
      if (w__9 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure ((ConstrainUnpredictableProcedure Unpredictable_PMUEVENTCOUNTER))))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__16 ← (( do
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
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__23 ← (( do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__18 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__19 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__18) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__19)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__21 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__21) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))) )
                : SailM Bool )
              if (w__23 : Bool)
              then
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__35 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__27) +++ (_get_HCR_EL2_Type_TGE
                                                w__28)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__32 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__32) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGWTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__35 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__41 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__39 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                let w__40 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) :
                                  SailM Int )
                                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__39)) ≥b w__40) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__41 : Bool)
                          then
                            (do
                              let w__42 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                              if ((! w__42) : Bool)
                              then
                                (pure ((ConstrainUnpredictableProcedure
                                    Unpredictable_PMUEVENTCOUNTER)))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__44 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__44 : Bool)
                              then
                                (do
                                  let w__46 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__46 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__47 ← (( do readReg PMEVCNTR_EL0 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  let w__48 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                  let w__49 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg PMEVCNTR_EL0 (vectorUpdate w__47
                                    (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__48)) w__49))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__56 ← (( do
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
              if (w__56 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__63 ← (( do
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
                                    let w__60 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__60) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGWTR_EL2_PMEVCNTRn_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__63 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__65 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__65 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__69 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__67 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                let w__68 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) :
                                  SailM Int )
                                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__67)) ≥b w__68) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__69 : Bool)
                          then
                            (do
                              let w__70 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                              if ((! w__70) : Bool)
                              then
                                (pure ((ConstrainUnpredictableProcedure
                                    Unpredictable_PMUEVENTCOUNTER)))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__72 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__72 : Bool)
                              then
                                (do
                                  let w__74 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__74 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__75 ← (( do readReg PMEVCNTR_EL0 ) : SailM
                                    (Vector (BitVec 64) 32) )
                                  let w__76 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                  let w__77 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg PMEVCNTR_EL0 (vectorUpdate w__75
                                    (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__76)) w__77)))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__84 ← (( do
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
                  if (w__84 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__86 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__86 : Bool)
                      then
                        (do
                          let w__88 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__88 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__89 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32)
                            )
                          let w__90 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                          let w__91 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PMEVCNTR_EL0 (vectorUpdate w__89
                            (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__90)) w__91))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__92 ← (( do readReg PMEVCNTR_EL0 ) : SailM (Vector (BitVec 64) 32) )
                      let w__93 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                      let w__94 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMEVCNTR_EL0 (vectorUpdate w__92
                        (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__93)) w__94))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def PMXEVTYPER_EL0_SysRegWrite_1b2a1f5e5253d48b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__18 ← (( do
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
          if (w__18 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__25 ← (( do
                if ((← do
                     if ((← do
                          (IsFeatureImplemented FEAT_PMUv3p9)) : Bool)
                     then
                       (do
                         let w__20 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         let w__21 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                         (pure (((((_get_PMUSERENR_EL0_Type_UEN w__20) +++ (_get_PMUSERENR_EL0_Type_EN
                                 w__21)) == 0b00#2) : Bool))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__23 ← (( do (IsFeatureImplemented FEAT_PMUv3p9) ) : SailM Bool )
                          (pure (((! w__23) : Bool)))) && ((__PMUSERENR_EL0_EN == 0#1) : Bool)))) )
                : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  let w__27 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__37 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__29) +++ (_get_HCR_EL2_Type_TGE
                                                w__30)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__34 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__34) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__37 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__39 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__39 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__45 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__41 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                     (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__41)) != 31) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__43 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                let w__44 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) :
                                  SailM Int )
                                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__43)) ≥b w__44) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__45 : Bool)
                          then
                            (do
                              let w__46 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                              if ((! w__46) : Bool)
                              then
                                (pure ((ConstrainUnpredictableProcedure
                                    Unpredictable_PMUEVENTCOUNTER)))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__48 : Bool)
                              then
                                (do
                                  let w__50 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__50 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__51 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                  if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__51)) == 31) : Bool)
                                  then
                                    (do
                                      let w__52 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type w__52))
                                  else
                                    (do
                                      let w__53 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                        (Vector (BitVec 64) 32) )
                                      let w__54 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                      let w__55 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg PMEVTYPER_EL0 (vectorUpdate w__53
                                        (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__54))
                                        (Mk_PMEVTYPER_EL0_Type w__55))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__62 ← (( do
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
              if (w__62 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__69 ← (( do
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
                                    let w__66 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__66) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HDFGWTR_EL2_PMEVTYPERn_EL0 == 1#1) : Bool))) ) :
                    SailM Bool )
                  if (w__69 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__71 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_TPM == 1#1) : Bool))) ) : SailM Bool
                        )
                      if (w__71 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__77 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__73 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                     (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__73)) != 31) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__75 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                let w__76 ← (( do (AArch64_GetNumEventCountersAccessible ()) ) :
                                  SailM Int )
                                (pure ((((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__75)) ≥b w__76) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__77 : Bool)
                          then
                            (do
                              let w__78 ← (( do (IsFeatureImplemented FEAT_FGT) ) : SailM Bool )
                              if ((! w__78) : Bool)
                              then
                                (pure ((ConstrainUnpredictableProcedure
                                    Unpredictable_PMUEVENTCOUNTER)))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__80 ← (( do
                                (pure ((← do
                                      (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__80 : Bool)
                              then
                                (do
                                  let w__82 ← (( do
                                    (pure ((← do
                                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM
                                    Bool )
                                  if (w__82 : Bool)
                                  then sailThrow ((Error_Undefined ()))
                                  else
                                    (do
                                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                              else
                                (do
                                  let w__83 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                  if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__83)) == 31) : Bool)
                                  then
                                    (do
                                      let w__84 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type w__84))
                                  else
                                    (do
                                      let w__85 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                        (Vector (BitVec 64) 32) )
                                      let w__86 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                                      let w__87 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                      writeReg PMEVTYPER_EL0 (vectorUpdate w__85
                                        (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__86))
                                        (Mk_PMEVTYPER_EL0_Type w__87)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__94 ← (( do
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
                  if (w__94 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__96 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__MDCR_EL3_TPM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__96 : Bool)
                      then
                        (do
                          let w__98 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__98 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__99 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                          if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__99)) == 31) : Bool)
                          then
                            (do
                              let w__100 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type w__100))
                          else
                            (do
                              let w__101 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                                (Vector (BitVec 64) 32) )
                              let w__102 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__103 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMEVTYPER_EL0 (vectorUpdate w__101
                                (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__102))
                                (Mk_PMEVTYPER_EL0_Type w__103))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__104 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                      if (((BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__104)) == 31) : Bool)
                      then
                        (do
                          let w__105 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PMCCFILTR_EL0 (Mk_PMCCFILTR_EL0_Type w__105))
                      else
                        (do
                          let w__106 ← (( do readReg PMEVTYPER_EL0 ) : SailM
                            (Vector (BitVec 64) 32) )
                          let w__107 ← (( do readReg PMSELR_EL0 ) : SailM (BitVec 64) )
                          let w__108 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PMEVTYPER_EL0 (vectorUpdate w__106
                            (BitVec.toNat (_get_PMSELR_EL0_Type_SEL w__107))
                            (Mk_PMEVTYPER_EL0_Type w__108))))
                  else (pure (()))))))


end ArmFull.Functions
