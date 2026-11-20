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
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0069
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
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
def SPMEVFILTR_EL0_SysRegWrite_182705557e8ea81d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__2)
  let w__3 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_EnSPM : (BitVec 1) := (_get_MDSCR_EL1_Type_EnSPM w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__5)
  let w__6 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 : (BitVec 1) := (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 w__6)
  let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__7)
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
              else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__MDSCR_EL1_EnSPM == 0#1) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__25 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE
                                            w__19)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT2))
                           else (pure false)) : Bool)
                      then
                        (do
                          (HaveEL EL3))
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
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
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__34 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__36 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__36 : Bool)
                          then
                            (do
                              let w__38 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__38 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__40 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (pure ((SPMEVFILTR_EL0_set
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__39))
                                  (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__40)) *i 16) +i 3)
                                  w__41))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__48 ← (( do
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
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__48 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__54 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT2))
                           else (pure false)) : Bool)
                      then
                        (do
                          (HaveEL EL3))
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__54 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__58 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__58 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__60 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__60 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__62 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__62 : Bool)
                          then
                            (do
                              let w__64 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__64 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__65 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__66 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__67 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (pure ((SPMEVFILTR_EL0_set
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__65))
                                  (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__66)) *i 16) +i 3)
                                  w__67)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__74 ← (( do
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
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__74 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__76 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
                  if (w__76 : Bool)
                  then
                    (do
                      let w__78 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__78 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__79 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                      let w__80 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                      let w__81 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (pure ((SPMEVFILTR_EL0_set
                          (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__79))
                          (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__80)) *i 16) +i 3) w__81))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__82 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__83 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__84 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (pure ((SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__82))
                      (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__83)) *i 16) +i 3) w__84))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_20aefd1cb9d1a5ad (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__2)
  let w__3 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_EnSPM : (BitVec 1) := (_get_MDSCR_EL1_Type_EnSPM w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__5)
  let w__6 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 : (BitVec 1) := (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 w__6)
  let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__7)
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
              else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__MDSCR_EL1_EnSPM == 0#1) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__25 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE
                                            w__19)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT2))
                           else (pure false)) : Bool)
                      then
                        (do
                          (HaveEL EL3))
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
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
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__34 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__36 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__36 : Bool)
                          then
                            (do
                              let w__38 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__38 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__40 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (pure ((SPMEVFILTR_EL0_set
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__39))
                                  (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__40)) *i 16) +i 13)
                                  w__41))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__48 ← (( do
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
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__48 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__54 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT2))
                           else (pure false)) : Bool)
                      then
                        (do
                          (HaveEL EL3))
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__54 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__58 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__58 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__60 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__60 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__62 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__62 : Bool)
                          then
                            (do
                              let w__64 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__64 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__65 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__66 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__67 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (pure ((SPMEVFILTR_EL0_set
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__65))
                                  (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__66)) *i 16) +i 13)
                                  w__67)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__74 ← (( do
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
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__74 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__76 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
                  if (w__76 : Bool)
                  then
                    (do
                      let w__78 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__78 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__79 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                      let w__80 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                      let w__81 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (pure ((SPMEVFILTR_EL0_set
                          (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__79))
                          (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__80)) *i 16) +i 13) w__81))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__82 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__83 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__84 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (pure ((SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__82))
                      (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__83)) *i 16) +i 13) w__84))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPMEVFILTR_EL0_SysRegWrite_299c129e3abe1407 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__2)
  let w__3 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_EnSPM : (BitVec 1) := (_get_MDSCR_EL1_Type_EnSPM w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__5)
  let w__6 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR2_EL2_nSPMEVTYPERn_EL0 : (BitVec 1) := (_get_HDFGWTR2_EL2_Type_nSPMEVTYPERn_EL0 w__6)
  let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__7)
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
              else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__MDSCR_EL1_EnSPM == 0#1) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__25 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__18) +++ (_get_HCR_EL2_Type_TGE
                                            w__19)) != 0b11#2) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT2))
                           else (pure false)) : Bool)
                      then
                        (do
                          (HaveEL EL3))
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
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
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__34 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__36 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__36 : Bool)
                          then
                            (do
                              let w__38 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__38 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__39 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__40 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (pure ((SPMEVFILTR_EL0_set
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__39))
                                  (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__40)) *i 16) +i 10)
                                  w__41))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__48 ← (( do
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
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__48 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__54 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (EL2Enabled ())) : Bool)
                           then
                             (do
                               (IsFeatureImplemented FEAT_FGT2))
                           else (pure false)) : Bool)
                      then
                        (do
                          (HaveEL EL3))
                      else (pure false)) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__54 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__58 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMEVTYPERn_EL0 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__58 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__60 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__60 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__62 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM
                            Bool )
                          if (w__62 : Bool)
                          then
                            (do
                              let w__64 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__64 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__65 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__66 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                              let w__67 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (pure ((SPMEVFILTR_EL0_set
                                  (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__65))
                                  (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__66)) *i 16) +i 10)
                                  w__67)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__74 ← (( do
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
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__74 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__76 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
                  if (w__76 : Bool)
                  then
                    (do
                      let w__78 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__78 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__79 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                      let w__80 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                      let w__81 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (pure ((SPMEVFILTR_EL0_set
                          (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__79))
                          (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__80)) *i 16) +i 10) w__81))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__82 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__83 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__84 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (pure ((SPMEVFILTR_EL0_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__82))
                      (((BitVec.toNat (_get_SPMSELR_EL0_Type_BANK w__83)) *i 16) +i 10) w__84))))
              else (pure (())))))


end ArmFull.Functions
