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
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0069
import ArmFull.Fn.M0073
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0112
import ArmFull.Fn.M0146
import ArmFull.Fn.M0156
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
import ArmFull.Fn.M0253
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
def SPMSELR_EL0_SysRegWrite_3811b80bc21b4614 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __HDFGWTR2_EL2_nSPMSELR_EL0 : (BitVec 1) := (_get_HDFGWTR2_EL2_Type_nSPMSELR_EL0 w__6)
  let w__7 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         (pure ((← do
                               (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__MDSCR_EL1_EnSPM == 0#1) : Bool)
          then
            (do
              let w__15 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__23 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__17) +++ (_get_HCR_EL2_Type_TGE
                                             w__18)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT2))
                            else (pure false)) && ((HaveEL EL3) : Bool)))) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__23 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__30 ← (( do
                    (pure ((← do
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
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMSELR_EL0 == 0#1) : Bool))) ) :
                    SailM Bool )
                  if (w__30 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__32 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__32 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                          then
                            (do
                              let w__34 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__34 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__35 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg SPMSELR_EL0 (Mk_SPMSELR_EL0_Type w__35))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__41 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__41 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__46 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT2))
                            else (pure false)) && ((HaveEL EL3) : Bool)))) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__46 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__50 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMSELR_EL0 == 0#1) : Bool))) ) :
                    SailM Bool )
                  if (w__50 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__52 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                          then
                            (do
                              let w__54 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__54 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__55 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg SPMSELR_EL0 (Mk_SPMSELR_EL0_Type w__55)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__61 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__61 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                  then
                    (do
                      let w__63 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__63 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__64 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg SPMSELR_EL0 (Mk_SPMSELR_EL0_Type w__64))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__65 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPMSELR_EL0 (Mk_SPMSELR_EL0_Type w__65))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSR_EL2_SysRegWrite_5e3ca78864ff5189 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__11 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 if ((← do
                                      (IsFeatureImplemented FEAT_GCS)) : Bool)
                                 then
                                   (do
                                     (GetCurrentEXLOCKEN ()))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__5 ← (( do (Halted ()) ) : SailM Bool )
                                (pure (((! w__5) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__7.EXLOCK == 1#1) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      (EL2Enabled ()))
                  else (pure false)) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (EXLOCKException ()))
          else
            (do
              let w__15 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__13) +++ (_get_HCR_EL2_Type_NV w__14)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__16))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else sailThrow ((Error_Undefined ())))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__25 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               (IsFeatureImplemented FEAT_GCS)) : Bool)
                          then
                            (do
                              (GetCurrentEXLOCKEN ()))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__22 ← (( do (Halted ()) ) : SailM Bool )
                         (pure (((! w__22) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__24.EXLOCK == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (EXLOCKException ()))
              else
                (do
                  let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_EL2 (Mk_SPSR_EL2_Type w__26)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_EL2 (Mk_SPSR_EL2_Type w__27))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSR_EL3_SysRegWrite_456470f5b76b34d3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EXLOCK : (BitVec 1) := w__1.EXLOCK
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (IsFeatureImplemented FEAT_GCS)) : Bool)
                               then
                                 (do
                                   (GetCurrentEXLOCKEN ()))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__5 ← (( do (Halted ()) ) : SailM Bool )
                              (pure (((! w__5) : Bool))))
                          else (pure false)) && ((__PSTATE_EXLOCK == 1#1) : Bool))) ) : SailM Bool )
                  if (w__7 : Bool)
                  then
                    (do
                      (EXLOCKException ()))
                  else
                    (do
                      let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg SPSR_EL3 (Mk_SPSR_EL3_Type w__8)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSR_abt_SysRegWrite_fcfb847bea953cff (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg SPSR_abt (Mk_SPSR_abt_Type w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_abt (Mk_SPSR_abt_Type w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSR_fiq_SysRegWrite_2563b670f1657883 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg SPSR_fiq (Mk_SPSR_fiq_Type w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_fiq (Mk_SPSR_fiq_Type w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSR_irq_SysRegWrite_ce481d2491908c8e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg SPSR_irq (Mk_SPSR_irq_Type w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_irq (Mk_SPSR_irq_Type w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSR_und_SysRegWrite_684160009ec60b5e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg SPSR_und (Mk_SPSR_und_Type w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_und (Mk_SPSR_und_Type w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SVCR_SysRegWrite_6af153139ced98f4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_ESM : (BitVec 1) := (_get_CPTR_EL3_Type_ESM w__2)
  let w__3 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  let __CPACR_EL1_SMEN : (BitVec 2) := (_get_CPACR_EL1_Type_SMEN w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_SMEN : (BitVec 2) := (_get_CPTR_EL2_Type_SMEN w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__6)
  let w__7 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TSM : (BitVec 1) := (_get_CPTR_EL2_Type_TSM w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   (pure ((← do
                         (pure ((← do
                               (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
              then
                (do
                  (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
              else (pure false)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__18 ← (( do
            (pure ((← do
                  let w__17 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) == 0b11#2) : Bool))))
                    else (pure false) ) : SailM Bool )
                  (pure (((! w__17) : Bool)))) && ((__CPACR_EL1_SMEN != 0b11#2) : Bool))) ) : SailM
            Bool )
          if (w__18 : Bool)
          then
            (do
              let w__20 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x1D#8))))
          else
            (do
              let w__25 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__22) +++ (_get_HCR_EL2_Type_TGE w__23)) == 0b11#2) : Bool))))
                      else (pure false)) && ((__CPTR_EL2_SMEN != 0b11#2) : Bool))) ) : SailM Bool )
              if (w__25 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
              else
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (EL2Enabled ())) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && (let b__3 :=
                          __CPTR_EL2_SMEN
                        (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                        then true
                        else false : Bool)))) ) : SailM Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                  else
                    (do
                      let w__31 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (EL2Enabled ())) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CPTR_EL2_TSM == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__31 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              let w__33 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__33 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))))
                          else
                            (do
                              let w__34 ← (( do (X_read t 32) ) : SailM (BitVec 32) )
                              (SetPSTATE_SVCR w__34))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__40 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool )
          if (w__40 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((let b__2 := __CPACR_EL1_SMEN
                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 0 0)) == (0#1 : (BitVec 1))) : Bool)
                 then true
                 else false : Bool)) : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x1D#8)))
              else
                (do
                  let w__43 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (EL2Enabled ())) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CPTR_EL2_TSM == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__43 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                  else
                    (do
                      let w__46 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    (EL2Enabled ())) && ((__HCR_EL2_E2H == 1#1) : Bool)))) && (let b__1 :=
                              __CPTR_EL2_SMEN
                            (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                            then true
                            else false : Bool)))) ) : SailM Bool )
                      if (w__46 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__48 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))))
                          else
                            (do
                              let w__49 ← (( do (X_read t 32) ) : SailM (BitVec 32) )
                              (SetPSTATE_SVCR w__49)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
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
                      else (pure false)) && ((__CPTR_EL3_ESM == 0#1) : Bool))) ) : SailM Bool )
              if (w__55 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TSM == 1#1)) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_SMEN
                           (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool))) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x1D#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_ESM == 0#1)) : Bool)
                          then
                            (do
                              let w__57 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__57 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8))))
                          else
                            (do
                              let w__58 ← (( do (X_read t 32) ) : SailM (BitVec 32) )
                              (SetPSTATE_SVCR w__58))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_ESM == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x1D#8)))
                  else
                    (do
                      let w__59 ← (( do (X_read t 32) ) : SailM (BitVec 32) )
                      (SetPSTATE_SVCR w__59)))
              else (pure (())))))


end ArmFull.Functions
