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
import ArmFull.Fn.M0043
import ArmFull.Fn.M0049
import ArmFull.Fn.M0069
import ArmFull.Fn.M0072
import ArmFull.Fn.M0073
import ArmFull.Fn.M0074
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0112
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0253
import ArmFull.Fn.M0254
import ArmFull.Fn.M1278

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
def SPMACCESSR_EL1_SysRegWrite_f6ec7d62f3c86b85 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_EnPM2 : (BitVec 1) := (_get_MDCR_EL3_Type_EnPM2 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn2 : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn2 w__3)
  let w__4 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR2_EL2_nSPMACCESSR_EL1 : (BitVec 1) := (_get_HDFGWTR2_EL2_Type_nSPMACCESSR_EL1 w__4)
  let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_EnSPM : (BitVec 1) := (_get_MDCR_EL2_Type_EnSPM w__5)
  let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__17 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT2))
                            else (pure false)) && ((HaveEL EL3) : Bool)))) && ((__SCR_EL3_FGTEn2 == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__21 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (IsFeatureImplemented FEAT_FGT2))
                          else (pure false)) && ((__HDFGWTR2_EL2_nSPMACCESSR_EL1 == 0#1) : Bool))) )
                    : SailM Bool )
                  if (w__21 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__23 ← (( do
                        (pure ((← do
                              (EL2Enabled ())) && ((__MDCR_EL2_EnSPM == 0#1) : Bool))) ) : SailM
                        Bool )
                      if (w__23 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                          then
                            (do
                              let w__25 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__25 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__30 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_NV2 w__27) +++ ((_get_HCR_EL2_Type_NV1
                                              w__28) +++ (_get_HCR_EL2_Type_NV w__29))) == 0b111#3) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__30 : Bool)
                              then
                                (do
                                  let w__31 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  (NVMem_set (BitVec.toNat 0x8E8#12) w__31))
                              else
                                (do
                                  let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg SPMACCESSR_EL1 (Mk_SPMACCESSR_EL1_Type w__32))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__38 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__MDCR_EL3_EnPM2 == 0#1) : Bool))) ) : SailM Bool )
              if (w__38 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_EnPM2 == 0#1)) : Bool)
                  then
                    (do
                      let w__40 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__40 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg SPMACCESSR_EL2 (Mk_SPMACCESSR_EL2_Type w__41))
                      else
                        (do
                          let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg SPMACCESSR_EL1 (Mk_SPMACCESSR_EL1_Type w__42)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPMACCESSR_EL1 (Mk_SPMACCESSR_EL1_Type w__43))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSR_EL1_SysRegWrite_f71c6fe811b4fd71 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__7 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__4) +++ ((_get_HCR_EL2_Type_NV1 w__5) +++ (_get_HCR_EL2_Type_NV
                          w__6))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x160#12) w__8))
          else
            (do
              let w__10 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__11))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__13 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__13) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__15 : Bool)
                  then
                    (do
                      let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__16))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSR_EL2_SysRegWrite_abd009a999e4a431 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__15 ← (( do
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
                if ((← do
                     let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure ((((_get_HCR_EL2_Type_NV w__9) == 0#1) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_NV1 w__11) +++ (_get_HCR_EL2_Type_NV w__12)) == 0b01#2) : Bool))))
                    else (pure false)))
            else (pure false) ) : SailM Bool )
          if (w__15 : Bool)
          then
            (do
              (EXLOCKException ()))
          else
            (do
              let w__20 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__18 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_NV2 w__17) +++ ((_get_HCR_EL2_Type_NV1 w__18) +++ (_get_HCR_EL2_Type_NV
                              w__19))) == 0b011#3) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__20 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__25 ← (( do
                    if ((← do
                         (EL2Enabled ())) : Bool)
                    then
                      (do
                        let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure (((((_get_HCR_EL2_Type_NV2 w__22) +++ ((_get_HCR_EL2_Type_NV1 w__23) +++ (_get_HCR_EL2_Type_NV
                                  w__24))) == 0b111#3) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (NVMem_set (BitVec.toNat 0x160#12) w__26))
                  else
                    (do
                      let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__27)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__35 ← (( do
                (pure ((← do
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
                               let w__31 ← (( do (Halted ()) ) : SailM Bool )
                               (pure (((! w__31) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__33.EXLOCK == 1#1) : Bool))))
                      else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
              if (w__35 : Bool)
              then
                (do
                  (EXLOCKException ()))
              else
                (do
                  if ((__HCR_EL2_E2H == 1#1) : Bool)
                  then
                    (do
                      let w__36 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg SPSR_EL2 (Mk_SPSR_EL2_Type w__36))
                  else
                    (do
                      let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__37))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPSR_EL1 (Mk_SPSR_EL1_Type w__38))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SP_EL1_SysRegWrite_ef3afaab001d7071 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__5 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__3) +++ (_get_HCR_EL2_Type_NV w__4)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x240#12) w__6))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg SP_EL1 w__9)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SP_EL1 w__10)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TCR2_EL1_SysRegWrite_8d0ce9228b7cb5c8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TCR2En : (BitVec 1) := (_get_SCR_EL3_Type_TCR2En w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__6) +++ ((_get_HCR_EL2_Type_NV1 w__7) +++ (_get_HCR_EL2_Type_NV
                          w__8))) == 0b101#3) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x270#12) w__10))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_TCR2En == 0#1) : Bool))) ) : SailM Bool
                    )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
                      then
                        (do
                          let w__20 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__20 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__21 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg TCR2_EL1 (Mk_TCR2_EL1_Type w__21))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__25 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__23) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__25 : Bool)
                  then
                    (do
                      let w__26 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg TCR2_EL1 (Mk_TCR2_EL1_Type w__26))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TCR2_EL2_SysRegWrite_c04bf19f053d56ef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TCR2En : (BitVec 1) := (_get_SCR_EL3_Type_TCR2En w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_TCR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_TCR_EL1 w__5)
  let w__6 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_TCR2En : (BitVec 1) := (_get_HCRX_EL2_Type_TCR2En w__6)
  let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
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
                  else (pure false)) && ((__SCR_EL3_TCR2En == 0#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGWTR_EL2_TCR_EL1 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__24 ← (( do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            (pure ((← do
                                  let w__22 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
                                  (pure (((! w__22) : Bool)))) || ((__HCRX_EL2_TCR2En == 0#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__24 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
                          then
                            (do
                              let w__26 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__26 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__31 ← (( do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_NV2 w__28) +++ ((_get_HCR_EL2_Type_NV1
                                              w__29) +++ (_get_HCR_EL2_Type_NV w__30))) == 0b111#3) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__31 : Bool)
                              then
                                (do
                                  let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  (NVMem_set (BitVec.toNat 0x270#12) w__32))
                              else
                                (do
                                  let w__33 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  writeReg TCR2_EL1 (Mk_TCR2_EL1_Type w__33))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__39 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_TCR2En == 0#1) : Bool))) ) : SailM Bool )
              if (w__39 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_TCR2En == 0#1)) : Bool)
                  then
                    (do
                      let w__41 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__41 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg TCR2_EL2 (Mk_TCR2_EL2_Type w__42))
                      else
                        (do
                          let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg TCR2_EL1 (Mk_TCR2_EL1_Type w__43)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__44 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg TCR2_EL1 (Mk_TCR2_EL1_Type w__44))
              else (pure (())))))


end ArmFull.Functions
