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
import ArmFull.Fn.M0040
import ArmFull.Fn.M0049
import ArmFull.Fn.M0064
import ArmFull.Fn.M0073
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
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
def PIRE0_EL2_SysRegWrite_13593dc3e37a5186 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__7 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_NV2 w__5) +++ (_get_HCR_EL2_Type_NV w__6)) == 0b11#2) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (NVMem_set (BitVec.toNat 0x298#12) w__8))
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
              let w__16 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      let w__18 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__18 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__19 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PIRE0_EL2 (Mk_PIRE0_EL2_Type w__19))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__20 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PIRE0_EL2 (Mk_PIRE0_EL2_Type w__20))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PIRE0_EL2_SysRegWrite_8aee2c676081a490 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_PIEn : (BitVec 1) := (_get_SCR_EL3_Type_PIEn w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_nPIRE0_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_nPIRE0_EL1 w__5)
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
                  else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGWTR_EL2_nPIRE0_EL1 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
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
                          let w__26 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_NV2 w__23) +++ ((_get_HCR_EL2_Type_NV1
                                          w__24) +++ (_get_HCR_EL2_Type_NV w__25))) == 0b111#3) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__26 : Bool)
                          then
                            (do
                              let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (NVMem_set (BitVec.toNat 0x290#12) w__27))
                          else
                            (do
                              let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PIRE0_EL1 (Mk_PIRE0_EL1_Type w__28)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__36 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PIRE0_EL2 (Mk_PIRE0_EL2_Type w__37))
                      else
                        (do
                          let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PIRE0_EL1 (Mk_PIRE0_EL1_Type w__38)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PIRE0_EL1 (Mk_PIRE0_EL1_Type w__39))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PIR_EL1_SysRegWrite_1431f0a180293b57 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_PIEn : (BitVec 1) := (_get_SCR_EL3_Type_PIEn w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_nPIR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_nPIR_EL1 w__5)
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
                  else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGWTR_EL2_nPIR_EL1 == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
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
                          let w__26 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_NV2 w__23) +++ ((_get_HCR_EL2_Type_NV1
                                          w__24) +++ (_get_HCR_EL2_Type_NV w__25))) == 0b111#3) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__26 : Bool)
                          then
                            (do
                              let w__27 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (NVMem_set (BitVec.toNat 0x2A0#12) w__27))
                          else
                            (do
                              let w__28 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PIR_EL1 (Mk_PIR_EL1_Type w__28)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__34 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__34 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
                  then
                    (do
                      let w__36 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__36 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      if ((__HCR_EL2_E2H == 1#1) : Bool)
                      then
                        (do
                          let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PIR_EL2 (Mk_PIR_EL2_Type w__37))
                      else
                        (do
                          let w__38 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg PIR_EL1 (Mk_PIR_EL1_Type w__38)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__39 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PIR_EL1 (Mk_PIR_EL1_Type w__39))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PIR_EL1_SysRegWrite_da3aa8710c2ede05 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_PIEn : (BitVec 1) := (_get_SCR_EL3_Type_PIEn w__4)
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
              (NVMem_set (BitVec.toNat 0x2A0#12) w__10))
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
                          else (pure false)) && ((__SCR_EL3_PIEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_PIEn == 0#1)) : Bool)
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
                          writeReg PIR_EL1 (Mk_PIR_EL1_Type w__21))))
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
                      writeReg PIR_EL1 (Mk_PIR_EL1_Type w__26))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PMBLIMITR_EL1_SysRegWrite_9f8902df06f4b415 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_NSPBE : (BitVec 1) := (_get_MDCR_EL3_Type_NSPBE w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NSE : (BitVec 1) := (_get_SCR_EL3_Type_NSE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HDFGWTR_EL2_PMBLIMITR_EL1 : (BitVec 1) := (_get_HDFGWTR_EL2_Type_PMBLIMITR_EL1 w__4)
  let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_E2PB : (BitVec 2) := (_get_MDCR_EL2_Type_E2PB w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__19 ← (( do
            if ((← do
                 if ((← do
                      if ((← do
                           (pure ((← do
                                 (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                      then
                        (do
                          let w__8 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                          (pure ((((_get_EDSCR_Type_SDD w__8) == 1#1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                 else (pure false)) : Bool)
            then
              (do
                if ((← do
                     if ((← do
                          let w__12 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                          (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                  (_get_MDCR_EL3_Type_NSPB w__12) 0)])) == 0#1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__13 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                         let w__14 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 (_get_MDCR_EL3_Type_NSPB w__13) 1)])) != (_get_SCR_EL3_Type_NS
                               w__14)) : Bool))))) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
            else (pure false) ) : SailM Bool )
          if (w__19 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__24 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HDFGWTR_EL2_PMBLIMITR_EL1 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__24 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && (let b__0 := __MDCR_EL2_E2PB
                        (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                        then true
                        else false : Bool)))) ) : SailM Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__34 ← (( do
                        if (((HaveEL EL3) : Bool) : Bool)
                        then
                          (do
                            if ((← do
                                 if ((← do
                                      let w__27 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                      (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                              (_get_MDCR_EL3_Type_NSPB w__27) 0)])) == 0#1) : Bool)))) : Bool)
                                 then (pure true)
                                 else
                                   (do
                                     let w__28 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                     let w__29 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                     (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             (_get_MDCR_EL3_Type_NSPB w__28) 1)])) != (_get_SCR_EL3_Type_NS
                                           w__29)) : Bool))))) : Bool)
                            then (pure true)
                            else
                              (do
                                (pure ((← do
                                      (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                        else (pure false) ) : SailM Bool )
                      if (w__34 : Bool)
                      then
                        (do
                          let w__37 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__36 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__36) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__37 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__41 ← (( do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                (pure (((((_get_HCR_EL2_Type_NV2 w__39) +++ (_get_HCR_EL2_Type_NV
                                        w__40)) == 0b11#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__41 : Bool)
                          then
                            (do
                              let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              (NVMem_set (BitVec.toNat 0x800#12) w__42))
                          else
                            (do
                              let w__43 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg PMBLIMITR_EL1 (Mk_PMBLIMITR_EL1_Type w__43)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__57 ← (( do
                if ((← do
                     if ((← do
                          if ((← do
                               (pure ((← do
                                     (Halted ())) && ((HaveEL EL3) : Bool)))) : Bool)
                          then
                            (do
                              let w__46 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                              (pure ((((_get_EDSCR_Type_SDD w__46) == 1#1) : Bool))))
                          else (pure false)) : Bool)
                     then
                       (do
                         (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                     else (pure false)) : Bool)
                then
                  (do
                    if ((← do
                         if ((← do
                              let w__50 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                              (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                      (_get_MDCR_EL3_Type_NSPB w__50) 0)])) == 0#1) : Bool)))) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__51 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                             let w__52 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     (_get_MDCR_EL3_Type_NSPB w__51) 1)])) != (_get_SCR_EL3_Type_NS
                                   w__52)) : Bool))))) : Bool)
                    then (pure true)
                    else
                      (do
                        (pure ((← do
                              (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                else (pure false) ) : SailM Bool )
              if (w__57 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__65 ← (( do
                    if (((HaveEL EL3) : Bool) : Bool)
                    then
                      (do
                        if ((← do
                             if ((← do
                                  let w__58 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                  (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                          (_get_MDCR_EL3_Type_NSPB w__58) 0)])) == 0#1) : Bool)))) : Bool)
                             then (pure true)
                             else
                               (do
                                 let w__59 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                                 let w__60 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         (_get_MDCR_EL3_Type_NSPB w__59) 1)])) != (_get_SCR_EL3_Type_NS
                                       w__60)) : Bool))))) : Bool)
                        then (pure true)
                        else
                          (do
                            (pure ((← do
                                  (IsFeatureImplemented FEAT_RME)) && ((__MDCR_EL3_NSPBE != __SCR_EL3_NSE) : Bool)))))
                    else (pure false) ) : SailM Bool )
                  if (w__65 : Bool)
                  then
                    (do
                      let w__68 ← (( do
                        if ((← do
                             (Halted ())) : Bool)
                        then
                          (do
                            let w__67 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_EDSCR_Type_SDD w__67) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__68 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__69 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg PMBLIMITR_EL1 (Mk_PMBLIMITR_EL1_Type w__69))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__70 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PMBLIMITR_EL1 (Mk_PMBLIMITR_EL1_Type w__70))
              else (pure (())))))


end ArmFull.Functions
