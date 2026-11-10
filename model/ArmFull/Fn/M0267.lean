import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0047
import ArmFull.Fn.M0058
import ArmFull.Fn.M0066
import ArmFull.Fn.M0080
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
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
def AMEVCNTR1_EL0_SysRegRead_7638ccb047de09f8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__0)
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__1)
  let w__2 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVCNTR11_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR11_EL0 w__6)
  let w__7 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 1) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__9.EL == EL0) : Bool)
      then
        (do
          let w__15 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__15 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__27 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__21 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__22 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__21) +++ (_get_HCR_EL2_Type_TGE
                                                     w__22)) != 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        (IsFeatureImplemented FEAT_FGT))
                                    else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR11_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__27 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              let w__29 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__29 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__30 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__30 1)))))))))
      else
        (do
          let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__31.EL == EL1) : Bool)
          then
            (do
              let w__37 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__39 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__39 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (IsFeatureImplemented FEAT_FGT))
                                    else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR11_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              let w__46 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__46 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      let w__47 ← (( do readReg PSTATE ) : SailM ProcState )
                                      (pure (((! (IsHighestEL w__47.EL)) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__48 : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__49 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__49 1))))))))
          else
            (do
              let w__50 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__50.EL == EL2) : Bool)
              then
                (do
                  let w__56 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__56 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__58 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__60 ← (( do
                            (pure ((← do
                                  let w__59 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((! (IsHighestEL w__59.EL)) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__60 : Bool)
                          then
                            (do
                              (X_set t 64 (Zeros (n := 64))))
                          else
                            (do
                              let w__61 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (GetElem?.getElem! w__61 1))))))
              else
                (do
                  let w__62 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__62.EL == EL3) : Bool)
                  then
                    (do
                      let w__63 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (GetElem?.getElem! w__63 1)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_8db93fe7c2515bf5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__0)
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__1)
  let w__2 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVCNTR14_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR14_EL0 w__6)
  let w__7 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__9.EL == EL0) : Bool)
      then
        (do
          let w__15 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__15 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__27 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__21 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__22 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__21) +++ (_get_HCR_EL2_Type_TGE
                                                     w__22)) != 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        (IsFeatureImplemented FEAT_FGT))
                                    else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR14_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__27 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              let w__29 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__29 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__30 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__30 4)))))))))
      else
        (do
          let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__31.EL == EL1) : Bool)
          then
            (do
              let w__37 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__39 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__39 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (IsFeatureImplemented FEAT_FGT))
                                    else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR14_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              let w__46 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__46 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      let w__47 ← (( do readReg PSTATE ) : SailM ProcState )
                                      (pure (((! (IsHighestEL w__47.EL)) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__48 : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__49 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__49 4))))))))
          else
            (do
              let w__50 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__50.EL == EL2) : Bool)
              then
                (do
                  let w__56 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__56 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__58 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__60 ← (( do
                            (pure ((← do
                                  let w__59 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((! (IsHighestEL w__59.EL)) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__60 : Bool)
                          then
                            (do
                              (X_set t 64 (Zeros (n := 64))))
                          else
                            (do
                              let w__61 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (GetElem?.getElem! w__61 4))))))
              else
                (do
                  let w__62 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__62.EL == EL3) : Bool)
                  then
                    (do
                      let w__63 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (GetElem?.getElem! w__63 4)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_9f7317df01644a85 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__0)
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__1)
  let w__2 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__3)
  let w__4 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__5)
  let w__6 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVCNTR111_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR111_EL0 w__6)
  let w__7 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__9.EL == EL0) : Bool)
      then
        (do
          let w__15 ← (( do
            (pure ((← do
                  if ((← do
                       (pure ((← do
                             (pure ((← do
                                   (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__15 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__27 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         if ((← do
                                              (EL2Enabled ())) : Bool)
                                         then
                                           (do
                                             let w__21 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             let w__22 ← (( do readReg HCR_EL2 ) : SailM
                                               (BitVec 64) )
                                             (pure (((((_get_HCR_EL2_Type_E2H w__21) +++ (_get_HCR_EL2_Type_TGE
                                                     w__22)) != 0b11#2) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        (IsFeatureImplemented FEAT_FGT))
                                    else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR111_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__27 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              let w__29 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__29 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__30 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__30 11)))))))))
      else
        (do
          let w__31 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__31.EL == EL1) : Bool)
          then
            (do
              let w__37 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__37 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__39 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__39 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__44 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        (IsFeatureImplemented FEAT_FGT))
                                    else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HAFGRTR_EL2_AMEVCNTR111_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                          then
                            (do
                              let w__46 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__46 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__48 ← (( do
                                (pure ((← do
                                      let w__47 ← (( do readReg PSTATE ) : SailM ProcState )
                                      (pure (((! (IsHighestEL w__47.EL)) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__48 : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__49 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__49 11))))))))
          else
            (do
              let w__50 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__50.EL == EL2) : Bool)
              then
                (do
                  let w__56 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__56 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__CPTR_EL3_TAM == 1#1)) : Bool)
                      then
                        (do
                          let w__58 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__58 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__60 ← (( do
                            (pure ((← do
                                  let w__59 ← (( do readReg PSTATE ) : SailM ProcState )
                                  (pure (((! (IsHighestEL w__59.EL)) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__60 : Bool)
                          then
                            (do
                              (X_set t 64 (Zeros (n := 64))))
                          else
                            (do
                              let w__61 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (GetElem?.getElem! w__61 11))))))
              else
                (do
                  let w__62 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__62.EL == EL3) : Bool)
                  then
                    (do
                      let w__63 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (GetElem?.getElem! w__63 11)))
                  else (pure (()))))))


end ArmFull.Functions
