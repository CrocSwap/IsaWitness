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
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0067
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
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
def AMEVTYPER1_EL0_SysRegRead_9fc9c2c315f2eddc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__2)
  let w__3 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVTYPER112_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVTYPER112_EL0 w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 12) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__15 ← (( do
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
                      let w__29 ← (( do
                        (pure ((← do
                              if ((← do
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
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__26 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__26) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVTYPER112_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__31 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__31 : Bool)
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
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__34 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__34 12)))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__41 ← (( do
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
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__43 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__43 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__50 ← (( do
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
                                        let w__47 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__47) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVTYPER112_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__52 : Bool)
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
                              let w__55 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__55 12))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
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
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__62 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__64 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__64 : Bool)
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
                          let w__67 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                            (Vector (BitVec 64) 16) )
                          (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__67 12))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__68 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__68 12))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_a53d76115c4ce8dd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__2)
  let w__3 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVTYPER18_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVTYPER18_EL0 w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__15 ← (( do
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
                      let w__29 ← (( do
                        (pure ((← do
                              if ((← do
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
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__26 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__26) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVTYPER18_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__31 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__31 : Bool)
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
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__34 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__34 8)))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__41 ← (( do
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
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__43 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__43 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__50 ← (( do
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
                                        let w__47 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__47) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVTYPER18_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__52 : Bool)
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
                              let w__55 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__55 8))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
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
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__62 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__64 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__64 : Bool)
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
                          let w__67 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                            (Vector (BitVec 64) 16) )
                          (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__67 8))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__68 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__68 8))))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_EL0_SysRegRead_ace2a16645ca5a01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TAM : (BitVec 1) := (_get_CPTR_EL3_Type_TAM w__2)
  let w__3 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  let __AMUSERENR_EL0_EN : (BitVec 1) := (_get_AMUSERENR_EL0_Type_EN w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TAM : (BitVec 1) := (_get_CPTR_EL2_Type_TAM w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__6)
  let w__7 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HAFGRTR_EL2_AMEVTYPER113_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVTYPER113_EL0 w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__15 ← (( do
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
                      let w__29 ← (( do
                        (pure ((← do
                              if ((← do
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
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__26 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__26) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVTYPER113_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__31 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__31 : Bool)
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
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__34 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__34 13)))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__41 ← (( do
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
                      else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__41 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__43 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__43 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__50 ← (( do
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
                                        let w__47 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__47) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVTYPER113_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__50 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__52 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__52 : Bool)
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
                              let w__55 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__55 13))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
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
                          else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__62 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__64 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__64 : Bool)
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
                          let w__67 ← (( do readReg AMEVTYPER1_EL0 ) : SailM
                            (Vector (BitVec 64) 16) )
                          (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__67 13))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__68 ← (( do readReg AMEVTYPER1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (__get_AMEVTYPER1_EL0 (GetElem?.getElem! w__68 13))))
                  else (pure (()))))))


end ArmFull.Functions
