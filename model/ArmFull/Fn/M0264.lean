module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0066
public import ArmFull.Fn.M0067
public import ArmFull.Fn.M0080
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0167
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
def AMEVCNTR1_EL0_SysRegRead_270554ed1cad7329 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __HAFGRTR_EL2_AMEVCNTR115_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR115_EL0 w__6)
  let w__7 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 15) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__9.EL == EL0) : Bool)
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
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (EL2Enabled ())) : Bool)
                                        then
                                          (do
                                            let w__22 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__23 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__22) +++ (_get_HCR_EL2_Type_TGE
                                                    w__23)) != 0b11#2) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_FGT))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__27 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__27) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR115_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__32 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__32 : Bool)
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
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__35 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__35 15)))))))))
      else
        (do
          let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__36.EL == EL1) : Bool)
          then
            (do
              let w__43 ← (( do
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
              if (w__43 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__52 ← (( do
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
                                        let w__49 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__49) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR115_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__54 : Bool)
                          then
                            (do
                              let w__56 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__56 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__59 ← (( do
                                (pure ((← do
                                      let w__57 ← (( do readReg PSTATE ) : SailM ProcState )
                                      let w__58 ← (( do (IsHighestEL w__57.EL) ) : SailM Bool )
                                      (pure (((! w__58) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__59 : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__60 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__60 15))))))))
          else
            (do
              let w__61 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__61.EL == EL2) : Bool)
              then
                (do
                  let w__68 ← (( do
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
                  if (w__68 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__70 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__70 : Bool)
                      then
                        (do
                          let w__72 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__72 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__75 ← (( do
                            (pure ((← do
                                  let w__73 ← (( do readReg PSTATE ) : SailM ProcState )
                                  let w__74 ← (( do (IsHighestEL w__73.EL) ) : SailM Bool )
                                  (pure (((! w__74) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__75 : Bool)
                          then
                            (do
                              (X_set t 64 (Zeros (n := 64))))
                          else
                            (do
                              let w__76 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (GetElem?.getElem! w__76 15))))))
              else
                (do
                  let w__77 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__77.EL == EL3) : Bool)
                  then
                    (do
                      let w__78 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (GetElem?.getElem! w__78 15)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_34297951a57ea0ef (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __HAFGRTR_EL2_AMEVCNTR18_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR18_EL0 w__6)
  let w__7 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__9.EL == EL0) : Bool)
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
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (EL2Enabled ())) : Bool)
                                        then
                                          (do
                                            let w__22 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__23 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__22) +++ (_get_HCR_EL2_Type_TGE
                                                    w__23)) != 0b11#2) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_FGT))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__27 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__27) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR18_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__32 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__32 : Bool)
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
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__35 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__35 8)))))))))
      else
        (do
          let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__36.EL == EL1) : Bool)
          then
            (do
              let w__43 ← (( do
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
              if (w__43 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__52 ← (( do
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
                                        let w__49 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__49) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR18_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__54 : Bool)
                          then
                            (do
                              let w__56 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__56 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__59 ← (( do
                                (pure ((← do
                                      let w__57 ← (( do readReg PSTATE ) : SailM ProcState )
                                      let w__58 ← (( do (IsHighestEL w__57.EL) ) : SailM Bool )
                                      (pure (((! w__58) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__59 : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__60 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__60 8))))))))
          else
            (do
              let w__61 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__61.EL == EL2) : Bool)
              then
                (do
                  let w__68 ← (( do
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
                  if (w__68 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__70 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__70 : Bool)
                      then
                        (do
                          let w__72 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__72 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__75 ← (( do
                            (pure ((← do
                                  let w__73 ← (( do readReg PSTATE ) : SailM ProcState )
                                  let w__74 ← (( do (IsHighestEL w__73.EL) ) : SailM Bool )
                                  (pure (((! w__74) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__75 : Bool)
                          then
                            (do
                              (X_set t 64 (Zeros (n := 64))))
                          else
                            (do
                              let w__76 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (GetElem?.getElem! w__76 8))))))
              else
                (do
                  let w__77 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__77.EL == EL3) : Bool)
                  then
                    (do
                      let w__78 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (GetElem?.getElem! w__78 8)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def AMEVCNTR1_EL0_SysRegRead_4784c0c277b5428d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __HAFGRTR_EL2_AMEVCNTR13_EL0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMEVCNTR13_EL0 w__6)
  let w__7 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  let __AMCR_EL0_CG1RZ : (BitVec 1) := (_get_AMCR_EL0_Type_CG1RZ w__7)
  let w__8 ← (( do (IsG1ActivityMonitorImplemented 3) ) : SailM Bool )
  if ((! w__8) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__9.EL == EL0) : Bool)
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
                  else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
              then
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__20 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        if ((← do
                                             (EL2Enabled ())) : Bool)
                                        then
                                          (do
                                            let w__22 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            let w__23 ← (( do readReg HCR_EL2 ) : SailM
                                              (BitVec 64) )
                                            (pure (((((_get_HCR_EL2_Type_E2H w__22) +++ (_get_HCR_EL2_Type_TGE
                                                    w__23)) != 0b11#2) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       (IsFeatureImplemented FEAT_FGT))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (pure ((← do
                                        let w__27 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__27) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR13_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__32 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__32 : Bool)
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
                              if ((__AMCR_EL0_CG1RZ == 1#1) : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__35 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__35 3)))))))))
      else
        (do
          let w__36 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((w__36.EL == EL1) : Bool)
          then
            (do
              let w__43 ← (( do
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
              if (w__43 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__45 ← (( do
                    (pure ((← do
                          (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__45 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__52 ← (( do
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
                                        let w__49 ← (( do (HaveEL EL3) ) : SailM Bool )
                                        (pure (((! w__49) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                              else (pure false)) && ((__HAFGRTR_EL2_AMEVCNTR13_EL0 == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__52 : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                      else
                        (do
                          let w__54 ← (( do
                            (pure ((← do
                                  (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__54 : Bool)
                          then
                            (do
                              let w__56 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__56 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              let w__59 ← (( do
                                (pure ((← do
                                      let w__57 ← (( do readReg PSTATE ) : SailM ProcState )
                                      let w__58 ← (( do (IsHighestEL w__57.EL) ) : SailM Bool )
                                      (pure (((! w__58) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                                ) : SailM Bool )
                              if (w__59 : Bool)
                              then
                                (do
                                  (X_set t 64 (Zeros (n := 64))))
                              else
                                (do
                                  let w__60 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                    (Vector (BitVec 64) 16) )
                                  (X_set t 64 (GetElem?.getElem! w__60 3))))))))
          else
            (do
              let w__61 ← (( do readReg PSTATE ) : SailM ProcState )
              if ((w__61.EL == EL2) : Bool)
              then
                (do
                  let w__68 ← (( do
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
                  if (w__68 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__70 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__70 : Bool)
                      then
                        (do
                          let w__72 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__72 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__75 ← (( do
                            (pure ((← do
                                  let w__73 ← (( do readReg PSTATE ) : SailM ProcState )
                                  let w__74 ← (( do (IsHighestEL w__73.EL) ) : SailM Bool )
                                  (pure (((! w__74) : Bool)))) && ((__AMCR_EL0_CG1RZ == 1#1) : Bool)))
                            ) : SailM Bool )
                          if (w__75 : Bool)
                          then
                            (do
                              (X_set t 64 (Zeros (n := 64))))
                          else
                            (do
                              let w__76 ← (( do readReg AMEVCNTR1_EL0 ) : SailM
                                (Vector (BitVec 64) 16) )
                              (X_set t 64 (GetElem?.getElem! w__76 3))))))
              else
                (do
                  let w__77 ← (( do readReg PSTATE ) : SailM ProcState )
                  if ((w__77.EL == EL3) : Bool)
                  then
                    (do
                      let w__78 ← (( do readReg AMEVCNTR1_EL0 ) : SailM (Vector (BitVec 64) 16) )
                      (X_set t 64 (GetElem?.getElem! w__78 3)))
                  else (pure (()))))))


end ArmFull.Functions
