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
public import ArmFull.Fn.M0066
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
def AMCG1IDR_EL0_SysRegRead_0dbcfa52be452f1c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__12 ← (( do
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
      if (w__12 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              let w__14 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
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
                      let w__21 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCG1IDR_EL0 w__21)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__28 ← (( do
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
          if (w__28 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__30 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__30 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__34 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__35 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCG1IDR_EL0 w__35))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__42 ← (( do
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
              if (w__42 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then
                    (do
                      let w__46 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__46 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__47 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCG1IDR_EL0 w__47)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__48 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_AMCG1IDR_EL0 w__48)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMCGCR_EL0_SysRegRead_06267c37ea5fd2cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__12 ← (( do
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
      if (w__12 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
          then
            (do
              let w__14 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__16 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
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
                      let w__21 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCGCR_EL0 w__21)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__28 ← (( do
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
          if (w__28 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__30 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__30 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      let w__34 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__34 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__35 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCGCR_EL0 w__35))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__42 ← (( do
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
              if (w__42 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__44 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__44 : Bool)
                  then
                    (do
                      let w__46 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__46 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__47 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCGCR_EL0 w__47)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__48 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_AMCGCR_EL0 w__48)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMCNTENCLR0_EL0_SysRegRead_21074600beb00df2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __HAFGRTR_EL2_AMCNTEN0 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMCNTEN0 w__7)
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
              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
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
              let w__18 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__18 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                                w__21)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__25 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__25) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HAFGRTR_EL2_AMCNTEN0 == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          let w__32 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__32 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__33 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_AMCNTENCLR0_EL0 w__33))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__40 ← (( do
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
          if (w__40 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__42 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__42 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__49 ← (( do
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
                                    let w__46 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__46) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HAFGRTR_EL2_AMCNTEN0 == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__49 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__51 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__51 : Bool)
                      then
                        (do
                          let w__53 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__53 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__54 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_AMCNTENCLR0_EL0 w__54)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__61 ← (( do
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
              if (w__61 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__63 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__63 : Bool)
                  then
                    (do
                      let w__65 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__65 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__66 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCNTENCLR0_EL0 w__66)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__67 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_AMCNTENCLR0_EL0 w__67)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMCNTENCLR1_EL0_SysRegRead_4cb38b40de21160e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let __HAFGRTR_EL2_AMCNTEN1 : (BitVec 1) := (_get_HAFGRTR_EL2_Type_AMCNTEN1 w__7)
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
              else (pure false)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
      if (w__14 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__AMUSERENR_EL0_EN == 0#1) : Bool)
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
              let w__18 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__18 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         (EL2Enabled ())) : Bool)
                                    then
                                      (do
                                        let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                        (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                                w__21)) != 0b11#2) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (IsFeatureImplemented FEAT_FGT))
                               else (pure false)) : Bool)
                          then
                            (do
                              (pure ((← do
                                    let w__25 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__25) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HAFGRTR_EL2_AMCNTEN1 == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__30 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__30 : Bool)
                      then
                        (do
                          let w__32 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__32 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__33 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_AMCNTENCLR1_EL0 w__33))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__40 ← (( do
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
          if (w__40 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__42 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__CPTR_EL2_TAM == 1#1) : Bool))) ) : SailM Bool )
              if (w__42 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__49 ← (( do
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
                                    let w__46 ← (( do (HaveEL EL3) ) : SailM Bool )
                                    (pure (((! w__46) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                          else (pure false)) && ((__HAFGRTR_EL2_AMCNTEN1 == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__49 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__51 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__51 : Bool)
                      then
                        (do
                          let w__53 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__53 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__54 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_AMCNTENCLR1_EL0 w__54)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__61 ← (( do
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
              if (w__61 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__63 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__CPTR_EL3_TAM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__63 : Bool)
                  then
                    (do
                      let w__65 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__65 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__66 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCNTENCLR1_EL0 w__66)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__67 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_AMCNTENCLR1_EL0 w__67)))
              else (pure (())))))


end ArmFull.Functions
