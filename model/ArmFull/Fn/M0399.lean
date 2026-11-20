module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0076
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0140
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
def REVIDR_EL1_SysRegRead_ec0a78562653e4de (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID1 : (BitVec 1) := (_get_HCR_EL2_Type_TID1 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_REVIDR_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_REVIDR_EL1 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__5 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else sailThrow ((Error_Undefined ())))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID1 == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__16 ← (( do
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
                                let w__13 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__13) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGRTR_EL2_REVIDR_EL1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__17 ← (( do readReg REVIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__17))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__18 ← (( do readReg REVIDR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__18))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__19 ← (( do readReg REVIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__19))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RGSR_EL1_SysRegRead_64fa1a7b4e06fd7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ATA : (BitVec 1) := (_get_SCR_EL3_Type_ATA w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_ATA : (BitVec 1) := (_get_HCR_EL2_Type_ATA w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_ATA == 0#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_ATA == 0#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_ATA == 0#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__16 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__16 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__17 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_RGSR_EL1 w__17))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__24 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_ATA == 0#1) : Bool))) ) : SailM Bool )
              if (w__24 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__26 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_ATA == 0#1) : Bool))) ) : SailM Bool )
                  if (w__26 : Bool)
                  then
                    (do
                      let w__28 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__28 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__29 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_RGSR_EL1 w__29)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__30 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_RGSR_EL1 w__30)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RMR_EL2_SysRegRead_0cc9a425a7ab6f44 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__0)
  let w__6 ← (( do
    (pure ((← do
          if ((← do
               if ((← do
                    let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__1.EL == EL1) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              (IsHighestEL EL2))
          else (pure false)) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
  else
    (do
      let w__9 ← (( do
        if ((← do
             let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__7.EL == EL2) : Bool)))) : Bool)
        then
          (do
            (IsHighestEL EL2))
        else (pure false) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          let w__10 ← (( do readReg RMR_EL2 ) : SailM (BitVec 64) )
          (X_set t 64 (__get_RMR_EL2 w__10)))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def RNDRRS_SysRegRead_8cd65845e0b85be3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TRNDR : (BitVec 1) := (_get_SCR_EL3_Type_TRNDR w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__4 ← (( do
        (pure ((← do
              (IsFeatureImplemented FEAT_RNG_TRAP)) && ((__SCR_EL3_TRNDR == 1#1) : Bool))) ) : SailM
        Bool )
      if (w__4 : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__7 ← (( do (IsFeatureImplemented FEAT_RNG) ) : SailM Bool )
          if ((! w__7) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__8 ← (( do readReg RNDRRS ) : SailM (BitVec 64) )
              (X_set t 64 w__8))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  (IsFeatureImplemented FEAT_RNG_TRAP)) && ((__SCR_EL3_TRNDR == 1#1) : Bool))) ) :
            SailM Bool )
          if (w__10 : Bool)
          then
            (do
              let w__12 ← (( do
                (pure ((← do
                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__13 ← (( do (IsFeatureImplemented FEAT_RNG) ) : SailM Bool )
              if ((! w__13) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__14 ← (( do readReg RNDRRS ) : SailM (BitVec 64) )
                  (X_set t 64 w__14))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (IsFeatureImplemented FEAT_RNG_TRAP)) && ((__SCR_EL3_TRNDR == 1#1) : Bool))) )
                : SailM Bool )
              if (w__16 : Bool)
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
                  let w__19 ← (( do (IsFeatureImplemented FEAT_RNG) ) : SailM Bool )
                  if ((! w__19) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__20 ← (( do readReg RNDRRS ) : SailM (BitVec 64) )
                      (X_set t 64 w__20))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__22 ← (( do
                    (pure ((← do
                          (IsFeatureImplemented FEAT_RNG_TRAP)) && ((__SCR_EL3_TRNDR == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__23 ← (( do (IsFeatureImplemented FEAT_RNG) ) : SailM Bool )
                      if ((! w__23) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__24 ← (( do readReg RNDRRS ) : SailM (BitVec 64) )
                          (X_set t 64 w__24))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RNDR_SysRegRead_cb03dcf786233956 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TRNDR : (BitVec 1) := (_get_SCR_EL3_Type_TRNDR w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__4 ← (( do
        (pure ((← do
              (IsFeatureImplemented FEAT_RNG_TRAP)) && ((__SCR_EL3_TRNDR == 1#1) : Bool))) ) : SailM
        Bool )
      if (w__4 : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__7 ← (( do (IsFeatureImplemented FEAT_RNG) ) : SailM Bool )
          if ((! w__7) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__8 ← (( do readReg RNDR ) : SailM (BitVec 64) )
              (X_set t 64 w__8))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  (IsFeatureImplemented FEAT_RNG_TRAP)) && ((__SCR_EL3_TRNDR == 1#1) : Bool))) ) :
            SailM Bool )
          if (w__10 : Bool)
          then
            (do
              let w__12 ← (( do
                (pure ((← do
                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__13 ← (( do (IsFeatureImplemented FEAT_RNG) ) : SailM Bool )
              if ((! w__13) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__14 ← (( do readReg RNDR ) : SailM (BitVec 64) )
                  (X_set t 64 w__14))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__16 ← (( do
                (pure ((← do
                      (IsFeatureImplemented FEAT_RNG_TRAP)) && ((__SCR_EL3_TRNDR == 1#1) : Bool))) )
                : SailM Bool )
              if (w__16 : Bool)
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
                  let w__19 ← (( do (IsFeatureImplemented FEAT_RNG) ) : SailM Bool )
                  if ((! w__19) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__20 ← (( do readReg RNDR ) : SailM (BitVec 64) )
                      (X_set t 64 w__20))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__22 ← (( do
                    (pure ((← do
                          (IsFeatureImplemented FEAT_RNG_TRAP)) && ((__SCR_EL3_TRNDR == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__23 ← (( do (IsFeatureImplemented FEAT_RNG) ) : SailM Bool )
                      if ((! w__23) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__24 ← (( do readReg RNDR ) : SailM (BitVec 64) )
                          (X_set t 64 w__24))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RVBAR_EL2_SysRegRead_4cac2371e78214e1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__0)
  let w__6 ← (( do
    (pure ((← do
          if ((← do
               if ((← do
                    let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__1.EL == EL1) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              (IsHighestEL EL2))
          else (pure false)) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
  else
    (do
      let w__9 ← (( do
        if ((← do
             let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__7.EL == EL2) : Bool)))) : Bool)
        then
          (do
            (IsHighestEL EL2))
        else (pure false) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          let w__10 ← (( do readReg RVBAR_EL2 ) : SailM (BitVec 64) )
          (X_set t 64 w__10))
      else sailThrow ((Error_Undefined ())))


/-- Type quantifiers: t : Int -/
def S3_op1_Cn_Cm_op2_SysRegRead_9e206a297d1c5480 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_TIDCP : (BitVec 1) := (_get_SCTLR_EL1_Type_TIDCP w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_TIDCP : (BitVec 1) := (_get_SCTLR_EL2_Type_TIDCP w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TIDCP : (BitVec 1) := (_get_HCR_EL2_Type_TIDCP w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__9 ← (( do
        (pure ((← do
              let w__8 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__6) +++ (_get_HCR_EL2_Type_TGE w__7)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__8) : Bool)))) && ((__SCTLR_EL1_TIDCP == 1#1) : Bool))) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
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
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__SCTLR_EL2_TIDCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__16 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_ImpDefSysRegRead op0 op1 CRn CRm op2 t))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__18 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TIDCP == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_ImpDefSysRegRead op0 op1 CRn CRm op2 t)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              (AArch64_ImpDefSysRegRead op0 op1 CRn CRm op2 t))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_ImpDefSysRegRead op0 op1 CRn CRm op2 t))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SCTLR2_EL2_SysRegRead_4e11a5aa656bf495 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_SCTLR2En : (BitVec 1) := (_get_SCR_EL3_Type_SCTLR2En w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
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
                      else (pure false)) && ((__SCR_EL3_SCTLR2En == 0#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_SCTLR2En == 0#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then
                    (do
                      let w__16 ← (( do
                        (pure ((← do
                              (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                      if (w__16 : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                  else
                    (do
                      let w__17 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_SCTLR2_EL2 w__17)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do readReg SCTLR2_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_SCTLR2_EL2 w__18)))
              else (pure (())))))


end ArmFull.Functions
