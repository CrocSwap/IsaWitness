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
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0076
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0195
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
def MECID_A0_EL2_SysRegRead_d1ae9fcf467da39c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_MECEn : (BitVec 1) := (_get_SCR_EL3_Type_MECEn w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do (IsCurrentSecurityState SS_Realm) ) : SailM Bool )
              if ((! w__3) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                          else (pure false)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__10 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__12 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                      if (w__12 : Bool)
                      then
                        (do
                          let w__14 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__14 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__15 ← (( do readReg MECID_A0_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_MECID_A0_EL2 w__15))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg MECID_A0_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MECID_A0_EL2 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MECID_A1_EL2_SysRegRead_c4456c8d850c3339 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_MECEn : (BitVec 1) := (_get_SCR_EL3_Type_MECEn w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do (IsCurrentSecurityState SS_Realm) ) : SailM Bool )
              if ((! w__3) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                          else (pure false)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__10 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__12 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                      if (w__12 : Bool)
                      then
                        (do
                          let w__14 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__14 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__15 ← (( do readReg MECID_A1_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_MECID_A1_EL2 w__15))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg MECID_A1_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MECID_A1_EL2 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MECID_P0_EL2_SysRegRead_63d80c0de4f28c1a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_MECEn : (BitVec 1) := (_get_SCR_EL3_Type_MECEn w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do (IsCurrentSecurityState SS_Realm) ) : SailM Bool )
              if ((! w__3) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                          else (pure false)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__10 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__12 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                      if (w__12 : Bool)
                      then
                        (do
                          let w__14 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__14 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__15 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_MECID_P0_EL2 w__15))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg MECID_P0_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MECID_P0_EL2 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MECID_P1_EL2_SysRegRead_7875ab7fe28cd25b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_MECEn : (BitVec 1) := (_get_SCR_EL3_Type_MECEn w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do (IsCurrentSecurityState SS_Realm) ) : SailM Bool )
              if ((! w__3) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
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
                          else (pure false)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__10 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__12 ← (( do
                        (pure ((← do
                              (HaveEL EL3)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                      if (w__12 : Bool)
                      then
                        (do
                          let w__14 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__14 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__15 ← (( do readReg MECID_P1_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_MECID_P1_EL2 w__15))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg MECID_P1_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MECID_P1_EL2 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MIDR_EL1_SysRegRead_5aac357d91bc3b98 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__2)
  let w__3 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_MIDR_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_MIDR_EL1 w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__4 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
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
          let w__13 ← (( do
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
                            let w__10 ← (( do (HaveEL EL3) ) : SailM Bool )
                            (pure (((! w__10) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                  else (pure false)) && ((__HFGRTR_EL2_MIDR_EL1 == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__14 ← (( do (EL2Enabled ()) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  let w__15 ← (( do readReg VPIDR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_VPIDR_EL2 w__15)))
              else
                (do
                  let w__16 ← (( do readReg MIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MIDR_EL1 w__16)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__17 ← (( do readReg MIDR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_MIDR_EL1 w__17)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do readReg MIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MIDR_EL1 w__18)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAM0_EL1_SysRegRead_26602bb382f28735 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  let __MPAM2_EL2_TRAPMPAM0EL1 : (BitVec 1) := (_get_MPAM2_EL2_Type_TRAPMPAM0EL1 w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              let w__7 ← (( do
                (pure ((← do
                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__9 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__MPAM2_EL2_TRAPMPAM0EL1 == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__9 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__10 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAM0_EL1 w__10)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__12 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__14 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__15 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAM0_EL1 w__15))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAM0_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAM2_EL2_SysRegRead_f89d395320b0f023 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__2)
  let w__3 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__3)
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
              let w__7 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  let w__9 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8))))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then
                (do
                  let w__13 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__13 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__14 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAM2_EL2 w__14))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAM2_EL2 w__15)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAMIDR_EL1_SysRegRead_e782b807b20cd739 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  let __MPAM3_EL3_TRAPLOWER : (BitVec 1) := (_get_MPAM3_EL3_Type_TRAPLOWER w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  let __MPAMIDR_EL1_HAS_HCR : (BitVec 1) := (_get_MPAMIDR_EL1_Type_HAS_HCR w__3)
  let w__4 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
  let __MPAMHCR_EL2_TRAP_MPAMIDR_EL1 : (BitVec 1) := (_get_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 w__4)
  let w__5 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  let __MPAMIDR_EL1_HAS_TIDR : (BitVec 1) := (_get_MPAMIDR_EL1_Type_HAS_TIDR w__5)
  let w__6 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  let __MPAM2_EL2_TIDR : (BitVec 1) := (_get_MPAM2_EL2_Type_TIDR w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              let w__10 ← (( do
                (pure ((← do
                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
              if (w__10 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      (pure ((← do
                            (EL2Enabled ())) && ((__MPAMIDR_EL1_HAS_HCR == 1#1) : Bool)))) && ((__MPAMHCR_EL2_TRAP_MPAMIDR_EL1 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (EL2Enabled ())) && ((__MPAMIDR_EL1_HAS_TIDR == 1#1) : Bool)))) && ((__MPAM2_EL2_TIDR == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__17 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
                      let w__18 ← (( do (__get_MPAMIDR_EL1 w__17) ) : SailM (BitVec 64) )
                      (X_set t 64 w__18)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__20 ← (( do
                (pure ((← do
                      (HaveEL EL3)) && ((__MPAM3_EL3_TRAPLOWER == 1#1) : Bool))) ) : SailM Bool )
              if (w__20 : Bool)
              then
                (do
                  let w__22 ← (( do
                    (pure ((← do
                          (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                  if (w__22 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
              else
                (do
                  let w__23 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
                  let w__24 ← (( do (__get_MPAMIDR_EL1 w__23) ) : SailM (BitVec 64) )
                  (X_set t 64 w__24)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__25 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
                  let w__26 ← (( do (__get_MPAMIDR_EL1 w__25) ) : SailM (BitVec 64) )
                  (X_set t 64 w__26))
              else (pure (())))))


end ArmFull.Functions
