import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0092
import ArmFull.Fn.M0138
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
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
def ID_AA64ISAR2_EL1_SysRegRead_c585336ab0c39b5d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      if ((← do
                           if ((← do
                                (IsFeatureImplemented FEAT_FGT)) : Bool)
                           then (pure true)
                           else
                             (do
                               let w__8 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
                               (pure (((! (IsZero w__8)) : Bool))))) : Bool)
                      then (pure true)
                      else
                        (do
                          (__IMPDEF_boolean "ID_AA64ISAR2_EL1 trapped by HCR_EL2.TID3")))
                  else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__14 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64ISAR2_EL1 w__14))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__15 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64ISAR2_EL1 w__15)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ID_AA64ISAR2_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_AA64MMFR0_EL1_SysRegRead_52d0be9703325603 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64MMFR0_EL1 w__8))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64MMFR0_EL1 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ID_AA64MMFR0_EL1 w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_AA64MMFR1_EL1_SysRegRead_8e0c46321a1a5a47 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__8)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__9))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__10))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_AA64MMFR2_EL1_SysRegRead_cc8ba5aa21a8fd21 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      if ((← do
                           if ((← do
                                (IsFeatureImplemented FEAT_FGT)) : Bool)
                           then (pure true)
                           else
                             (do
                               let w__8 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
                               (pure (((! (IsZero w__8)) : Bool))))) : Bool)
                      then (pure true)
                      else
                        (do
                          (__IMPDEF_boolean "ID_AA64MMFR2_EL1 trapped by HCR_EL2.TID3")))
                  else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__14 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64MMFR2_EL1 w__14))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__15 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64MMFR2_EL1 w__15)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ID_AA64MMFR2_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_AA64MMFR3_EL1_SysRegRead_a84482354ffb3943 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      if ((← do
                           if ((← do
                                (IsFeatureImplemented FEAT_FGT)) : Bool)
                           then (pure true)
                           else
                             (do
                               let w__8 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
                               (pure (((! (IsZero w__8)) : Bool))))) : Bool)
                      then (pure true)
                      else
                        (do
                          (__IMPDEF_boolean "ID_AA64MMFR3_EL1 trapped by HCR_EL2.TID3")))
                  else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__14 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64MMFR3_EL1 w__14))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__15 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64MMFR3_EL1 w__15)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ID_AA64MMFR3_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_AA64MMFR4_EL1_SysRegRead_3578f169e732088b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      if ((← do
                           if ((← do
                                (IsFeatureImplemented FEAT_FGT)) : Bool)
                           then (pure true)
                           else
                             (do
                               let w__8 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
                               (pure (((! (IsZero w__8)) : Bool))))) : Bool)
                      then (pure true)
                      else
                        (do
                          (__IMPDEF_boolean "ID_AA64MMFR4_EL1 trapped by HCR_EL2.TID3")))
                  else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__14 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64MMFR4_EL1 w__14))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__15 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64MMFR4_EL1 w__15)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ID_AA64MMFR4_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_AA64PFR0_EL1_SysRegRead_f36f783e888272fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__8)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__9))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__10))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_AA64PFR1_EL1_SysRegRead_99547bac83e88d23 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
          let w__7 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64PFR1_EL1 w__8))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64PFR1_EL1 w__9)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ID_AA64PFR1_EL1 w__10)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_AA64PFR2_EL1_SysRegRead_c98524f93c119d97 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__3 ← (( do (IsFeatureImplemented FEAT_IDST) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__5 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__5 : Bool)
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
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      if ((← do
                           if ((← do
                                (IsFeatureImplemented FEAT_FGT)) : Bool)
                           then (pure true)
                           else
                             (do
                               let w__8 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
                               (pure (((! (IsZero w__8)) : Bool))))) : Bool)
                      then (pure true)
                      else
                        (do
                          (__IMPDEF_boolean "ID_AA64PFR2_EL1 trapped by HCR_EL2.TID3")))
                  else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__14 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64PFR2_EL1 w__14))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__15 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_ID_AA64PFR2_EL1 w__15)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ID_AA64PFR2_EL1 w__16)))
              else (pure (())))))


end ArmFull.Functions
