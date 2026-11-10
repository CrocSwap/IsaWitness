import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0036
import ArmFull.Fn.M0048
import ArmFull.Fn.M0067
import ArmFull.Fn.M0071
import ArmFull.Fn.M0079
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144
import ArmFull.Fn.M0178
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
def CNTHV_TVAL_EL2_SysRegRead_42829873ebd7042d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHV_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHV_CTL_EL2_Type_ENABLE w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
              then
                (do
                  let w__5 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else
                (do
                  let w__6 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                  let w__7 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__6 - w__7))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__8 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__8))
                  else
                    (do
                      let w__9 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                      let w__10 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__9 - w__10))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTKCTL_EL1_SysRegRead_dfa3587117fd7e6d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          let w__4 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTKCTL_EL1 w__5)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__9 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__7) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      let w__10 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTKCTL_EL1 w__10)))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPCT_EL0_SysRegRead_30a0e264d583fe56 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0PCTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0PCTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let w__7 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_VHE)) : Bool)
    then
      (do
        let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_E2H w__6) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__8 : Int :=
    if (w__7 : Bool)
    then 10
    else 0
  let __CNTHCTL_EL2_EL1PCTEN : (BitVec 1) := (BitVec.slice w__4 (Sail.Int.toNatChecked (w__8)) 1)
  let w__9 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0PCTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0PCTEN w__9)
  let w__10 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ECVEn : (BitVec 1) := (_get_SCR_EL3_Type_ECVEn w__10)
  let w__11 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_ECV : (BitVec 1) := (_get_CNTHCTL_EL2_Type_ECV w__11)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__16 ← (( do
        (pure ((← do
              let w__15 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__13) +++ (_get_HCR_EL2_Type_TGE w__14)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__15) : Bool)))) && ((__CNTKCTL_EL1_EL0PCTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__16 : Bool)
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
          let w__21 ← (( do
            (pure ((← do
                  (pure ((← do
                        (EL2Enabled ())) && ((__HCR_EL2_E2H == 0#1) : Bool)))) && ((__CNTHCTL_EL2_EL1PCTEN == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE w__24)) == 0b10#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1PCTEN == 0#1) : Bool))) ) : SailM
                Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                      w__29)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL0PCTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__39 ← (( do
                        if ((← do
                             (pure ((← do
                                   (pure ((← do
                                         if ((← do
                                              (IsFeatureImplemented FEAT_ECV)) : Bool)
                                         then
                                           (do
                                             (EL2Enabled ()))
                                         else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))) : Bool)
                        then
                          (do
                            let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_HCR_EL2_Type_E2H w__37) +++ (_get_HCR_EL2_Type_TGE w__38)) != 0b11#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__39 : Bool)
                      then
                        (do
                          let w__40 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__41 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64 (w__40 - w__41)))
                      else
                        (do
                          let w__42 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64 w__42)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__44 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__CNTHCTL_EL2_EL1PCTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__44 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__49 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (IsFeatureImplemented FEAT_ECV)) : Bool)
                            then
                              (do
                                (EL2Enabled ()))
                            else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__49 : Bool)
              then
                (do
                  let w__50 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let w__51 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (w__50 - w__51)))
              else
                (do
                  let w__52 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (X_set t 64 w__52))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__53 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
              (X_set t 64 w__53))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__54 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (X_set t 64 w__54))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPS_CTL_EL1_SysRegRead_b28f26339dbc713f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ST : (BitVec 1) := (_get_SCR_EL3_Type_ST w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__4 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTPS_CTL_EL1 w__4)))))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTPS_CTL_EL1 w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPS_CVAL_EL1_SysRegRead_21e9c10a0f76a1d1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ST : (BitVec 1) := (_get_SCR_EL3_Type_ST w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__4 ← (( do readReg CNTPS_CVAL_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 w__4))))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTPS_CVAL_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPS_TVAL_EL1_SysRegRead_748a1753bd033377 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ST : (BitVec 1) := (_get_SCR_EL3_Type_ST w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ECVEn : (BitVec 1) := (_get_SCR_EL3_Type_ECVEn w__4)
  let w__5 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_ECV : (BitVec 1) := (_get_CNTHCTL_EL2_Type_ECV w__5)
  let w__6 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
  let __CNTPS_CTL_EL1_ENABLE : (BitVec 1) := (_get_CNTPS_CTL_EL1_Type_ENABLE w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if (((HaveEL EL3) && (__SCR_EL3_NS == 0#1)) : Bool)
          then
            (do
              if ((__SCR_EL3_EEL2 == 1#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__SCR_EL3_ST == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__11 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (IsFeatureImplemented FEAT_ECV)) : Bool)
                                    then
                                      (do
                                        (EL2Enabled ()))
                                    else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          if ((__CNTPS_CTL_EL1_ENABLE == 0#1) : Bool)
                          then
                            (do
                              let w__12 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                              (X_set t 64 w__12))
                          else
                            (do
                              let w__13 ← (( do readReg CNTPS_CVAL_EL1 ) : SailM (BitVec 64) )
                              let w__14 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              let w__15 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_CNTPS_TVAL_EL1
                                  (Mk_CNTPS_TVAL_EL1_Type (w__13 - (w__14 - w__15)))))))
                      else
                        (do
                          if ((__CNTPS_CTL_EL1_ENABLE == 0#1) : Bool)
                          then
                            (do
                              let w__16 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                              (X_set t 64 w__16))
                          else
                            (do
                              let w__17 ← (( do readReg CNTPS_CVAL_EL1 ) : SailM (BitVec 64) )
                              let w__18 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_CNTPS_TVAL_EL1 (Mk_CNTPS_TVAL_EL1_Type (w__17 - w__18)))))))))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTPS_CTL_EL1_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__19 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__19))
                  else
                    (do
                      let w__20 ← (( do readReg CNTPS_CVAL_EL1 ) : SailM (BitVec 64) )
                      let w__21 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTPS_TVAL_EL1 (Mk_CNTPS_TVAL_EL1_Type (w__20 - w__21))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTP_TVAL_EL0_SysRegRead_65dd187dcad1babf (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  let __CNTP_CTL_EL0_ENABLE : (BitVec 1) := (_get_CNTP_CTL_EL0_Type_ENABLE w__3)
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
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__6 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__6))
                  else
                    (do
                      let w__7 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                      let w__8 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__7 - w__8))))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__10 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__10) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__12 : Bool)
                  then
                    (do
                      if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__13 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__13))
                      else
                        (do
                          let w__14 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                          let w__15 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__14 - w__15))))))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTP_TVAL_EL0_SysRegRead_aa86b862886b57ac (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0PTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0PTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PCEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PCEN w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1PTEN w__4)
  let w__5 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0PTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0PTEN w__5)
  let w__6 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHPS_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHPS_CTL_EL2_Type_ENABLE w__6)
  let w__7 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHP_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHP_CTL_EL2_Type_ENABLE w__7)
  let w__8 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ECVEn : (BitVec 1) := (_get_SCR_EL3_Type_ECVEn w__8)
  let w__9 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_ECV : (BitVec 1) := (_get_CNTHCTL_EL2_Type_ECV w__9)
  let w__10 ← (( do readReg CNTP_CTL_EL0 ) : SailM (BitVec 64) )
  let __CNTP_CTL_EL0_ENABLE : (BitVec 1) := (_get_CNTP_CTL_EL0_Type_ENABLE w__10)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__15 ← (( do
        (pure ((← do
              let w__14 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__13 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__12) +++ (_get_HCR_EL2_Type_TGE w__13)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__14) : Bool)))) && ((__CNTKCTL_EL1_EL0PTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__15 : Bool)
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
          let w__21 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_HCR_EL2_Type_E2H w__19) == 0#1) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__21 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__23) +++ (_get_HCR_EL2_Type_TGE w__24)) == 0b10#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                      w__29)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL0PTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__39 ← (( do
                        if ((← do
                             if ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__33 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      let w__34 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((((_get_HCR_EL2_Type_E2H w__33) +++ (_get_HCR_EL2_Type_TGE
                                              w__34)) == 0b11#2) : Bool))))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__36 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_SCR_EL3_Type_NS w__36) == 0#1) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (IsFeatureImplemented FEAT_SEL2))
                        else (pure false) ) : SailM Bool )
                      if (w__39 : Bool)
                      then
                        (do
                          if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                          then
                            (do
                              let w__40 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                              (X_set t 64 w__40))
                          else
                            (do
                              let w__41 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
                              let w__42 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__41 - w__42))))))
                      else
                        (do
                          let w__48 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__44 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__45 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__44) +++ (_get_HCR_EL2_Type_TGE
                                             w__45)) == 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__47 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure ((((_get_SCR_EL3_Type_NS w__47) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__48 : Bool)
                          then
                            (do
                              if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
                              then
                                (do
                                  let w__49 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                                  (X_set t 64 w__49))
                              else
                                (do
                                  let w__50 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
                                  let w__51 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  (X_set t 64
                                    (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__50 - w__51))))))
                          else
                            (do
                              let w__59 ← (( do
                                if ((← do
                                     (pure ((← do
                                           (pure ((← do
                                                 if ((← do
                                                      (IsFeatureImplemented FEAT_ECV)) : Bool)
                                                 then
                                                   (do
                                                     (EL2Enabled ()))
                                                 else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))) : Bool)
                                then
                                  (do
                                    let w__57 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__58 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__57) +++ (_get_HCR_EL2_Type_TGE
                                            w__58)) != 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__59 : Bool)
                              then
                                (do
                                  if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                                  then
                                    (do
                                      let w__60 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64)
                                        )
                                      (X_set t 64 w__60))
                                  else
                                    (do
                                      let w__61 ← (( do readReg CNTP_CVAL_EL0 ) : SailM
                                        (BitVec 64) )
                                      let w__62 ← (( do (PhysicalCountInt ()) ) : SailM
                                        (BitVec 64) )
                                      let w__63 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64)
                                        )
                                      (X_set t 64
                                        (__get_CNTP_TVAL_EL0
                                          (Mk_CNTP_TVAL_EL0_Type (w__61 - (w__62 - w__63)))))))
                              else
                                (do
                                  if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                                  then
                                    (do
                                      let w__64 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64)
                                        )
                                      (X_set t 64 w__64))
                                  else
                                    (do
                                      let w__65 ← (( do readReg CNTP_CVAL_EL0 ) : SailM
                                        (BitVec 64) )
                                      let w__66 ← (( do (PhysicalCountInt ()) ) : SailM
                                        (BitVec 64) )
                                      (X_set t 64
                                        (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__65 - w__66)))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__70 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__68 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_HCR_EL2_Type_E2H w__68) == 0#1) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__70 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__74 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__72 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__72) == 1#1) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__74 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__79 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (IsFeatureImplemented FEAT_ECV)) : Bool)
                                then
                                  (do
                                    (EL2Enabled ()))
                                else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__79 : Bool)
                  then
                    (do
                      if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__80 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__80))
                      else
                        (do
                          let w__81 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                          let w__82 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__83 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__81 - (w__82 - w__83)))))))
                  else
                    (do
                      if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__84 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__84))
                      else
                        (do
                          let w__85 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                          let w__86 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__85 - w__86)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__91 ← (( do
                if ((← do
                     if ((← do
                          let w__87 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__87) == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         let w__88 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_NS w__88) == 0#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    (IsFeatureImplemented FEAT_SEL2))
                else (pure false) ) : SailM Bool )
              if (w__91 : Bool)
              then
                (do
                  if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__92 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__92))
                  else
                    (do
                      let w__93 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
                      let w__94 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__93 - w__94))))))
              else
                (do
                  let w__97 ← (( do
                    if ((← do
                         let w__95 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__95) == 1#1) : Bool)))) : Bool)
                    then
                      (do
                        let w__96 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__96) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__97 : Bool)
                  then
                    (do
                      if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__98 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__98))
                      else
                        (do
                          let w__99 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
                          let w__100 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__99 - w__100))))))
                  else
                    (do
                      if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__101 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__101))
                      else
                        (do
                          let w__102 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                          let w__103 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__102 - w__103))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTP_CTL_EL0_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__104 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__104))
                  else
                    (do
                      let w__105 ← (( do readReg CNTP_CVAL_EL0 ) : SailM (BitVec 64) )
                      let w__106 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTP_TVAL_EL0 (Mk_CNTP_TVAL_EL0_Type (w__105 - w__106))))))
              else (pure (())))))


end ArmFull.Functions
