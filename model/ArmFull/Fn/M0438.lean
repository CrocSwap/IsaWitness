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
import ArmFull.Fn.M0075
import ArmFull.Fn.M0092
import ArmFull.Fn.M0146
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
def CNTKCTL_EL1_SysRegWrite_b6b89671d5078ba5 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__5))
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
                      let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__10))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPS_CTL_EL1_SysRegWrite_22bfd6d865a619e7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (__set_CNTPS_CTL_EL1 (Mk_CNTPS_CTL_EL1_Type w__4)))))
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
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_CNTPS_CTL_EL1 (Mk_CNTPS_CTL_EL1_Type w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPS_CVAL_EL1_SysRegWrite_0efe14958ca47dee (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type w__4))))
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
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTPS_TVAL_EL1_SysRegWrite_fed363b581c49e0d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      let w__10 ← (( do
                        (pure ((← do
                              (pure ((← do
                                    if ((← do
                                         (IsFeatureImplemented FEAT_ECV)) : Bool)
                                    then
                                      (do
                                        (EL2Enabled ()))
                                    else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))
                        ) : SailM Bool )
                      if (w__10 : Bool)
                      then
                        (do
                          let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let w__12 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__13 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                          writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type
                            ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                  (Sail.BitVec.extractLsb w__11 31 0) 64)) + w__12)) - w__13)))
                      else
                        (do
                          let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let w__15 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type
                            ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                (Sail.BitVec.extractLsb w__14 31 0) 64)) + w__15))))))
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
                  let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__17 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  writeReg CNTPS_CVAL_EL1 (Mk_CNTPS_CVAL_EL1_Type
                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        (Sail.BitVec.extractLsb w__16 31 0) 64)) + w__17)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTP_TVAL_EL0_SysRegWrite_4aac8466b90febf7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__6 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type
                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        (Sail.BitVec.extractLsb w__5 31 0) 64)) + w__6)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__8 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__8) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__10 : Bool)
                  then
                    (do
                      let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__12 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type
                        ((Sail.BitVec.castWidth (m := 64) (sign_extend
                            (Sail.BitVec.extractLsb w__11 31 0) 64)) + w__12)))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTP_TVAL_EL0_SysRegWrite_eccdee10d8c7f39e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ECVEn : (BitVec 1) := (_get_SCR_EL3_Type_ECVEn w__6)
  let w__7 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_ECV : (BitVec 1) := (_get_CNTHCTL_EL2_Type_ECV w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__12 ← (( do
        (pure ((← do
              let w__11 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__9) +++ (_get_HCR_EL2_Type_TGE w__10)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__11) : Bool)))) && ((__CNTKCTL_EL1_EL0PTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__12 : Bool)
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
          let w__18 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_HCR_EL2_Type_E2H w__16) == 0#1) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__23 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE w__21)) == 0b10#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__23 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__28 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__25) +++ (_get_HCR_EL2_Type_TGE
                                      w__26)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__CNTHCTL_EL2_EL0PTEN == 0#1) : Bool))) ) : SailM
                    Bool )
                  if (w__28 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__36 ← (( do
                        if ((← do
                             if ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      let w__31 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                      (pure (((((_get_HCR_EL2_Type_E2H w__30) +++ (_get_HCR_EL2_Type_TGE
                                              w__31)) == 0b11#2) : Bool))))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__33 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                 (pure ((((_get_SCR_EL3_Type_NS w__33) == 0#1) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            (IsFeatureImplemented FEAT_SEL2))
                        else (pure false) ) : SailM Bool )
                      if (w__36 : Bool)
                      then
                        (do
                          let w__37 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          let w__38 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type
                            ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                (Sail.BitVec.extractLsb w__37 31 0) 64)) + w__38)))
                      else
                        (do
                          let w__44 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__40) +++ (_get_HCR_EL2_Type_TGE
                                             w__41)) == 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__43 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                                (pure ((((_get_SCR_EL3_Type_NS w__43) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__44 : Bool)
                          then
                            (do
                              let w__45 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              let w__46 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type
                                ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                    (Sail.BitVec.extractLsb w__45 31 0) 64)) + w__46)))
                          else
                            (do
                              let w__54 ← (( do
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
                                    let w__52 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__53 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__52) +++ (_get_HCR_EL2_Type_TGE
                                            w__53)) != 0b11#2) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__54 : Bool)
                              then
                                (do
                                  let w__55 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  let w__56 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  let w__57 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                                  writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type
                                    ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                          (Sail.BitVec.extractLsb w__55 31 0) 64)) + w__56)) - w__57)))
                              else
                                (do
                                  let w__58 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                                  let w__59 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type
                                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                                        (Sail.BitVec.extractLsb w__58 31 0) 64)) + w__59))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__63 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__61 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_HCR_EL2_Type_E2H w__61) == 0#1) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL1PCEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__63 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__67 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__65 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__65) == 1#1) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1PTEN == 0#1) : Bool))) ) : SailM Bool
                )
              if (w__67 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__72 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (IsFeatureImplemented FEAT_ECV)) : Bool)
                                then
                                  (do
                                    (EL2Enabled ()))
                                else (pure false)) && ((__SCR_EL3_ECVEn == 1#1) : Bool)))) && ((__CNTHCTL_EL2_ECV == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__72 : Bool)
                  then
                    (do
                      let w__73 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__74 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__75 ← (( do readReg CNTPOFF_EL2 ) : SailM (BitVec 64) )
                      writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type
                        ((Sail.BitVec.castWidth (m := 64) ((Sail.BitVec.castWidth (m := 64) (sign_extend
                              (Sail.BitVec.extractLsb w__73 31 0) 64)) + w__74)) - w__75)))
                  else
                    (do
                      let w__76 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__77 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type
                        ((Sail.BitVec.castWidth (m := 64) (sign_extend
                            (Sail.BitVec.extractLsb w__76 31 0) 64)) + w__77))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__82 ← (( do
                if ((← do
                     if ((← do
                          let w__78 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__78) == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         let w__79 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_NS w__79) == 0#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    (IsFeatureImplemented FEAT_SEL2))
                else (pure false) ) : SailM Bool )
              if (w__82 : Bool)
              then
                (do
                  let w__83 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__84 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  writeReg CNTHPS_CVAL_EL2 (Mk_CNTHPS_CVAL_EL2_Type
                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        (Sail.BitVec.extractLsb w__83 31 0) 64)) + w__84)))
              else
                (do
                  let w__87 ← (( do
                    if ((← do
                         let w__85 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__85) == 1#1) : Bool)))) : Bool)
                    then
                      (do
                        let w__86 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__86) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__87 : Bool)
                  then
                    (do
                      let w__88 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__89 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      writeReg CNTHP_CVAL_EL2 (Mk_CNTHP_CVAL_EL2_Type
                        ((Sail.BitVec.castWidth (m := 64) (sign_extend
                            (Sail.BitVec.extractLsb w__88 31 0) 64)) + w__89)))
                  else
                    (do
                      let w__90 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      let w__91 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type
                        ((Sail.BitVec.castWidth (m := 64) (sign_extend
                            (Sail.BitVec.extractLsb w__90 31 0) 64)) + w__91)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__92 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let w__93 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  writeReg CNTP_CVAL_EL0 (Mk_CNTP_CVAL_EL0_Type
                    ((Sail.BitVec.castWidth (m := 64) (sign_extend
                        (Sail.BitVec.extractLsb w__92 31 0) 64)) + w__93)))
              else (pure (())))))


end ArmFull.Functions
