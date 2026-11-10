import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0041
import ArmFull.Fn.M0048
import ArmFull.Fn.M0072
import ArmFull.Fn.M0076
import ArmFull.Fn.M0079
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
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
def CNTVCT_EL0_SysRegRead_1d562372e622baf9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0VCTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0VCTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0VCTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0VCTEN w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1TVCT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1TVCT w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__10 ← (( do
        (pure ((← do
              let w__9 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__7) +++ (_get_HCR_EL2_Type_TGE w__8)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__9) : Bool)))) && ((__CNTKCTL_EL1_EL0VCTEN == 0#1) : Bool))) ) : SailM
        Bool )
      if (w__10 : Bool)
      then
        (do
          let w__12 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__12 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__17 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__14 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__14) +++ (_get_HCR_EL2_Type_TGE w__15)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL0VCTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__22 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__19) +++ (_get_HCR_EL2_Type_TGE w__20)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1TVCT == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__22 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__27 ← (( do
                    if (((HaveEL EL2) : Bool) : Bool)
                    then
                      (do
                        if ((← do
                             let w__23 ← (( do (EL2Enabled ()) ) : SailM Bool )
                             (pure (((! w__23) : Bool)))) : Bool)
                        then (pure true)
                        else
                          (do
                            let w__24 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            let w__25 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_HCR_EL2_Type_E2H w__24) +++ (_get_HCR_EL2_Type_TGE w__25)) != 0b11#2) : Bool)))))
                    else (pure false) ) : SailM Bool )
                  if (w__27 : Bool)
                  then
                    (do
                      let w__28 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__29 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (w__28 - w__29)))
                  else
                    (do
                      let w__30 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 w__30))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__32 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__CNTHCTL_EL2_EL1TVCT == 1#1) : Bool))) ) : SailM Bool )
          if (w__32 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              if ((HaveEL EL2) : Bool)
              then
                (do
                  let w__33 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let w__34 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (w__33 - w__34)))
              else
                (do
                  let w__35 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (X_set t 64 w__35))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 0#1) : Bool)
              then
                (do
                  let w__36 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  let w__37 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (w__36 - w__37)))
              else
                (do
                  let w__38 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (X_set t 64 w__38)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__40 ← (( do
                    if (((HaveEL EL2) : Bool) : Bool)
                    then
                      (do
                        let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                        (pure (((! w__39) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__40 : Bool)
                  then
                    (do
                      let w__41 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__42 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (w__41 - w__42)))
                  else
                    (do
                      let w__44 ← (( do
                        if (((HaveEL EL2) : Bool) : Bool)
                        then
                          (do
                            (ELUsingAArch32 EL2))
                        else (pure false) ) : SailM Bool )
                      if (w__44 : Bool)
                      then
                        (do
                          let w__45 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__46 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                          (X_set t 64 (w__45 - w__46)))
                      else
                        (do
                          let w__47 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64 w__47))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTV_TVAL_EL0_SysRegRead_f682815b8c52312a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__2)
  let w__3 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  let __CNTV_CTL_EL0_ENABLE : (BitVec 1) := (_get_CNTV_CTL_EL0_Type_ENABLE w__3)
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
                  if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__6 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__6))
                  else
                    (do
                      let w__7 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                      let w__8 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__9 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64
                        (__get_CNTV_TVAL_EL0 (Mk_CNTV_TVAL_EL0_Type (w__7 - (w__8 - w__9)))))))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__11 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__11) : Bool))))
                          else (pure false)) && ((__HCR_EL2_E2H == 1#1) : Bool))) ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__14 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__14))
                      else
                        (do
                          let w__15 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                          let w__16 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__17 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_CNTV_TVAL_EL0 (Mk_CNTV_TVAL_EL0_Type (w__15 - (w__16 - w__17)))))))
                  else sailThrow ((Error_Undefined ())))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CONTEXTIDR_EL2_SysRegRead_dc0e6b987e373678 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do readReg CONTEXTIDR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CONTEXTIDR_EL2 w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CONTEXTIDR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CONTEXTIDR_EL2 w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CPTR_EL2_SysRegRead_70f3036b7ed095c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_TCPAC : (BitVec 1) := (_get_CPTR_EL3_Type_TCPAC w__3)
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
              let w__11 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__CPTR_EL3_TCPAC == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__CPTR_EL3_TCPAC == 1#1)) : Bool)
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
                      let w__14 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CPTR_EL2 w__14)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CPTR_EL2 w__15)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CSSELR_EL1_SysRegRead_5913225fc951e4d2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID4 : (BitVec 1) := (_get_HCR_EL2_Type_TID4 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_CSSELR_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_CSSELR_EL1 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_TID4 == 1#1) : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__13 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGRTR_EL2_CSSELR_EL1 == 1#1) : Bool)))
                    ) : SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__14 ← (( do readReg CSSELR_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CSSELR_EL1 w__14))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__15 ← (( do readReg CSSELR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CSSELR_EL1 w__15)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do readReg CSSELR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CSSELR_EL1 w__16)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CTR_EL0_SysRegRead_17103694dd49566e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_UCT : (BitVec 1) := (_get_SCTLR_EL1_Type_UCT w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID2 : (BitVec 1) := (_get_HCR_EL2_Type_TID2 w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_CTR_EL0 : (BitVec 1) := (_get_HFGRTR_EL2_Type_CTR_EL0 w__5)
  let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_UCT : (BitVec 1) := (_get_SCTLR_EL2_Type_UCT w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_UCT == 0#1) : Bool))) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
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
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      (pure ((← do
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
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGRTR_EL2_CTR_EL0 == 1#1) : Bool)))
                ) : SailM Bool )
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
                          else (pure false)) && ((__SCTLR_EL2_UCT == 0#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__32 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CTR_EL0 w__32)))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__34 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TID2 == 1#1) : Bool))) ) : SailM Bool )
          if (w__34 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__39 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGRTR_EL2_CTR_EL0 == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__39 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__40 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CTR_EL0 w__40)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__41 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CTR_EL0 w__41)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__42 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CTR_EL0 w__42)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DACR32_EL2_SysRegRead_7553854be98ecb11 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  if ((! (HaveAArch32EL EL1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__3 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__3 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ())))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__4 ← (( do readReg DACR32_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_DACR32_EL2 w__4)))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      let w__5 ← (( do readReg DACR32_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_DACR32_EL2 w__5)))
                  else (pure (()))))))


end ArmFull.Functions
