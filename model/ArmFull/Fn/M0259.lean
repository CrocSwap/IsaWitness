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
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0076
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0139
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0247
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

def AArch32_TakeVirtualFIQException (_ : Unit) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:43355.63-43355.64"
  let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__8 ← (( do
        if ((← do
             let w__6 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
             (pure ((((_get_HCR_Type_TGE w__6) == 0#1) : Bool)))) : Bool)
        then
          (do
            let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_HCR_Type_FMO w__7) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      ArmFull.assert w__8 "sail-inputs/03-v8_base.sail:43357.62-43357.63")
  else
    (do
      let w__11 ← (( do
        if ((← do
             let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
             (pure ((((_get_HCR_EL2_Type_TGE w__9) == 0#1) : Bool)))) : Bool)
        then
          (do
            let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_FMO w__10) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      ArmFull.assert w__11 "sail-inputs/03-v8_base.sail:43359.56-43359.57")
  let w__14 ← (( do
    if ((← do
         let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__12.EL == EL0) : Bool)))) : Bool)
    then
      (do
        let w__13 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        (pure (((! w__13) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__14 : Bool)
  then
    (do
      (AArch64_TakeVirtualFIQException ()))
  else (pure (()))
  let preferred_exception_return ← (( do (ThisInstrAddr 32) ) : SailM (BitVec 32) )
  let vect_offset : Int := (BitVec.toNat 0x1C#8)
  let lr_offset : Nat := 4
  (AArch32_EnterMode M32_FIQ preferred_exception_return lr_offset vect_offset)


def __HandlePendingInterrupt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg __GIC_Pending ) : SailM (Option InterruptID) )
  match w__0 with
  | .some intid =>
    (do
      let _ : Unit := (prerr_bits "[Clock] GIC interrupt " (__GIC_InterruptID intid))
      (AArch64_TakePhysicalIRQException ()))
  | none => (pure (()))


/-- Type quantifiers: t : Int -/
def ACCDATA_EL1_SysRegRead_6deec7bc548bcc31 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_ADEn : (BitVec 1) := (_get_SCR_EL3_Type_ADEn w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_nACCDATA_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_nACCDATA_EL1 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
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
                  else (pure false)) && ((__SCR_EL3_ADEn == 0#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__18 ← (( do
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
                                let w__15 ← (( do (HaveEL EL3) ) : SailM Bool )
                                (pure (((! w__15) : Bool)))) || ((__SCR_EL3_FGTEn == 1#1) : Bool))))
                      else (pure false)) && ((__HFGRTR_EL2_nACCDATA_EL1 == 0#1) : Bool))) ) : SailM
                Bool )
              if (w__18 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__20 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_ADEn == 0#1) : Bool))) ) : SailM Bool )
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
                      let w__23 ← (( do readReg ACCDATA_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_ACCDATA_EL1 w__23))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__30 ← (( do
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
                      else (pure false)) && ((__SCR_EL3_ADEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__30 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__32 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_ADEn == 0#1) : Bool))) ) : SailM Bool )
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
                      let w__35 ← (( do readReg ACCDATA_EL1 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_ACCDATA_EL1 w__35)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__36 ← (( do readReg ACCDATA_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ACCDATA_EL1 w__36)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ACTLR_EL2_SysRegRead_949275ba7f389456 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg ACTLR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg ACTLR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AFSR0_EL2_SysRegRead_acffc015481d1ac8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg AFSR0_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg AFSR0_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AFSR1_EL2_SysRegRead_a12c342eb9f7885a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg AFSR1_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg AFSR1_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AIDR_EL1_SysRegRead_3367279f59657745 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID1 : (BitVec 1) := (_get_HCR_EL2_Type_TID1 w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__3)
  let w__4 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  let __HFGRTR_EL2_AIDR_EL1 : (BitVec 1) := (_get_HFGRTR_EL2_Type_AIDR_EL1 w__4)
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
                      else (pure false)) && ((__HFGRTR_EL2_AIDR_EL1 == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__16 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__17 ← (( do readReg AIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__17))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__18 ← (( do readReg AIDR_EL1 ) : SailM (BitVec 64) )
              (X_set t 64 w__18))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__19 ← (( do readReg AIDR_EL1 ) : SailM (BitVec 64) )
                  (X_set t 64 w__19))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMAIR2_EL2_SysRegRead_c6e17744cc03d54f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_AIEn : (BitVec 1) := (_get_SCR_EL3_Type_AIEn w__3)
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
                      else (pure false)) && ((__SCR_EL3_AIEn == 0#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__14 ← (( do
                    (pure ((← do
                          (HaveEL EL3)) && ((__SCR_EL3_AIEn == 0#1) : Bool))) ) : SailM Bool )
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
                      let w__17 ← (( do readReg AMAIR2_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__17))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__18 ← (( do readReg AMAIR2_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__18))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMAIR_EL2_SysRegRead_8a38edf51a31f5e0 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg AMAIR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg AMAIR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def AMCFGR_EL0_SysRegRead_ec6dd3c706fcda64 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      let w__21 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCFGR_EL0 w__21)))))))
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
                      let w__35 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCFGR_EL0 w__35))))))
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
                      let w__47 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_AMCFGR_EL0 w__47)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__48 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_AMCFGR_EL0 w__48)))
              else (pure (())))))


end ArmFull.Functions
