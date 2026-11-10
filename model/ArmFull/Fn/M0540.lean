import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0035
import ArmFull.Fn.M0041
import ArmFull.Fn.M0046
import ArmFull.Fn.M0051
import ArmFull.Fn.M0052
import ArmFull.Fn.M0058
import ArmFull.Fn.M0063
import ArmFull.Fn.M0072
import ArmFull.Fn.M0092
import ArmFull.Fn.M0100
import ArmFull.Fn.M0146
import ArmFull.Fn.M0166
import ArmFull.Fn.M0181
import ArmFull.Fn.M0182
import ArmFull.Fn.M0196
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
def TPIDR_EL1_SysRegWrite_be51f1ab4eeaabd3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__1)
  let w__2 ← (( do readReg HFGWTR_EL2 ) : SailM (BitVec 64) )
  let __HFGWTR_EL2_TPIDR_EL1 : (BitVec 1) := (_get_HFGWTR_EL2_Type_TPIDR_EL1 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__7 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (EL2Enabled ())) : Bool)
                        then
                          (do
                            (IsFeatureImplemented FEAT_FGT))
                        else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGWTR_EL2_TPIDR_EL1 == 1#1) : Bool)))
            ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg TPIDR_EL1 w__8))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg TPIDR_EL1 w__9)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__10 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg TPIDR_EL1 w__10)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TRFCR_EL2_SysRegWrite_20a366481946c8fe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TTRF : (BitVec 1) := (_get_MDCR_EL3_Type_TTRF w__3)
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
                      else (pure false)) && ((__MDCR_EL3_TTRF == 1#1) : Bool))) ) : SailM Bool )
              if (w__11 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((HaveEL EL3) && (__MDCR_EL3_TTRF == 1#1)) : Bool)
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
                      let w__14 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg TRFCR_EL2 (Mk_TRFCR_EL2_Type w__14))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__15 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg TRFCR_EL2 (Mk_TRFCR_EL2_Type w__15))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TTBR0_EL2_SysRegWrite_6f2504a3aff125cc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
              let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (Sail.BitVec.updateSubrange w__4 63 0 w__5))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__6 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (TTBR0_EL2_write (Mk_TTBR0_EL2_Type (Sail.BitVec.updateSubrange w__6 63 0 w__7))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TTBR1_EL2_SysRegWrite_2b203badd6cd49c7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
              let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange w__4 63 0 w__5))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__6 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
                  let w__7 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg TTBR1_EL2 (Sail.BitVec.updateSubrange w__6 63 0 w__7))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VBAR_EL2_SysRegWrite_89ae3d074e337e2e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg VBAR_EL2 w__4)
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg VBAR_EL2 w__5)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VMECID_A_EL2_SysRegWrite_d4d52ce2ee2e86c2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__9 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                      then
                        (do
                          let w__11 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__11 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg VMECID_A_EL2 (Mk_VMECID_A_EL2_Type w__12)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg VMECID_A_EL2 (Mk_VMECID_A_EL2_Type w__13))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VMECID_P_EL2_SysRegWrite_b0549714107a13fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__9 ← (( do
                    (pure ((← do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                          else (pure false)) && ((__SCR_EL3_MECEn == 0#1) : Bool))) ) : SailM Bool )
                  if (w__9 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if (((HaveEL EL3) && (__SCR_EL3_MECEn == 0#1)) : Bool)
                      then
                        (do
                          let w__11 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__11 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          let w__12 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                          writeReg VMECID_P_EL2 (Mk_VMECID_P_EL2_Type w__12)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg VMECID_P_EL2 (Mk_VMECID_P_EL2_Type w__13))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ZCR_EL2_SysRegWrite_bd0a9b879ec59921 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__2)
  let w__3 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_EZ : (BitVec 1) := (_get_CPTR_EL3_Type_EZ w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__4)
  let w__5 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_TZ : (BitVec 1) := (_get_CPTR_EL2_Type_TZ w__5)
  let w__6 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let __CPTR_EL2_ZEN : (BitVec 2) := (_get_CPTR_EL2_Type_ZEN w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (pure ((← do
                                 (pure ((← do
                                       (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                      else (pure false)) && ((__CPTR_EL3_EZ == 0#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if (((__HCR_EL2_E2H == 0#1) && (__CPTR_EL2_TZ == 1#1)) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8)))
                  else
                    (do
                      if (((__HCR_EL2_E2H == 1#1) && (let b__0 := __CPTR_EL2_ZEN
                           (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
                           then true
                           else false : Bool))) : Bool)
                      then
                        (do
                          (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x19#8)))
                      else
                        (do
                          if (((HaveEL EL3) && (__CPTR_EL3_EZ == 0#1)) : Bool)
                          then
                            (do
                              let w__16 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__16 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8))))
                          else
                            (do
                              let w__17 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                              writeReg ZCR_EL2 (Mk_ZCR_EL2_Type w__17))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                  else
                    (do
                      let w__18 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ZCR_EL2 (Mk_ZCR_EL2_Type w__18)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ZCR_EL3_SysRegWrite_8b6f2f3c0ab9da70 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  let __CPTR_EL3_EZ : (BitVec 1) := (_get_CPTR_EL3_Type_EZ w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CPTR_EL3_EZ == 0#1) : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x19#8)))
                  else
                    (do
                      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg ZCR_EL3 (Mk_ZCR_EL3_Type w__2)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def BRB_IALL_SysOpsWrite_dd273770082db6a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_SBRBE : (BitVec 2) := (_get_MDCR_EL3_Type_SBRBE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_nBRBIALL : (BitVec 1) := (_get_HFGITR_EL2_Type_nBRBIALL w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__12 ← (( do
            (pure ((← do
                  (pure ((← do
                        if ((← do
                             (pure ((← do
                                   (pure ((← do
                                         (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                        then
                          (do
                            (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                        else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
            ) : SailM Bool )
          if (w__12 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (pure ((← do
                                       (pure ((← do
                                             (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                            else (pure false)) && (let b__3 := __MDCR_EL3_SBRBE
                          (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__3 0 0)) == (0#1 : (BitVec 1))) : Bool)
                          then true
                          else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__19 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__24 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (EL2Enabled ())) : Bool)
                                then
                                  (do
                                    (IsFeatureImplemented FEAT_FGT))
                                else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_nBRBIALL == 0#1) : Bool)))
                    ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__26 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__2 := __MDCR_EL3_SBRBE
                                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2
                                        0 0)) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool))) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              let w__28 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__28 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              (BRB_IALL ())))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__35 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (pure ((← do
                                       (pure ((← do
                                             (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                            then
                              (do
                                (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                            else (pure false)) && ((__MDCR_EL3_SBRBE != 0b11#2) : Bool)))) && ((__SCR_EL3_NS == 0#1) : Bool)))
                ) : SailM Bool )
              if (w__35 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__42 ← (( do
                    (pure ((← do
                          (pure ((← do
                                if ((← do
                                     (pure ((← do
                                           (pure ((← do
                                                 (Halted ())) && ((HaveEL EL3) : Bool)))) && ((__EDSCR_SDD == 1#1) : Bool)))) : Bool)
                                then
                                  (do
                                    (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                                else (pure false)) && (let b__1 := __MDCR_EL3_SBRBE
                              (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 0 0)) == (0#1 : (BitVec 1))) : Bool)
                              then true
                              else false : Bool))))) && ((__SCR_EL3_NS == 1#1) : Bool))) ) : SailM
                    Bool )
                  if (w__42 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((((HaveEL EL3) && (__MDCR_EL3_SBRBE != 0b11#2)) && (__SCR_EL3_NS == 0#1)) : Bool)
                      then
                        (do
                          let w__44 ← (( do
                            (pure ((← do
                                  (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool )
                          if (w__44 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                      else
                        (do
                          if ((((HaveEL EL3) && (let b__0 := __MDCR_EL3_SBRBE
                                 (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0
                                        0 0)) == (0#1 : (BitVec 1))) : Bool)
                                 then true
                                 else false : Bool))) && (__SCR_EL3_NS == 1#1)) : Bool)
                          then
                            (do
                              let w__46 ← (( do
                                (pure ((← do
                                      (Halted ())) && ((__EDSCR_SDD == 1#1) : Bool))) ) : SailM Bool
                                )
                              if (w__46 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch64_SystemAccessTrap EL3 (BitVec.toNat 0x18#8))))
                          else
                            (do
                              (BRB_IALL ()))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (BRB_IALL ()))
              else (pure (())))))


end ArmFull.Functions
