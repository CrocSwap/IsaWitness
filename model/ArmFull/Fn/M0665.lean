import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0042
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0057
import ArmFull.Fn.M0059
import ArmFull.Fn.M0092
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0203
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260

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
def ID_AFR0_SysRegRead32_49547d26babbff09 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID3 : (BitVec 1) := (_get_HCR_Type_TID3 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__14) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TID3 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do (ID_AFR0_read ()) ) : SailM (BitVec 32) )
                          (R_set t w__21))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do (ID_AFR0_read ()) ) : SailM (BitVec 32) )
              (R_set t w__22))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (ID_AFR0_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__23))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_DFR0_SysRegRead32_cc2c637f50f14510 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID3 : (BitVec 1) := (_get_HCR_Type_TID3 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__14) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TID3 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
                          (R_set t w__21))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
              (R_set t w__22))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__23))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_DFR1_SysRegRead32_a7aac5df14f5281e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID3 : (BitVec 1) := (_get_HCR_Type_TID3 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__22 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (EL2Enabled ())) : Bool)
                               then
                                 (do
                                   let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                   (pure (((! w__14) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              if ((← do
                                   if ((← do
                                        (IsFeatureImplemented FEAT_FGT)) : Bool)
                                   then (pure true)
                                   else
                                     (do
                                       let w__17 ← (( do (ID_DFR1_read ()) ) : SailM (BitVec 32) )
                                       (pure (((! (IsZero w__17)) : Bool))))) : Bool)
                              then (pure true)
                              else
                                (do
                                  (__IMPDEF_boolean "ID_DFR1 trapped by HCR_EL2.TID3")))
                          else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__22 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__32 ← (( do
                        (pure ((← do
                              if ((← do
                                   if ((← do
                                        (EL2Enabled ())) : Bool)
                                   then
                                     (do
                                       (ELUsingAArch32 EL2))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  if ((← do
                                       if ((← do
                                            (IsFeatureImplemented FEAT_FGT)) : Bool)
                                       then (pure true)
                                       else
                                         (do
                                           let w__27 ← (( do (ID_DFR1_read ()) ) : SailM
                                             (BitVec 32) )
                                           (pure (((! (IsZero w__27)) : Bool))))) : Bool)
                                  then (pure true)
                                  else
                                    (do
                                      (__IMPDEF_boolean "ID_DFR1 trapped by HCR.TID3")))
                              else (pure false)) && ((__HCR_TID3 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__32 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__33 ← (( do (ID_DFR1_read ()) ) : SailM (BitVec 32) )
                          (R_set t w__33))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__34 ← (( do (ID_DFR1_read ()) ) : SailM (BitVec 32) )
              (R_set t w__34))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__35 ← (( do (ID_DFR1_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__35))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_ISAR0_SysRegRead32_bb26ec35196a236d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID3 : (BitVec 1) := (_get_HCR_Type_TID3 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__14) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TID3 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
                          (R_set t w__21))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
              (R_set t w__22))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__23))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_ISAR1_SysRegRead32_2151a78ccf12fa49 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID3 : (BitVec 1) := (_get_HCR_Type_TID3 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__14) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TID3 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
                          (R_set t w__21))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
              (R_set t w__22))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__23))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ID_ISAR2_SysRegRead32_24153ecb491475a1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T0 : (BitVec 1) := (_get_HSTR_EL2_Type_T0 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T0 : (BitVec 1) := (_get_HSTR_Type_T0 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TID3 : (BitVec 1) := (_get_HCR_EL2_Type_TID3 w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TID3 : (BitVec 1) := (_get_HCR_Type_TID3 w__4)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__8 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__6) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T0 == 1#1) : Bool))) ) : SailM Bool )
          if (w__8 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__12 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T0 == 1#1) : Bool))) ) : SailM Bool )
              if (w__12 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__16 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__14) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TID3 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__16 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__20 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TID3 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__20 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__21 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
                          (R_set t w__21))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__22 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
              (R_set t w__22))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__23 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__23))
              else (pure (())))))


end ArmFull.Functions
