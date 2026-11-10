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
import ArmFull.Fn.M0071
import ArmFull.Fn.M0074
import ArmFull.Fn.M0075
import ArmFull.Fn.M0079
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
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
def CNTHPS_CVAL_EL2_SysRegRead_d2662865ff7936c3 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__3) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__6 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__6) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__7 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__7)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__8 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__8)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHPS_TVAL_EL2_SysRegRead_893c5b3a9908faeb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHPS_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHPS_CTL_EL2_Type_ENABLE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__4) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__6 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__6 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__7 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__7) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__8 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__8))
                  else
                    (do
                      let w__9 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
                      let w__10 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHPS_TVAL_EL2 (Mk_CNTHPS_TVAL_EL2_Type (w__9 - w__10)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__CNTHPS_CTL_EL2_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__11 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__11))
                      else
                        (do
                          let w__12 ← (( do readReg CNTHPS_CVAL_EL2 ) : SailM (BitVec 64) )
                          let w__13 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_CNTHPS_TVAL_EL2 (Mk_CNTHPS_TVAL_EL2_Type (w__12 - w__13)))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHP_CTL_EL2_SysRegRead_fc0ab47b2d1292cd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CNTHP_CTL_EL2 w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTHP_CTL_EL2 w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHP_CVAL_EL2_SysRegRead_5a841847b0720163 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_EL2_SysRegRead_ddcf2e9dd3ff2611 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHP_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHP_CTL_EL2_Type_ENABLE w__2)
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
              if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
              then
                (do
                  let w__5 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else
                (do
                  let w__6 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
                  let w__7 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTHP_TVAL_EL2 (Mk_CNTHP_TVAL_EL2_Type (w__6 - w__7))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTHP_CTL_EL2_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__8 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__8))
                  else
                    (do
                      let w__9 ← (( do readReg CNTHP_CVAL_EL2 ) : SailM (BitVec 64) )
                      let w__10 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHP_TVAL_EL2 (Mk_CNTHP_TVAL_EL2_Type (w__9 - w__10))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHVS_CTL_EL2_SysRegRead_46708ffedf6618c4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__3) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__6 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__6) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__7 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTHVS_CTL_EL2 w__7))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__8 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHVS_CTL_EL2 w__8))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHVS_CVAL_EL2_SysRegRead_e87d470dc26af07a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__2)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__3) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__5 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__6 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__6) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__7 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__7)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__8 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64 w__8)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHVS_TVAL_EL2_SysRegRead_7b30facaa926411e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_NV : (BitVec 1) := (_get_HCR_EL2_Type_NV w__1)
  let w__2 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHVS_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHVS_CTL_EL2_Type_ENABLE w__2)
  let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EEL2 : (BitVec 1) := (_get_SCR_EL3_Type_EEL2 w__3)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__4 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
          if ((! w__4) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__6 ← (( do
                (pure ((← do
                      (EL2Enabled ())) && ((__HCR_EL2_NV == 1#1) : Bool))) ) : SailM Bool )
              if (w__6 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else sailThrow ((Error_Undefined ()))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__7 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
              if ((! w__7) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__8 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__8))
                  else
                    (do
                      let w__9 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                      let w__10 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHVS_TVAL_EL2 (Mk_CNTHVS_TVAL_EL2_Type (w__9 - w__10)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_EL3_EEL2 == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__11 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__11))
                      else
                        (do
                          let w__12 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                          let w__13 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_CNTHVS_TVAL_EL2 (Mk_CNTHVS_TVAL_EL2_Type (w__12 - w__13)))))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHV_CTL_EL2_SysRegRead_fe7c25cca2e88b3f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_CNTHV_CTL_EL2 w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_CNTHV_CTL_EL2 w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHV_CVAL_EL2_SysRegRead_7bb539c281c21387 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
              let w__4 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 w__4))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHV_TVAL_EL2_SysRegRead_131a29f8b5d31ce1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  let __CNTKCTL_EL1_EL0VTEN : (BitVec 1) := (_get_CNTKCTL_EL1_Type_EL0VTEN w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL0VTEN : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL0VTEN w__3)
  let w__4 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHCTL_EL2_EL1TVT : (BitVec 1) := (_get_CNTHCTL_EL2_Type_EL1TVT w__4)
  let w__5 ← (( do readReg CNTHVS_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHVS_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHVS_CTL_EL2_Type_ENABLE w__5)
  let w__6 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
  let __CNTHV_CTL_EL2_ENABLE : (BitVec 1) := (_get_CNTHV_CTL_EL2_Type_ENABLE w__6)
  let w__7 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  let __CNTV_CTL_EL0_ENABLE : (BitVec 1) := (_get_CNTV_CTL_EL0_Type_ENABLE w__7)
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
              (pure (((! w__11) : Bool)))) && ((__CNTKCTL_EL1_EL0VTEN == 0#1) : Bool))) ) : SailM
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
          let w__19 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__17 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__16) +++ (_get_HCR_EL2_Type_TGE w__17)) == 0b11#2) : Bool))))
                  else (pure false)) && ((__CNTHCTL_EL2_EL0VTEN == 0#1) : Bool))) ) : SailM Bool )
          if (w__19 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__24 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          let w__22 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure (((((_get_HCR_EL2_Type_E2H w__21) +++ (_get_HCR_EL2_Type_TGE w__22)) != 0b11#2) : Bool))))
                      else (pure false)) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool
                )
              if (w__24 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__32 ← (( do
                    if ((← do
                         if ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  let w__27 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                  (pure (((((_get_HCR_EL2_Type_E2H w__26) +++ (_get_HCR_EL2_Type_TGE
                                          w__27)) == 0b11#2) : Bool))))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__29 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_NS w__29) == 0#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        (IsFeatureImplemented FEAT_SEL2))
                    else (pure false) ) : SailM Bool )
                  if (w__32 : Bool)
                  then
                    (do
                      if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__33 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__33))
                      else
                        (do
                          let w__34 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                          let w__35 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__34 - w__35))))))
                  else
                    (do
                      let w__41 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__37 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                 (pure (((((_get_HCR_EL2_Type_E2H w__37) +++ (_get_HCR_EL2_Type_TGE
                                         w__38)) == 0b11#2) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__40 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                            (pure ((((_get_SCR_EL3_Type_NS w__40) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__41 : Bool)
                      then
                        (do
                          if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
                          then
                            (do
                              let w__42 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                              (X_set t 64 w__42))
                          else
                            (do
                              let w__43 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                              let w__44 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__43 - w__44))))))
                      else
                        (do
                          let w__49 ← (( do
                            if (((HaveEL EL2) : Bool) : Bool)
                            then
                              (do
                                if ((← do
                                     let w__45 ← (( do (EL2Enabled ()) ) : SailM Bool )
                                     (pure (((! w__45) : Bool)))) : Bool)
                                then (pure true)
                                else
                                  (do
                                    let w__46 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    let w__47 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_HCR_EL2_Type_E2H w__46) +++ (_get_HCR_EL2_Type_TGE
                                            w__47)) != 0b11#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__49 : Bool)
                          then
                            (do
                              if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                              then
                                (do
                                  let w__50 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                                  (X_set t 64 w__50))
                              else
                                (do
                                  let w__51 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                                  let w__52 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  let w__53 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                                  (X_set t 64
                                    (__get_CNTHV_TVAL_EL2
                                      (Mk_CNTHV_TVAL_EL2_Type (w__51 - (w__52 - w__53)))))))
                          else
                            (do
                              if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                              then
                                (do
                                  let w__54 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                                  (X_set t 64 w__54))
                              else
                                (do
                                  let w__55 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                                  let w__56 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                                  (X_set t 64
                                    (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__55 - w__56))))))))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__58 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__CNTHCTL_EL2_EL1TVT == 1#1) : Bool))) ) : SailM Bool )
          if (w__58 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              if ((HaveEL EL2) : Bool)
              then
                (do
                  if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__59 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__59))
                  else
                    (do
                      let w__60 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                      let w__61 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      let w__62 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                      (X_set t 64
                        (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__60 - (w__61 - w__62)))))))
              else
                (do
                  if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__63 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__63))
                  else
                    (do
                      let w__64 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                      let w__65 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__64 - w__65))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__70 ← (( do
                if ((← do
                     if ((← do
                          let w__66 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__66) == 1#1) : Bool)))) : Bool)
                     then
                       (do
                         let w__67 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                         (pure ((((_get_SCR_EL3_Type_NS w__67) == 0#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    (IsFeatureImplemented FEAT_SEL2))
                else (pure false) ) : SailM Bool )
              if (w__70 : Bool)
              then
                (do
                  if ((__CNTHVS_CTL_EL2_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__71 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__71))
                  else
                    (do
                      let w__72 ← (( do readReg CNTHVS_CVAL_EL2 ) : SailM (BitVec 64) )
                      let w__73 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (X_set t 64 (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__72 - w__73))))))
              else
                (do
                  let w__76 ← (( do
                    if ((← do
                         let w__74 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure ((((_get_HCR_EL2_Type_E2H w__74) == 1#1) : Bool)))) : Bool)
                    then
                      (do
                        let w__75 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__75) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__76 : Bool)
                  then
                    (do
                      if ((__CNTHV_CTL_EL2_ENABLE == 0#1) : Bool)
                      then
                        (do
                          let w__77 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                          (X_set t 64 w__77))
                      else
                        (do
                          let w__78 ← (( do readReg CNTHV_CVAL_EL2 ) : SailM (BitVec 64) )
                          let w__79 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__78 - w__79))))))
                  else
                    (do
                      let w__80 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      if (((_get_HCR_EL2_Type_E2H w__80) == 0#1) : Bool)
                      then
                        (do
                          if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                          then
                            (do
                              let w__81 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                              (X_set t 64 w__81))
                          else
                            (do
                              let w__82 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                              let w__83 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              let w__84 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_CNTHV_TVAL_EL2
                                  (Mk_CNTHV_TVAL_EL2_Type (w__82 - (w__83 - w__84)))))))
                      else
                        (do
                          if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                          then
                            (do
                              let w__85 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                              (X_set t 64 w__85))
                          else
                            (do
                              let w__86 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                              let w__87 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__86 - w__87)))))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__CNTV_CTL_EL0_ENABLE == 0#1) : Bool)
                  then
                    (do
                      let w__88 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                      (X_set t 64 w__88))
                  else
                    (do
                      let w__90 ← (( do
                        if (((HaveEL EL2) : Bool) : Bool)
                        then
                          (do
                            let w__89 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                            (pure (((! w__89) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__90 : Bool)
                      then
                        (do
                          let w__91 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                          let w__92 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                          let w__93 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
                          (X_set t 64
                            (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__91 - (w__92 - w__93))))))
                      else
                        (do
                          let w__95 ← (( do
                            if (((HaveEL EL2) : Bool) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL2))
                            else (pure false) ) : SailM Bool )
                          if (w__95 : Bool)
                          then
                            (do
                              let w__96 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                              let w__97 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              let w__98 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_CNTHV_TVAL_EL2
                                  (Mk_CNTHV_TVAL_EL2_Type (w__96 - (w__97 - w__98))))))
                          else
                            (do
                              let w__99 ← (( do readReg CNTV_CVAL_EL0 ) : SailM (BitVec 64) )
                              let w__100 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                              (X_set t 64
                                (__get_CNTHV_TVAL_EL2 (Mk_CNTHV_TVAL_EL2_Type (w__99 - w__100))))))))
              else (pure (())))))


end ArmFull.Functions
