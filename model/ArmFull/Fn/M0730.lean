import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0054
import ArmFull.Fn.M0058
import ArmFull.Fn.M0059
import ArmFull.Fn.M0082
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0202
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
def AMEVTYPER1_SysRegWrite32_4c73d953aff0e20b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 15) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 15 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_4f4eada85dcde70a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 0) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 0 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_5157ae2713cc2d9d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 9) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 9 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_5a1635be7bbcd05b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 11 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_a868a5149842a50f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 12) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 12 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_c08be1aaf0c6ac78 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 8 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_cb60b5ebc90e745e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 14) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 14 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_d066b294b71fc9c6 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 2) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 2 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_d612c920e0f1e095 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 6) ) : SailM Bool )
  if ((! w__2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__8 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__3.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__6 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                  (pure (((! w__6) : Bool))))
              else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__9.EL == EL1) : Bool)))) : Bool)
                       then
                         (do
                           (EL2Enabled ()))
                       else (pure false)) : Bool)
                  then
                    (do
                      (ELUsingAArch32 EL2))
                  else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
          if (w__14 : Bool)
          then
            (do
              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
          else
            (do
              let w__17 ← (( do
                if ((← do
                     let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                     (pure (((IsHighestEL w__15.EL) : Bool)))) : Bool)
                then
                  (do
                    let w__16 ← (( do (__IMPDEF_boolean "AMEVCNTR1[m] is fixed") ) : SailM Bool )
                    (pure (((! w__16) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  let w__18 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AMEVTYPER1_set 6 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


end ArmFull.Functions
