import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
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
def AMCNTENCLR1_SysRegWrite32_54f7ea48fcecb714 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__7 ← (( do
    (pure ((← do
          if ((← do
               if ((← do
                    let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__2.EL == EL1) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              (pure (((! w__5) : Bool))))
          else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
  else
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__8.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  (ELUsingAArch32 EL2))
              else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then
        (do
          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((IsHighestEL w__14.EL) : Bool)
          then
            (do
              let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AMCNTENCLR1_write (Mk_AMCNTENCLR1_Type w__15)))
          else sailThrow ((Error_Undefined ()))))


/-- Type quantifiers: t : Int -/
def AMCNTENSET0_SysRegWrite32_e19916620d98350a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__7 ← (( do
    (pure ((← do
          if ((← do
               if ((← do
                    let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__2.EL == EL1) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              (pure (((! w__5) : Bool))))
          else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
  else
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__8.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  (ELUsingAArch32 EL2))
              else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then
        (do
          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((IsHighestEL w__14.EL) : Bool)
          then
            (do
              let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AMCNTENSET0_write (Mk_AMCNTENSET0_Type w__15)))
          else sailThrow ((Error_Undefined ()))))


/-- Type quantifiers: t : Int -/
def AMCNTENSET1_SysRegWrite32_c9fde2d74a2eae8e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__7 ← (( do
    (pure ((← do
          if ((← do
               if ((← do
                    let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__2.EL == EL1) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              (pure (((! w__5) : Bool))))
          else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
  else
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__8.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  (ELUsingAArch32 EL2))
              else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then
        (do
          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((IsHighestEL w__14.EL) : Bool)
          then
            (do
              let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AMCNTENSET1_write (Mk_AMCNTENSET1_Type w__15)))
          else sailThrow ((Error_Undefined ()))))


/-- Type quantifiers: t : Int -/
def AMCR_SysRegWrite32_0a36aa89c00db4ab (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__7 ← (( do
    (pure ((← do
          if ((← do
               if ((← do
                    let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__2.EL == EL1) : Bool)))) : Bool)
               then
                 (do
                   (EL2Enabled ()))
               else (pure false)) : Bool)
          then
            (do
              let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              (pure (((! w__5) : Bool))))
          else (pure false)) && ((__HSTR_EL2_T13 == 1#1) : Bool))) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
  else
    (do
      let w__13 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                        (pure (((w__8.EL == EL1) : Bool)))) : Bool)
                   then
                     (do
                       (EL2Enabled ()))
                   else (pure false)) : Bool)
              then
                (do
                  (ELUsingAArch32 EL2))
              else (pure false)) && ((__HSTR_T13 == 1#1) : Bool))) ) : SailM Bool )
      if (w__13 : Bool)
      then
        (do
          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
      else
        (do
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          if ((IsHighestEL w__14.EL) : Bool)
          then
            (do
              let w__15 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AMCR_write (Mk_AMCR_Type w__15)))
          else sailThrow ((Error_Undefined ()))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_10f3aef13e8663a1 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 1) ) : SailM Bool )
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
                  (AMEVTYPER1_set 1 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_1c15a0e3b00864c2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 7) ) : SailM Bool )
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
                  (AMEVTYPER1_set 7 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_3549526a1f7ad5a9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
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
                  (AMEVTYPER1_set 4 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_381d8337f3d30ba8 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 5) ) : SailM Bool )
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
                  (AMEVTYPER1_set 5 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_3f6816ffcd57dccb (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
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
                  (AMEVTYPER1_set 13 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


/-- Type quantifiers: t : Int -/
def AMEVTYPER1_SysRegWrite32_405b1a2a28f91a31 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T13 : (BitVec 1) := (_get_HSTR_EL2_Type_T13 w__0)
  let w__1 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T13 : (BitVec 1) := (_get_HSTR_Type_T13 w__1)
  let w__2 ← (( do (IsG1ActivityMonitorImplemented 10) ) : SailM Bool )
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
                  (AMEVTYPER1_set 10 (Mk_AMEVTYPER1_Type w__18)))
              else sailThrow ((Error_Undefined ())))))


end ArmFull.Functions
