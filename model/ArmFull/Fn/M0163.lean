import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0036
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0056
import ArmFull.Fn.M0066
import ArmFull.Fn.M0069
import ArmFull.Fn.M0075
import ArmFull.Fn.M0076
import ArmFull.Fn.M0079
import ArmFull.Fn.M0086
import ArmFull.Fn.M0092
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0150

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
def ICC_SRE_EL3_SysRegWrite_b650b212ede313fc (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg ICC_SRE_EL3 (Mk_ICC_SRE_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MAIR2_EL3_SysRegWrite_47b59b09cadb288b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MAIR2_EL3 (Mk_MAIR2_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MAIR_EL3_SysRegWrite_77100e09b4275a77 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MAIR_EL3 (Mk_MAIR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MDCR_EL3_SysRegWrite_83616ee112453f2c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MDCR_EL3 (Mk_MDCR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MECID_RL_A_EL3_SysRegWrite_be910360ddec275a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MECID_RL_A_EL3 (Mk_MECID_RL_A_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MFAR_EL3_SysRegWrite_036c1c3c4a295873 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg MFAR_EL3 (Mk_MFAR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAM3_EL3_SysRegWrite_350da3ad09fd23ed (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (__set_MPAM3_EL3 (Mk_MPAM3_EL3_Type w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def NZCV_SysRegWrite_a24ec14709a57410 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      let split_vec := (Sail.BitVec.extractLsb w__1 31 28)
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          let split_vec := (Sail.BitVec.extractLsb w__6 31 28)
          let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__7 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
          let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__8 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
          let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__9 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
          let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__10 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__11 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              let split_vec := (Sail.BitVec.extractLsb w__11 31 28)
              let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__12 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
              let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__13 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
              let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__14 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
              let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__15 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__16 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  let split_vec := (Sail.BitVec.extractLsb w__16 31 28)
                  let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__17 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
                  let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__18 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
                  let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__19 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
                  let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__20 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PAN_SysRegWrite_2264c0f921011765 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__1 with PAN := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2
                22)])) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg PSTATE { w__3 with PAN := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__4 22)])) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PSTATE { w__5 with PAN := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        w__6 22)])) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PIR_EL3_SysRegWrite_159b4ed98919a7a7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PIR_EL3 (Mk_PIR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PM_SysRegWrite_b080c52627d6ad22 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__1 with PM := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2 32)])) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg PSTATE { w__3 with PM := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__4 32)])) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PSTATE { w__5 with PM := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        w__6 32)])) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def POR_EL3_SysRegWrite_09c8bd91786b4cc2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg POR_EL3 (Mk_POR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RMR_EL1_SysRegWrite_f5cc0dff5c1c57d6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__0.EL == EL1) : Bool)))) && ((IsHighestEL EL1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg RMR_EL1 (Mk_RMR_EL1_Type w__2))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RMR_EL3_SysRegWrite_d2303115883d7964 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__0.EL == EL3) : Bool)))) && ((IsHighestEL EL3) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg RMR_EL3 (Mk_RMR_EL3_Type w__2))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def SCR_EL3_SysRegWrite_b664c319973b52d6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SCR_EL3 (Mk_SCR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SCTLR2_EL3_SysRegWrite_78fc138b1a53fb7d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SCTLR2_EL3 (Mk_SCTLR2_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SCTLR_EL3_SysRegWrite_5a24dde2d7f68746 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SCTLR_EL3 (Mk_SCTLR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SCXTNUM_EL3_SysRegWrite_5070eac7134cb9ba (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SCXTNUM_EL3 w__1)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SDER32_EL3_SysRegWrite_b1dc0570bf04f2cb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if (((! (HaveEL EL3)) || (! (HaveAArch32EL EL1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
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
                      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (SDER32_EL3_write (Mk_SDER32_EL3_Type w__1)))
                  else (pure (()))))))


/-- Type quantifiers: t : Int -/
def SPMACCESSR_EL3_SysRegWrite_01596d02a5af2d0d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SPMACCESSR_EL3 (Mk_SPMACCESSR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPMROOTCR_EL3_SysRegWrite_0baeba57352c9f52 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
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
                  let w__1 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
                  let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (pure ((SPMROOTCR_EL3_set (BitVec.toNat (_get_SPMSELR_EL0_Type_SYSPMUSEL w__1))
                      w__2))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SPSel_SysRegWrite_0f30d004facde41d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__1 with SP := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2 0)])) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg PSTATE { w__3 with SP := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__4 0)])) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PSTATE { w__5 with SP := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        w__6 0)])) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SP_EL0_SysRegWrite_eb3954d261630177 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_SP : (BitVec 1) := w__1.SP
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((__PSTATE_SP == 0#1) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg SP_EL0 w__2))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__PSTATE_SP == 0#1) : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg SP_EL0 w__3))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__PSTATE_SP == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      writeReg SP_EL0 w__4))
              else (pure (())))))


end ArmFull.Functions
