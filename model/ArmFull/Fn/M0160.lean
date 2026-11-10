import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0100
import ArmFull.Fn.M0113
import ArmFull.Fn.M0139
import ArmFull.Fn.M0140
import ArmFull.Fn.M0144

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
def DIT_SysRegRead_80b5d608e76aa495 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (X_set t 64 (((Zeros (n := 39)) +++ w__1.DIT) +++ (Zeros (n := 24)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          (X_set t 64 (((Zeros (n := 39)) +++ w__2.DIT) +++ (Zeros (n := 24)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
              (X_set t 64 (((Zeros (n := 39)) +++ w__3.DIT) +++ (Zeros (n := 24)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
                  (X_set t 64 (((Zeros (n := 39)) +++ w__4.DIT) +++ (Zeros (n := 24)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DLR_EL0_SysRegRead_635696e4f590448d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg DLR_EL0 ) : SailM (BitVec 64) )
      (X_set t 64 w__1))


/-- Type quantifiers: t : Int -/
def DSPSR_EL0_SysRegRead_e92e924519c42368 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do readReg DSPSR_EL0 ) : SailM (BitVec 64) )
      (X_set t 64 (__get_DSPSR_EL0 w__1)))


/-- Type quantifiers: t : Int -/
def ELR_EL3_SysRegRead_48156757f03c05da (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg ELR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ESR_EL3_SysRegRead_ba1b08f3b6ea1fa7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg ESR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ESR_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def FAR_EL3_SysRegRead_5f326570429f53a6 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg FAR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSCR_EL3_SysRegRead_f722c361b12a49bd (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_GCSCR_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPR_EL3_SysRegRead_3f6b8f8e31fb3882 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg GCSPR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_GCSPR_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GPCCR_EL3_SysRegRead_709f878e2648a87d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_GPCCR_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GPTBR_EL3_SysRegRead_fe0f38a8cd7c60a9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg GPTBR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_GPTBR_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICC_SRE_EL3_SysRegRead_7a177b6c72e9cd7e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_ICC_SRE_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MAIR2_EL3_SysRegRead_06e8ce86a19999af (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg MAIR2_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MAIR_EL3_SysRegRead_3a3602f6f0c9e03f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg MAIR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MDCR_EL3_SysRegRead_fa75e32e1a0e4d27 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MDCR_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MECIDR_EL2_SysRegRead_22d6791638dc141a (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          then
            (do
              let w__1 ← (( do readReg MECIDR_EL2 ) : SailM (BitVec 64) )
              (X_set t 64 (__get_MECIDR_EL2 w__1)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__2 ← (( do readReg MECIDR_EL2 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MECIDR_EL2 w__2)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MECID_RL_A_EL3_SysRegRead_50a71cb28bab1988 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg MECID_RL_A_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MECID_RL_A_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MFAR_EL3_SysRegRead_6520d659502d749b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg MFAR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MFAR_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def MPAM3_EL3_SysRegRead_2770962b9f8f46c1 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
                  (X_set t 64 (__get_MPAM3_EL3 w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def NZCV_SysRegRead_66dd3f91dc048279 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      (X_set t 64
        (((Zeros (n := 32)) +++ (w__1.N +++ (w__2.Z +++ (w__3.C +++ w__4.V)))) +++ (Zeros (n := 28)))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
          (X_set t 64
            (((Zeros (n := 32)) +++ (w__5.N +++ (w__6.Z +++ (w__7.C +++ w__8.V)))) +++ (Zeros
                (n := 28)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
              (X_set t 64
                (((Zeros (n := 32)) +++ (w__9.N +++ (w__10.Z +++ (w__11.C +++ w__12.V)))) +++ (Zeros
                    (n := 28)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
                  (X_set t 64
                    (((Zeros (n := 32)) +++ (w__13.N +++ (w__14.Z +++ (w__15.C +++ w__16.V)))) +++ (Zeros
                        (n := 28)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PAN_SysRegRead_ffa7ce033244778f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          (X_set t 64 (((Zeros (n := 41)) +++ w__1.PAN) +++ (Zeros (n := 22)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
              (X_set t 64 (((Zeros (n := 41)) +++ w__2.PAN) +++ (Zeros (n := 22)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                  (X_set t 64 (((Zeros (n := 41)) +++ w__3.PAN) +++ (Zeros (n := 22)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PIR_EL3_SysRegRead_1dc2ca24d5a22e66 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg PIR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def PM_SysRegRead_801ea1615b4051f7 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          (X_set t 64 (((Zeros (n := 31)) +++ w__1.PM) +++ (Zeros (n := 32)))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
              (X_set t 64 (((Zeros (n := 31)) +++ w__2.PM) +++ (Zeros (n := 32)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                  (X_set t 64 (((Zeros (n := 31)) +++ w__3.PM) +++ (Zeros (n := 32)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def POR_EL3_SysRegRead_dd4204e711df2c15 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  let w__1 ← (( do readReg POR_EL3 ) : SailM (BitVec 64) )
                  (X_set t 64 w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RMR_EL1_SysRegRead_9adb359c4ff7cc32 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__0.EL == EL1) : Bool)))) && ((IsHighestEL EL1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
      (X_set t 64 (__get_RMR_EL1 w__2)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RMR_EL3_SysRegRead_412ca53e076c7a6e (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__0.EL == EL3) : Bool)))) && ((IsHighestEL EL3) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
      (X_set t 64 (__get_RMR_EL3 w__2)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RVBAR_EL1_SysRegRead_c839c12def98ebc4 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__0.EL == EL1) : Bool)))) && ((IsHighestEL EL1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do readReg RVBAR_EL1 ) : SailM (BitVec 64) )
      (X_set t 64 w__2))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def RVBAR_EL3_SysRegRead_d57b9abefb0ea569 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__0.EL == EL3) : Bool)))) && ((IsHighestEL EL3) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do readReg RVBAR_EL3 ) : SailM (BitVec 64) )
      (X_set t 64 w__2))
  else sailThrow ((Error_Undefined ()))


end ArmFull.Functions
