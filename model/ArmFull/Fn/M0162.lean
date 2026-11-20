module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0037
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0073
public import ArmFull.Fn.M0077
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0149 set_option backward.proofsInPublic true @[expose] public section

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
def CNTHCTL_EL2_SysRegWrite_c57f8627acf05dc2 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_E2H : (BitVec 1) := (_get_HCR_EL2_Type_E2H w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__2))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              if ((__HCR_EL2_E2H == 1#1) : Bool)
              then
                (do
                  let w__3 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTHCTL_EL2 (Mk_CNTHCTL_EL2_Type w__3))
              else
                (do
                  let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg CNTKCTL_EL1 (Mk_CNTKCTL_EL1_Type w__5))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CPTR_EL3_SysRegWrite_3835d83d048c2034 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg CPTR_EL3 (Mk_CPTR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DIT_SysRegWrite_cb82290c1722296d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg PSTATE { w__1 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2 24)])) })
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__3 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__4
                24)])) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg PSTATE { w__5 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__6 24)])) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PSTATE { w__7 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        w__8 24)])) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DLR_EL0_SysRegWrite_7614507cf751cf9d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg DLR_EL0 w__1)


/-- Type quantifiers: t : Int -/
def DSPSR_EL0_SysRegWrite_2829d14e4c67df55 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg DSPSR_EL0 (Mk_DSPSR_EL0_Type w__1))


/-- Type quantifiers: t : Int -/
def ESR_EL3_SysRegWrite_d8e4dd481971160d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg ESR_EL3 (Mk_ESR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def FAR_EL3_SysRegWrite_d150ecea5bb2beb8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg FAR_EL3 w__1)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSCR_EL3_SysRegWrite_7d39fd6ab827245b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg GCSCR_EL3 (Mk_GCSCR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GCSPR_EL3_SysRegWrite_2c3789955c87eb01 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg GCSPR_EL3 (Mk_GCSPR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GPCCR_EL3_SysRegWrite_34a621e690dc851f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (__set_GPCCR_EL3 (Mk_GPCCR_EL3_Type w__1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def GPTBR_EL3_SysRegWrite_6f7a8066a1cb6176 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg GPTBR_EL3 (Mk_GPTBR_EL3_Type w__1))
              else (pure (())))))


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


end ArmFull.Functions
