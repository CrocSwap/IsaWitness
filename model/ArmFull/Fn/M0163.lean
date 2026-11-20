module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0069
public import ArmFull.Fn.M0079
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0143
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
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
  let w__3 ← (( do
    if ((← do
         let w__1 ← (( do (HaveEL EL3) ) : SailM Bool )
         (pure (((! w__1) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__2 ← (( do (HaveAArch32EL EL1) ) : SailM Bool )
        (pure (((! w__2) : Bool)))) ) : SailM Bool )
  if (w__3 : Bool)
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
                      let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (SDER32_EL3_write (Mk_SDER32_EL3_Type w__4)))
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


/-- Type quantifiers: t : Int -/
def SP_EL2_SysRegWrite_ff905d2134243823 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg SP_EL2 w__1)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def SSBS_SysRegWrite_9913e9eaee3498e8 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg PSTATE { w__1 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2 12)])) })
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__3 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__4
                12)])) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg PSTATE { w__5 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__6 12)])) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PSTATE { w__7 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        w__8 12)])) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TCO_SysRegWrite_ad1525aaa3fbe60d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__2 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
      writeReg PSTATE { w__1 with TCO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2 25)])) })
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
          writeReg PSTATE { w__3 with TCO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__4
                25)])) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg PSTATE { w__5 with TCO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__6 25)])) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__8 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PSTATE { w__7 with TCO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        w__8 25)])) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TCR_EL3_SysRegWrite_7cd20b115677d482 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg TCR_EL3 (Mk_TCR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TFSR_EL3_SysRegWrite_f3f90e5ae77101da (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg TFSR_EL3 (Mk_TFSR_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TPIDR_EL3_SysRegWrite_ea00df52cbaac80c (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg TPIDR_EL3 w__1)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TTBR0_EL3_SysRegWrite_3f52a3edf2b13467 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg TTBR0_EL3 (Mk_TTBR0_EL3_Type w__1))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def UAO_SysRegWrite_3265e241e210a049 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
          writeReg PSTATE { w__1 with UAO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__2
                23)])) })
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
              let w__4 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              writeReg PSTATE { w__3 with UAO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__4 23)])) })
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                  let w__6 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  writeReg PSTATE { w__5 with UAO := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        w__6 23)])) })
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def VBAR_EL3_SysRegWrite_a4ea3bd6f4a6393d (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  writeReg VBAR_EL3 w__1)
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CIGDPAPA_SysOpsWrite_04c6858387bf2414 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (pure ((DC_CIGDPAPA w__1))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DC_CIPAPA_SysOpsWrite_bec4067ecaf3ce6b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                  (pure ((DC_CIPAPA w__1))))
              else (pure (())))))


/-- Type quantifiers: k_isRNDRRS : Bool -/
def genRandomNum (isRNDRRS : Bool) : SailM (BitVec 64) := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb 0b0000#4 3 3) }
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb 0b0000#4 2 2) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb 0b0000#4 1 1) }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb 0b0000#4 0 0) }
  let w__4 ← (( do readReg __cycle_count ) : SailM Int )
  let x : (BitVec 128) := (integer_subrange w__4 127 0)
  let w__5 ← (( do readReg __cycle_count ) : SailM Int )
  let y : (BitVec 128) := (integer_subrange (w__5 +i 1) 127 0)
  let w__6 ← (( do readReg __cycle_count ) : SailM Int )
  let w : (BitVec 128) := (integer_subrange (w__6 +i 2) 127 0)
  let w__7 ← (( do (SHA256hash x y w true) ) : SailM (BitVec 128) )
  (pure ((Sail.BitVec.extractLsb w__7 63 0)))


def CacheConfigRead (cache_sel : (BitVec 4)) : SailM (BitVec 64) := do
  let data_cache : Bool :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cache_sel 0)])) == 0#1) : Bool)
    then true
    else false
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb cache_sel 3 1))
  ArmFull.assert (level <b 7) "sail-inputs/12-sysregs.sail:253.20-253.21"
  (getCacheID level data_cache)


def decode_aarch32_instrs_SETPAN_A1enc_A_txt (imm1 : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HavePANExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let value_name : (BitVec 1) := imm1
  (execute_aarch32_instrs_SETPAN_Op_A_txt value_name)


def decode_aarch32_instrs_TSB_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:46053.29-46053.30"
      let w__1 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (EndOfInstruction ()))
      else (pure (()))
      if ((cond != 0b1110#4) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (pure ((execute_aarch32_instrs_TSB_Op_A_txt ()))))
  else (pure (()))


def decode_aarch32_instrs_CLRBHB_A1enc_A_txt (cond : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:47977.29-47977.30"
      let w__1 ← (( do (HaveFeatCLRBHB ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (EndOfInstruction ()))
      else (pure (()))
      (pure ((execute_aarch32_instrs_CLRBHB_Op_A_txt ()))))
  else (pure (()))


def decode_aarch32_instrs_CLRBHB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveFeatCLRBHB ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (EndOfInstruction ()))
      else (pure (()))
      (pure ((execute_aarch32_instrs_CLRBHB_Op_A_txt ()))))
  else (pure (()))


end ArmFull.Functions
