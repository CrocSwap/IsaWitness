import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0040
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0052
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0099
import ArmFull.Fn.M0112
import ArmFull.Fn.M0115
import ArmFull.Fn.M0118
import ArmFull.Fn.M0124
import ArmFull.Fn.M0143
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0151

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
  ArmFull.assert (level <b 7) "/home/doug/boss-scratch/sail-lean-fork/integ/model/sysregs.sail:253.20-253.21"
  (getCacheID level data_cache)


def SetResetVector (value_name : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      if ((HaveEL EL3) : Bool)
      then
        (do
          writeReg MVBAR (Mk_MVBAR_Type ((Sail.BitVec.extractLsb value_name 31 1) +++ 1#1)))
      else
        (do
          writeReg RVBAR ((Sail.BitVec.extractLsb value_name 31 1) +++ 1#1)))
  else
    (do
      if (((HighestEL ()) == EL3) : Bool)
      then
        (do
          writeReg RVBAR_EL3 (Mk_RVBAR_EL3_Type value_name))
      else
        (do
          if (((HighestEL ()) == EL2) : Bool)
          then
            (do
              writeReg RVBAR_EL2 (Mk_RVBAR_EL2_Type value_name))
          else
            (do
              writeReg RVBAR_EL1 (Mk_RVBAR_EL1_Type value_name))))


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
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:46053.29-46053.30"
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
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:47977.29-47977.30"
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


/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_unary_abs (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result : Nat := (Int.natAbs (BitVec.toInt operand1))
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, k_setflags : Bool, k_sub_op : Bool, 0
  ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_carry (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (setflags : Bool) (sub_op : Bool) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3913)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3914) 4) ) : SailM (BitVec 4) )
  let operand2 : (BitVec datasize) :=
    if (sub_op : Bool)
    then (Complement.complement operand2)
    else operand2
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) :=
    ((AddWithCarry operand1 operand2 w__0.C) : ((BitVec datasize) × (BitVec 4)))
  let result : (BitVec datasize) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if (setflags : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, k_setflags : Bool, k_sub_op : Bool, 0 ≤ n
  ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_immediate (d : Nat) (datasize : Nat) (imm : (BitVec datasize)) (n : Nat) (setflags : Bool) (sub_op : Bool) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3921)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        let w__0 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
        (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)))))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (X_read n datasize))) ) : SailM (BitVec datasize) )
  let operand2 : (BitVec datasize) := imm
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3922) 4) ) : SailM (BitVec 4) )
  let carry_in ← (( do (undefined_bitvector_at (← occLabel 3923) 1) ) : SailM (BitVec 1) )
  let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
    if (sub_op : Bool)
    then
      (let operand2 : (BitVec datasize) := (Complement.complement operand2)
      let carry_in : (BitVec 1) := 1#1
      (carry_in, operand2))
    else
      (let carry_in : (BitVec 1) := 0#1
      (carry_in, operand2))
  let (tup__0, tup__1) :=
    ((AddWithCarry operand1 operand2 carry_in) : ((BitVec datasize) × (BitVec 4)))
  let result : (BitVec datasize) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if (setflags : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))
  if (((d == 31) && (! setflags)) : Bool)
  then
    (do
      (SP_set (Sail.BitVec.zeroExtend result 64)))
  else
    (do
      (X_set d datasize (Sail.BitVec.castWidth result)))


/-- Type quantifiers: d : Nat, k_page : Bool, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_address_pc_rel (d : Nat) (imm : (BitVec 64)) (page : Bool) : SailM Unit := do
  let base ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  let base : (BitVec 64) :=
    if (page : Bool)
    then (Sail.BitVec.updateSubrange base 11 0 (Zeros (n := 12)))
    else base
  (X_set d 64 (base + imm))


/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_logical_immediate (d : Nat) (datasize : Nat) (imm : (BitVec datasize)) (n : Nat) (op : LogicalOp) (setflags : Bool) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3943)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 : (BitVec datasize) := imm
  let result : (BitVec datasize) :=
    match op with
    | .LogicalOp_AND => (operand1 &&& operand2)
    | .LogicalOp_ORR => (operand1 ||| operand2)
    | .LogicalOp_EOR => (operand1 ^^^ operand2)
  let result := result
  if (setflags : Bool)
  then
    (do
      let split_vec :=
        (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                (Sail.Int.toNatChecked ((datasize -i 1))))])) +++ (IsZeroBit result)) +++ 0b00#2)
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  if (((d == 31) && (! setflags)) : Bool)
  then
    (do
      (SP_set (Sail.BitVec.zeroExtend result 64)))
  else
    (do
      (X_set d datasize (Sail.BitVec.castWidth result)))


def decode_axflag_aarch64_instrs_integer_flags_axflag (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFlagFormatExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_integer_flags_axflag ())


/-- Type quantifiers: d : Nat, datasize : Nat, k_extend : Bool, k_inzero : Bool, n : Nat, r : Nat, s
  : Nat, 0 ≤ s ∧
  s ≤ 63 ∧
  0 ≤ r ∧
  r ≤ 63 ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_bitfield (d : Nat) (datasize : Nat) (extend : Bool) (inzero : Bool) (n : Nat) (r : Nat) (s : Nat) (tmask : (BitVec datasize)) (wmask : (BitVec datasize)) : SailM Unit := do
  let dst ← (( do
    if (inzero : Bool)
    then (pure ((Sail.BitVec.castWidth (Zeros (n := datasize)))))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (X_read d datasize))) ) : SailM (BitVec datasize) )
  let src ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM (BitVec datasize) )
  let bot : (BitVec datasize) :=
    ((dst &&& (Complement.complement wmask)) ||| ((ROR src r) &&& wmask))
  let top ← (( do
    if (extend : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b s) && (s <b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:2923.53-2923.54"
        (pure ((Sail.BitVec.castWidth (BitVec.replicateBits
            (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access src s)])) datasize)))))
    else (pure (dst)) ) : SailM (BitVec datasize) )
  (X_set d datasize
    (Sail.BitVec.castWidth ((top &&& (Complement.complement tmask)) ||| (bot &&& tmask))))


/-- Type quantifiers: datasize : Nat, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_integer_conditional_compare_register (condition : (BitVec 4)) (datasize : Nat) (flags__arg : (BitVec 4)) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  let flags : (BitVec 4) := flags__arg
  let taken : Bool := false
  let w__0 ← (( do (ConditionHolds condition) ) : SailM Bool )
  let (flags, taken) ← (( do
    if (w__0 : Bool)
    then
      (do
        let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
          (BitVec datasize) )
        let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
          (BitVec datasize) )
        let carry_in : (BitVec 1) := 0#1
        let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
          if (sub_op : Bool)
          then
            (let operand2 : (BitVec datasize) := (Complement.complement operand2)
            let carry_in : (BitVec 1) := 1#1
            (carry_in, operand2))
          else (carry_in, operand2)
        let (_, __tup_1) := (AddWithCarry operand1 operand2 carry_in)
        let flags : (BitVec 4) := __tup_1
        let taken : Bool := true
        (pure ((flags, taken))))
    else (pure ((flags, taken))) ) : SailM ((BitVec 4) × Bool) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb flags 3 3) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb flags 2 2) }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb flags 1 1) }
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb flags 0 0) }
  let w__5 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let conditional : Bool := true
      (SPESampleAddOpOther conditional taken))
  else (pure (()))


end ArmFull.Functions
