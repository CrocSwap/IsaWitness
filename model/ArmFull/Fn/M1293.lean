import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0019
import ArmFull.Fn.M0086
import ArmFull.Fn.M0117
import ArmFull.Fn.M0146
import ArmFull.Fn.M0198
import ArmFull.Fn.M1183

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

def decode_cpyfprn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4081) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9206.58-9206.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfprt_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4082) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9263.58-9263.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfprtn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4083) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9320.58-9320.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfprtrn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4084) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9377.58-9377.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfprtwn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4085) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9434.58-9434.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfpt_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4086) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9491.58-9491.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfptn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4087) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9548.58-9548.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfptrn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4088) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9605.58-9605.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfptwn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4089) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9662.58-9662.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfpwn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4090) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9719.58-9719.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfpwt_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4091) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9776.58-9776.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfpwtn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4092) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9833.58-9833.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfpwtrn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4093) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9890.58-9890.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfpwtwn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((sz != 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let s : Int := (BitVec.toNat Rs)
  let n : Int := (BitVec.toNat Rn)
  let options_name : (BitVec 4) := op2
  let stage ← (( do (undefined_MOPSStage (← occLabel 4094) ()) ) : SailM MOPSStage )
  let stage ← (( do
    match op1 with
    | 0b00 => (pure (MOPSStage_Prologue))
    | 0b01 => (pure (MOPSStage_Main))
    | 0b10 => (pure (MOPSStage_Epilogue))
    | _ => sailThrow ((Error_See "Memory Copy and Memory Set")) ) : SailM MOPSStage )
  let stage := stage
  (CheckMOPSEnabled ())
  if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-arm/instrs64.sail:9947.58-9947.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_add_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp := ReduceOp_FADD
  (execute_aarch64_instrs_vector_reduce_fp16_add_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


def decode_faddp_advsimd_pair_aarch64_instrs_vector_reduce_fp_add_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp := ReduceOp_FADD
  (execute_aarch64_instrs_vector_reduce_fp16_add_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


def decode_fmaxp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp16_max_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  if ((sz == 1#1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


def decode_fminp_advsimd_pair_aarch64_instrs_vector_reduce_fp_max_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let datasize : Int := (esize *i 2)
  let elements : Nat := 2
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_sisd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n))
    op)


def decode_fmaxv_advsimd_aarch64_instrs_vector_reduce_fp16_max_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o1 : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  if ((! (HaveFP16Ext ())) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let esize : Nat := 16
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let op : ReduceOp :=
    if ((o1 == 1#1) : Bool)
    then ReduceOp_FMIN
    else ReduceOp_FMAX
  (execute_aarch64_instrs_vector_reduce_fp16_max_simd (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (n)) op)


end ArmFull.Functions
