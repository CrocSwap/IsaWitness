import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0019
import ArmFull.Fn.M0117
import ArmFull.Fn.M0146
import ArmFull.Fn.M0198
import ArmFull.Fn.M1182
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

def decode_cpypn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4061) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8094.58-8094.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyprn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4062) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8151.58-8151.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyprt_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4063) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8208.58-8208.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyprtn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4064) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8265.58-8265.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyprtrn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4065) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8322.58-8322.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyprtwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4066) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8379.58-8379.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpypt_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4067) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8436.58-8436.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyptn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4068) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8493.58-8493.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyptrn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4069) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8550.58-8550.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyptwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4070) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8607.58-8607.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpypwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4071) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8664.58-8664.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpypwt_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4072) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8721.58-8721.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpypwtn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4073) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8778.58-8778.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpypwtrn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4074) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8835.58-8835.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpypwtwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4075) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:8892.58-8892.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfp_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4079) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:9092.58-9092.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


def decode_cpyfpn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
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
  let stage ← (( do (undefined_MOPSStage (← occLabel 4080) ()) ) : SailM MOPSStage )
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
      ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:9149.58-9149.59"
      match c with
      | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
      | .Constraint_NOP =>
        (do
          (EndOfInstruction ()))
      | _ => (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)


end ArmFull.Functions
