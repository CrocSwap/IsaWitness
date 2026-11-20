module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0198
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1243
public import ArmFull.Fn.M1244 set_option backward.proofsInPublic true @[expose] public section

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

def decode_cpyptn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:8493.58-8493.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpyptrn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:8550.58-8550.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpyptwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:8607.58-8607.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpypwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:8664.58-8664.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpypwt_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:8721.58-8721.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpypwtn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:8778.58-8778.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpypwtrn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:8835.58-8835.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpypwtwn_aarch64_instrs_memory_mcpymset_cpy (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:8892.58-8892.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpy (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpyfp_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:9092.58-9092.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpyfpn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:9149.58-9149.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpyfprn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:9206.58-9206.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpyfprt_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:9263.58-9263.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpyfprtn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:9320.58-9320.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_cpyfprtrn_aarch64_instrs_memory_mcpymset_cpyf (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (op1 : (BitVec 2)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
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
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if (((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (s == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:9377.58-9377.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_cpyf (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


end ArmFull.Functions
