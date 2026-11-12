import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0020
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0099
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0152
import ArmFull.Fn.M0165
import ArmFull.Fn.M0166
import ArmFull.Fn.M0169
import ArmFull.Fn.M0170
import ArmFull.Fn.M0171
import ArmFull.Fn.M0172

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

def decode_subs_addsub_shift_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (shift : (BitVec 2)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  if ((shift == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  (execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    setflags (Sail.Int.toNatChecked (shift_amount)) shift_type sub_op)


def decode_add_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) extend_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift)) sub_op)


def decode_adds_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) extend_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift)) sub_op)


def decode_sub_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) extend_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift)) sub_op)


def decode_subs_addsub_ext_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm3 : (BitVec 3)) (option_name : (BitVec 3)) (Rm : (BitVec 5)) (S : (BitVec 1)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let setflags : Bool := (S == 1#1)
  let extend_type ← (( do (DecodeRegExtend option_name) ) : SailM ExtendType )
  let shift : Int := (BitVec.toNat imm3)
  if ((shift >b 4) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) extend_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) setflags (Sail.Int.toNatChecked (shift)) sub_op)


def decode_and_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3958) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3959) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type)


def decode_ands_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3960) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3961) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type)


def decode_bic_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3962) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3963) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type)


def decode_bics_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3964) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3965) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type)


def decode_eon_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3966) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3967) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type)


def decode_eor_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3968) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3969) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type)


def decode_orn_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3970) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3971) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type)


def decode_orr_log_shift_aarch64_instrs_integer_logical_shiftedreg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (shift : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3972) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3973) ()) ) : SailM LogicalOp )
  let (op, setflags) : (LogicalOp × Bool) :=
    match opc with
    | 0b00 =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := false
      (op, setflags))
    | 0b01 =>
      (let op : LogicalOp := LogicalOp_ORR
      let setflags : Bool := false
      (op, setflags))
    | 0b10 =>
      (let op : LogicalOp := LogicalOp_EOR
      let setflags : Bool := false
      (op, setflags))
    | _ =>
      (let op : LogicalOp := LogicalOp_AND
      let setflags : Bool := true
      (op, setflags))
  let op := op
  let setflags := setflags
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm6 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
  let shift_amount : Int := (BitVec.toNat imm6)
  let invert : Bool := (N == 1#1)
  (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type)


def decode_asrv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (execute_aarch64_instrs_integer_shift_variable (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    shift_type)


def decode_lslv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (execute_aarch64_instrs_integer_shift_variable (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    shift_type)


def decode_lsrv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (execute_aarch64_instrs_integer_shift_variable (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    shift_type)


def decode_rorv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (execute_aarch64_instrs_integer_shift_variable (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    shift_type)


def decode_cls_int_aarch64_instrs_integer_arithmetic_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let opcode : CountOp :=
    if ((op == 0#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (execute_aarch64_instrs_integer_arithmetic_cnt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)) opcode)


def decode_clz_int_aarch64_instrs_integer_arithmetic_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let opcode : CountOp :=
    if ((op == 0#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (execute_aarch64_instrs_integer_arithmetic_cnt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)) opcode)


def C40InitRawRegression (_ : Unit) : SailM Unit := do
  writeReg NUM_BREAKPOINTS (Neg.neg 1)
  writeReg NUM_WATCHPOINTS (Neg.neg 1)
  writeReg __num_ctx_breakpoints (Neg.neg 1)
  (InitFeatureImpl ())
  let w__0 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  ArmFull.assert (w__0 ≥b 2) "armcert/armcert-c47-impdef.sail:799.31-799.32"
  let w__1 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  ArmFull.assert (w__1 ≥b 2) "armcert/armcert-c47-impdef.sail:800.31-800.32"
  let w__5 ← (( do
    if ((← do
         let w__2 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
         (pure (((w__2 ≥b 1) : Bool)))) : Bool)
    then
      (do
        let w__3 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
        let w__4 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
        (pure (((w__3 ≤b w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__5 "armcert/armcert-c47-impdef.sail:801.80-801.81"


def ELUsingAArch32 (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (IsSecureBelowEL3 ()) ) : SailM Bool )
  (ELStateUsingAArch32 el w__0)


def FPCR_read (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  let r ← (( do (__get_FPCR w__0) ) : SailM (BitVec 64) )
  (pure ((Mk_FPCRType r)))


def FPSCR_read (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  let w__1 ← (( do (__get_FPSCR w__0) ) : SailM (BitVec 32) )
  let r : (BitVec 64) := ((Zeros (n := 32)) +++ w__1)
  (pure ((Mk_FPCRType r)))


def __IMPDEF_integer (x : String) : SailM Int := do
  (ImpDefInt x)


def HaveSecureState (_ : Unit) : SailM Bool := do
  if ((! (HaveEL EL3)) : Bool)
  then
    (do
      (SecureOnlyImplementation ()))
  else
    (do
      let w__3 ← (( do
        if ((← do
             (HaveRME ())) : Bool)
        then
          (do
            let w__2 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      let w__4 : Bool :=
        if (w__3 : Bool)
        then false
        else true
      (pure (w__4)))


def ExternalSecureInvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  let w__1 ← (( do
    if (((! (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (SecureOnlyImplementation ()) ) : SailM Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (false))
  else
    (do
      if ((← do
           (ExternalInvasiveDebugEnabled ())) : Bool)
      then
        (do
          let w__3 ← (( do readReg SPIDEN ) : SailM Signal )
          (pure (((BEq.beq w__3 Signal_High) : Bool))))
      else (pure false))


def BRBEFreeze (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__0 7 7 1#1)
  let w__1 ← (( do (BRBETimeStamp ()) ) : SailM TimeStamp )
  let w__2 ← (( do (GetTimestamp w__1) ) : SailM (BitVec 64) )
  writeReg BRBTS_EL1 (Mk_BRBTS_EL1_Type w__2)


def ELUsingAArch32K (el : (BitVec 2)) : SailM (Bool × Bool) := do
  let w__0 ← (( do (IsSecureBelowEL3 ()) ) : SailM Bool )
  (ELStateUsingAArch32K el w__0)


def AArch32_SelfHostedSecurePrivilegedInvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  let w__1 ← (( do
    if (((! (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        (NonSecureOnlyImplementation ()))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (false))
  else
    (do
      if ((← do
           let w__2 ← (( do readReg DBGEN ) : SailM Signal )
           (pure (((BEq.beq w__2 Signal_High) : Bool)))) : Bool)
      then
        (do
          let w__3 ← (( do readReg SPIDEN ) : SailM Signal )
          (pure (((BEq.beq w__3 Signal_High) : Bool))))
      else (pure false))


end ArmFull.Functions
