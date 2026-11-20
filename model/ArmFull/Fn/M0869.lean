module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0164
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0603 set_option backward.proofsInPublic true @[expose] public section

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

def decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel (Rd : (BitVec 5)) (immhi : (BitVec 19)) (immlo : (BitVec 2)) (op : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let page : Bool := (op == 1#1)
  let imm ← (( do (undefined_bitvector_at (← occLabel 3941) 64) ) : SailM (BitVec 64) )
  let imm : (BitVec 64) :=
    if (page : Bool)
    then (sign_extend ((immhi +++ immlo) +++ (Zeros (n := 12))) 64)
    else (sign_extend (immhi +++ immlo) 64)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_address_pc_rel (Sail.Int.toNatChecked (d)) imm page)


def decode_and_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3944) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3945) ()) ) : SailM LogicalOp )
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
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3946)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let (__tup_0, _) ← (( do
        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
          N imms immr true (Sail.Int.toNatChecked (datasize)))) ) : SailM
        ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
        )
      let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := __tup_0
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_immediate (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
        op setflags))


def decode_ands_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3947) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3948) ()) ) : SailM LogicalOp )
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
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3949)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let (__tup_0, _) ← (( do
        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
          N imms immr true (Sail.Int.toNatChecked (datasize)))) ) : SailM
        ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
        )
      let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := __tup_0
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_immediate (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
        op setflags))


def decode_eor_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3950) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3951) ()) ) : SailM LogicalOp )
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
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3952)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let (__tup_0, _) ← (( do
        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
          N imms immr true (Sail.Int.toNatChecked (datasize)))) ) : SailM
        ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
        )
      let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := __tup_0
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_immediate (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
        op setflags))


def decode_orr_log_imm_aarch64_instrs_integer_logical_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let setflags ← (( do (undefined_bool_at (← occLabel 3953) ()) ) : SailM Bool )
  let op ← (( do (undefined_LogicalOp (← occLabel 3954) ()) ) : SailM LogicalOp )
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
  let imm ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3955)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  if (((sf == 0#1) && (N != 0#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let (__tup_0, _) ← (( do
        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
          N imms immr true (Sail.Int.toNatChecked (datasize)))) ) : SailM
        ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
        )
      let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := __tup_0
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_immediate (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
        op setflags))


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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
      let shift_amount : Int := (BitVec.toNat imm6)
      let invert : Bool := (N == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type))


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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
      let shift_amount : Int := (BitVec.toNat imm6)
      let invert : Bool := (N == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type))


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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
      let shift_amount : Int := (BitVec.toNat imm6)
      let invert : Bool := (N == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type))


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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
      let shift_amount : Int := (BitVec.toNat imm6)
      let invert : Bool := (N == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type))


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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
      let shift_amount : Int := (BitVec.toNat imm6)
      let invert : Bool := (N == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type))


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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
      let shift_amount : Int := (BitVec.toNat imm6)
      let invert : Bool := (N == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type))


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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
      let shift_amount : Int := (BitVec.toNat imm6)
      let invert : Bool := (N == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type))


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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let shift_type ← (( do (DecodeShift shift) ) : SailM ShiftType )
      let shift_amount : Int := (BitVec.toNat imm6)
      let invert : Bool := (N == 1#1)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_logical_shiftedreg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) invert (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) op setflags (Sail.Int.toNatChecked (shift_amount)) shift_type))


def decode_asrv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (__ArmCertEndOfDecode ())
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
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_shift_variable (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    shift_type)


end ArmFull.Functions
