import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0020
import ArmFull.Fn.M0024
import ArmFull.Fn.M0087
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0152
import ArmFull.Fn.M0158
import ArmFull.Fn.M0164
import ArmFull.Fn.M0165

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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let (__tup_0, _) ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
      N imms immr true (Sail.Int.toNatChecked (datasize)))) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
    )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := __tup_0
  (execute_aarch64_instrs_integer_logical_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n)) op
    setflags)


/-- Type quantifiers: d : Nat, datasize : Nat, k_invert : Bool, m : Nat, n : Nat, k_setflags : Bool, shift_amount
  : Nat, 0 ≤ shift_amount ∧
  shift_amount ≤ 63 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_logical_shiftedreg (d : Nat) (datasize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : LogicalOp) (setflags : Bool) (shift_amount : Nat) (shift_type : ShiftType) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (ShiftReg m shift_type shift_amount datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3957)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand2 : (BitVec datasize) :=
    if (invert : Bool)
    then (Complement.complement operand2)
    else operand2
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
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_shift_variable (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (shift_type : ShiftType) : SailM Unit := do
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (ShiftReg n shift_type (Nat.mod (BitVec.toNat operand2) datasize)
      datasize)) ) : SailM (BitVec datasize) )
  (X_set d datasize (Sail.BitVec.castWidth result))


def decode_bfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool_at (← occLabel 3977) ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool_at (← occLabel 3978) ()) ) : SailM Bool )
  let wmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3979)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let tmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3980)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let (extend, inzero) ← (( do
    match opc with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure ((extend, inzero))))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure ((extend, inzero))))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure ((extend, inzero))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sf == 0#1) && (((N != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immr 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               imms 5)])) != 0#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let r : Int := (BitVec.toNat immr)
  let s : Int := (BitVec.toNat imms)
  let w__0 ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
      N imms immr false (Sail.Int.toNatChecked (datasize)))) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
    )
  let (tup__0, tup__1) :=
    (w__0 : ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int)))))
  let wmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__0
  let tmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__1
  (execute_aarch64_instrs_integer_bitfield (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) extend inzero (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (r)) (Sail.Int.toNatChecked (s)) (Sail.BitVec.castWidth tmask)
    (Sail.BitVec.castWidth wmask))


def decode_sbfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool_at (← occLabel 3981) ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool_at (← occLabel 3982) ()) ) : SailM Bool )
  let wmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3983)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let tmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3984)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let (extend, inzero) ← (( do
    match opc with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure ((extend, inzero))))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure ((extend, inzero))))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure ((extend, inzero))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sf == 0#1) && (((N != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immr 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               imms 5)])) != 0#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let r : Int := (BitVec.toNat immr)
  let s : Int := (BitVec.toNat imms)
  let w__0 ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
      N imms immr false (Sail.Int.toNatChecked (datasize)))) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
    )
  let (tup__0, tup__1) :=
    (w__0 : ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int)))))
  let wmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__0
  let tmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__1
  (execute_aarch64_instrs_integer_bitfield (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) extend inzero (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (r)) (Sail.Int.toNatChecked (s)) (Sail.BitVec.castWidth tmask)
    (Sail.BitVec.castWidth wmask))


def decode_ubfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool_at (← occLabel 3985) ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool_at (← occLabel 3986) ()) ) : SailM Bool )
  let wmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3987)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let tmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3988)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let (extend, inzero) ← (( do
    match opc with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure ((extend, inzero))))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure ((extend, inzero))))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure ((extend, inzero))))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sf == 0#1) && (((N != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immr 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               imms 5)])) != 0#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let r : Int := (BitVec.toNat immr)
  let s : Int := (BitVec.toNat imms)
  let w__0 ← (( do
    ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
      N imms immr false (Sail.Int.toNatChecked (datasize)))) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
    )
  let (tup__0, tup__1) :=
    (w__0 : ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int)))))
  let wmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__0
  let tmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__1
  (execute_aarch64_instrs_integer_bitfield (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) extend inzero (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (r)) (Sail.Int.toNatChecked (s)) (Sail.BitVec.castWidth tmask)
    (Sail.BitVec.castWidth wmask))


def decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (execute_aarch64_instrs_integer_conditional_compare_register condition
    (Sail.Int.toNatChecked (datasize)) flags (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (execute_aarch64_instrs_integer_conditional_compare_register condition
    (Sail.Int.toNatChecked (datasize)) flags (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend imm5 (Sail.Int.toNatChecked (datasize))))
  (execute_aarch64_instrs_integer_conditional_compare_immediate condition
    (Sail.Int.toNatChecked (datasize)) flags (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend imm5 (Sail.Int.toNatChecked (datasize))))
  (execute_aarch64_instrs_integer_conditional_compare_immediate condition
    (Sail.Int.toNatChecked (datasize)) flags (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    sub_op)


/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_cnt (d : Nat) (datasize : Nat) (n : Nat) (opcode : CountOp) : SailM Unit := do
  let result ← (( do (undefined_int_at (← occLabel 4031) ()) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int :=
    if ((BEq.beq opcode CountOp_CLZ) : Bool)
    then (CountLeadingZeroBits operand1)
    else (CountLeadingSignBits operand1)
  let result : Int := result
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


def decode_cnt_aarch64_instrs_integer_arithmetic_unary_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_unary_cnt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


def decode_crc32_aarch64_instrs_integer_crc (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCRCExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sf == 1#1) && (sz != 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sf == 0#1) && (sz == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let size : Int := (Int.shiftl 8 (BitVec.toNat sz))
  let crc32c : Bool := (C == 1#1)
  (execute_aarch64_instrs_integer_crc crc32c (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (size)))


def decode_crc32c_aarch64_instrs_integer_crc (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCRCExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  if (((sf == 1#1) && (sz != 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sf == 0#1) && (sz == 0b11#2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let size : Int := (Int.shiftl 8 (BitVec.toNat sz))
  let crc32c : Bool := (C == 1#1)
  (execute_aarch64_instrs_integer_crc crc32c (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (size)))


def decode_csel_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let condition : (BitVec 4) := cond
  let else_inv : Bool := (op == 1#1)
  let else_inc : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_integer_conditional_select condition (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) else_inc else_inv (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_csinc_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let condition : (BitVec 4) := cond
  let else_inv : Bool := (op == 1#1)
  let else_inc : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_integer_conditional_select condition (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) else_inc else_inv (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_csinv_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let condition : (BitVec 4) := cond
  let else_inv : Bool := (op == 1#1)
  let else_inc : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_integer_conditional_select condition (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) else_inc else_inv (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_csneg_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let condition : (BitVec 4) := cond
  let else_inv : Bool := (op == 1#1)
  let else_inc : Bool := (o2 == 1#1)
  (execute_aarch64_instrs_integer_conditional_select condition (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) else_inc else_inv (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_ctz_aarch64_instrs_integer_arithmetic_unary_ctz (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  (execute_aarch64_instrs_integer_arithmetic_unary_ctz (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


def decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  if ((N != sf) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imms 5)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let lsb : Int := (BitVec.toNat imms)
  (execute_aarch64_instrs_integer_ins_ext_extract_immediate (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (lsb)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


def decode_gmi_aarch64_instrs_integer_tags_mcinserttagmask (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Xd)
  let n : Int := (BitVec.toNat Xn)
  let m : Int := (BitVec.toNat Xm)
  (execute_aarch64_instrs_integer_tags_mcinserttagmask (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))


def decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let datasize : Int := destsize
  let sub_op : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (destsize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let datasize : Int := destsize
  let sub_op : Bool := (o0 == 1#1)
  (execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (destsize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let imm : (BitVec 16) := imm16
  let opcode ← (( do (undefined_MoveWideOp (← occLabel 4659) ()) ) : SailM MoveWideOp )
  let opcode ← (( do
    match opc with
    | 0b00 => (pure (MoveWideOp_N))
    | 0b10 => (pure (MoveWideOp_Z))
    | 0b11 => (pure (MoveWideOp_K))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MoveWideOp )
  let opcode := opcode
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access hw 1)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pos : Int := (BitVec.toNat (hw +++ 0b0000#4))
  (execute_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) imm opcode (Sail.Int.toNatChecked (pos)))


def decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let imm : (BitVec 16) := imm16
  let opcode ← (( do (undefined_MoveWideOp (← occLabel 4660) ()) ) : SailM MoveWideOp )
  let opcode ← (( do
    match opc with
    | 0b00 => (pure (MoveWideOp_N))
    | 0b10 => (pure (MoveWideOp_Z))
    | 0b11 => (pure (MoveWideOp_K))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MoveWideOp )
  let opcode := opcode
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access hw 1)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pos : Int := (BitVec.toNat (hw +++ 0b0000#4))
  (execute_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) imm opcode (Sail.Int.toNatChecked (pos)))


def decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let imm : (BitVec 16) := imm16
  let opcode ← (( do (undefined_MoveWideOp (← occLabel 4661) ()) ) : SailM MoveWideOp )
  let opcode ← (( do
    match opc with
    | 0b00 => (pure (MoveWideOp_N))
    | 0b10 => (pure (MoveWideOp_Z))
    | 0b11 => (pure (MoveWideOp_K))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM MoveWideOp )
  let opcode := opcode
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access hw 1)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pos : Int := (BitVec.toNat (hw +++ 0b0000#4))
  (execute_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) imm opcode (Sail.Int.toNatChecked (pos)))


def decode_rbit_int_aarch64_instrs_integer_arithmetic_rbit (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  (execute_aarch64_instrs_integer_arithmetic_rbit (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


def decode_rev_aarch64_instrs_integer_arithmetic_rev (Rd : (BitVec 5)) (Rn : (BitVec 5)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let container_size : Int := 16
  let container_size ← (( do
    match opc with
    | 0b00 =>
      (do
        (Unreachable ())
        (pure (container_size)))
    | 0b01 => (pure (16))
    | 0b10 => (pure (32))
    | _ =>
      (do
        if ((sf == 0#1) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (64))) ) : SailM Int )
  let container_size : Int := container_size
  (execute_aarch64_instrs_integer_arithmetic_rev (Sail.Int.toNatChecked (container_size))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)))


end ArmFull.Functions
