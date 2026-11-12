import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0008
import ArmFull.Fn.M0043
import ArmFull.Fn.M0051
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0114
import ArmFull.Fn.M0115
import ArmFull.Fn.M0118
import ArmFull.Fn.M0143
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0152

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

/-- Type quantifiers: datasize : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] -/
def execute_aarch64_instrs_integer_conditional_compare_immediate (condition : (BitVec 4)) (datasize : Nat) (flags__arg : (BitVec 4)) (imm : (BitVec datasize)) (n : Nat) (sub_op : Bool) : SailM Unit := do
  let flags : (BitVec 4) := flags__arg
  let taken : Bool := false
  let w__0 ← (( do (ConditionHolds condition) ) : SailM Bool )
  let (flags, taken) ← (( do
    if (w__0 : Bool)
    then
      (do
        let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
          (BitVec datasize) )
        let operand2 : (BitVec datasize) := imm
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


def decode_cfinv_aarch64_instrs_integer_flags_cfinv (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFlagManipulateExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_integer_flags_cfinv ())


/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_unary_cnt (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (BitCount operand1)
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: k_crc32c : Bool, d : Nat, m : Nat, n : Nat, size : Nat, List.elem size
  [8, 16, 32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_crc (crc32c : Bool) (d : Nat) (m : Nat) (n : Nat) (size : Nat) : SailM Unit := do
  let acc ← (( do (X_read n 32) ) : SailM (BitVec 32) )
  let val_name ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m size)) ) : SailM (BitVec size) )
  let poly : (BitVec 32) :=
    (integer_subrange
      (if (crc32c : Bool)
      then (BitVec.toNat 0x1EDC6F41#32)
      else (BitVec.toNat 0x04C11DB7#32)) 31 0)
  let w__0 ← (( do (BitReverse acc) ) : SailM (BitVec 32) )
  let tempacc : (BitVec (32 + size)) := (Sail.BitVec.castWidth (w__0 +++ (Zeros (n := size))))
  let w__1 ← (( do (BitReverse val_name) ) : SailM (BitVec size) )
  let tempval : (BitVec (size + 32)) := (Sail.BitVec.castWidth (w__1 +++ (Zeros (n := 32))))
  let w__2 ← (( do (Poly32Mod2 (tempacc ^^^ (Sail.BitVec.castWidth tempval)) poly) ) : SailM
    (BitVec 32) )
  let w__3 ← (( do (BitReverse w__2) ) : SailM (BitVec 32) )
  (X_set d 32 w__3)


/-- Type quantifiers: d : Nat, datasize : Nat, k_else_inc : Bool, k_else_inv : Bool, m : Nat, n :
  Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_conditional_select (condition : (BitVec 4)) (d : Nat) (datasize : Nat) (else_inc : Bool) (else_inv : Bool) (m : Nat) (n : Nat) : SailM Unit := do
  let taken : Bool := false
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4095)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let w__0 ← (( do (ConditionHolds condition) ) : SailM Bool )
  let (result, taken) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
          (BitVec datasize) )
        let result := (w__1 : (BitVec datasize))
        let taken : Bool := true
        (pure ((result, taken))))
    else
      (do
        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
          (BitVec datasize) )
        let result := (w__2 : (BitVec datasize))
        let result : (BitVec datasize) :=
          if (else_inv : Bool)
          then (Complement.complement result)
          else result
        let result : (BitVec datasize) :=
          if (else_inc : Bool)
          then (BitVec.addInt result 1)
          else result
        (pure ((result, taken)))) ) : SailM ((BitVec datasize) × Bool) )
  (X_set d datasize (Sail.BitVec.castWidth result))
  let w__3 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let conditional : Bool := true
      (SPESampleAddOpOther conditional taken))
  else (pure (()))


/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_unary_ctz (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let w__0 ← (( do (BitReverse operand1) ) : SailM (BitVec datasize) )
  let result : Int := (CountLeadingZeroBits w__0)
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, lsb : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ lsb ∧ lsb ≤ 63 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_ins_ext_extract_immediate (d : Nat) (datasize : Nat) (lsb : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let concat : (BitVec (2 * datasize)) := (Sail.BitVec.castWidth (operand1 +++ operand2))
  ArmFull.assert (((lsb +i datasize) -i 1) <b (2 *i datasize)) "sail-arm/instrs64.sail:10732.59-10732.60"
  let result : (BitVec datasize) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb concat
      (Sail.Int.toNatChecked (((lsb +i datasize) -i 1))) lsb))
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_tags_mcinserttagmask (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let mask ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress address)
  let mask : (BitVec 64) := (BitVec.update mask (BitVec.toNat tag) (Bit 1#1))
  (X_set d 64 mask)


/-- Type quantifiers: a : Nat, d : Nat, datasize : Nat, destsize : Nat, m : Nat, n : Nat, k_sub_op :
  Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem destsize [32, 64] ∧
  List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (a : Nat) (d : Nat) (datasize : Nat) (destsize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read a destsize)) ) : SailM
    (BitVec destsize) )
  let result ← (( do (undefined_int_at (← occLabel 4646) ()) ) : SailM Int )
  let result : Int :=
    if (sub_op : Bool)
    then ((BitVec.toNat operand3) -i ((BitVec.toNat operand1) *i (BitVec.toNat operand2)))
    else ((BitVec.toNat operand3) +i ((BitVec.toNat operand1) *i (BitVec.toNat operand2)))
  let result : Int := result
  (X_set d destsize (Sail.BitVec.castWidth (integer_subrange result (destsize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, pos : Nat, 0 ≤ pos ∧
  pos ≤ 63 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_ins_ext_insert_movewide (d : Nat) (datasize : Nat) (imm : (BitVec 16)) (opcode : MoveWideOp) (pos : Nat) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4658)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    if ((BEq.beq opcode MoveWideOp_K) : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (X_read d datasize)))
    else
      (let result : (BitVec datasize) := (Sail.BitVec.castWidth (Zeros (n := datasize)))
      (pure (result))) ) : SailM (BitVec datasize) )
  ArmFull.assert ((pos +i 15) <b datasize) "sail-arm/instrs64.sail:38730.44-38730.45"
  let result : (BitVec datasize) :=
    (Sail.BitVec.updateSubrange result (Sail.Int.toNatChecked ((pos +i 15))) pos
      (Sail.BitVec.castWidth imm))
  let result : (BitVec datasize) :=
    if ((BEq.beq opcode MoveWideOp_N) : Bool)
    then (Complement.complement result)
    else result
  let result := result
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_rbit (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4686)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let result ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := (Sail.Int.toNatChecked ((datasize -i 1)))
    (do
      let mut loop_vars := result
      for i in [loop_i_lower:loop_i_upper:1]i do
        let result := loop_vars
        loop_vars :=
          (BitVec.update result (Sail.Int.toNatChecked (((datasize -i 1) -i i)))
            (Bit
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand (Sail.Int.toNatChecked (i)))]))))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: container_size : Nat, d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ List.elem container_size [16, 32, 64] -/
def execute_aarch64_instrs_integer_arithmetic_rev (container_size : Nat) (d : Nat) (datasize : Nat) (n : Nat) : SailM Unit := do
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4735)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let containers : Nat := (Sail.Int.toNatChecked ((Int.ediv datasize container_size)))
  let elements_per_container : Nat := (Sail.Int.toNatChecked ((Int.ediv container_size 8)))
  let index : Int := 0
  let rev_index ← (( do (undefined_int_at (← occLabel 4736) ()) ) : SailM Int )
  let (index, result, rev_index) ← (( do
    let loop_c_lower : Nat := 0
    let loop_c_upper : Int := (containers -i 1)
    (do
      let mut loop_vars := (index, result, rev_index)
      for c in [loop_c_lower:loop_c_upper:1]i do
        let (index, result, rev_index) := loop_vars
        loop_vars ← do
          let rev_index : Int := (index +i ((elements_per_container -i 1) *i 8))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements_per_container -i 1)
          (do
            let mut loop_vars_1 := (index, result, rev_index)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (index, result, rev_index) := loop_vars_1
              loop_vars_1 ← do
                let rev_index : Int := rev_index
                let index : Int := index
                ArmFull.assert ((0 ≤b rev_index) && ((rev_index +i 7) <b datasize)) "sail-arm/instrs64.sail:41065.83-41065.84"
                ArmFull.assert ((0 ≤b index) && ((index +i 7) <b datasize)) "sail-arm/instrs64.sail:41066.75-41066.76"
                let result : (BitVec datasize) :=
                  (Sail.BitVec.updateSubrange result (Sail.Int.toNatChecked ((rev_index +i 7)))
                    (Sail.Int.toNatChecked (rev_index))
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb operand
                      (Sail.Int.toNatChecked ((index +i 7))) (Sail.Int.toNatChecked (index)))))
                let index : Int := (index +i 8)
                let rev_index : Int := (rev_index -i 8)
                (pure ((index, result, rev_index)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec datasize) × Int) )
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: lsb : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ lsb ∧ lsb ≤ 63 -/
def execute_aarch64_instrs_integer_flags_rmif (lsb : Nat) (mask : (BitVec 4)) (n : Nat) : SailM Unit := do
  let tmpreg ← (( do (X_read n 64) ) : SailM (BitVec 64) )
  let tmp : (BitVec 4) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb (tmpreg +++ tmpreg)
      (Sail.Int.toNatChecked ((lsb +i 3))) lsb))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask 3)])) == 1#1) : Bool)
  then
    (do
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tmp 3)])) })
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask 2)])) == 1#1) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with Z := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tmp 2)])) })
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask 1)])) == 1#1) : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with C := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tmp 1)])) })
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask 0)])) == 1#1) : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with V := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tmp 0)])) })
  else (pure (()))


/-- Type quantifiers: m : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 -/
def execute_aarch64_instrs_memory_single_general_range (m : Nat) (n : Nat) (operation : (BitVec 6)) : SailM Unit := do
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let metadata ← (( do (X_read m 64) ) : SailM (BitVec 64) )
  let stride : Int := (BitVec.toInt (Sail.BitVec.extractLsb metadata 59 38))
  let count : Int := ((BitVec.toNat (Sail.BitVec.extractLsb metadata 37 22)) +i 1)
  let length : Int := (BitVec.toInt (Sail.BitVec.extractLsb metadata 21 0))
  let reuse ← (( do (undefined_int_at (← occLabel 4739) ()) ) : SailM Int )
  let reuse : Int :=
    if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb metadata 63 60)) == 0b0000#4) : Bool)
    then (Neg.neg 1)
    else
      (Int.shiftl 32768
        (Sail.Int.toNatChecked ((15 -i (BitVec.toNat (Sail.BitVec.extractLsb metadata 63 60))))))
  let reuse : Int := reuse
  (pure ((Hint_RangePrefetch address length stride count reuse operation)))


def decode_sb_aarch64_instrs_system_barriers_sb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveSBExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_system_barriers_sb ())


/-- Type quantifiers: d : Nat, datasize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_div (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do (undefined_int_at (← occLabel 4762) ()) ) : SailM Int )
  let result ← (( do
    if ((IsZero operand2) : Bool)
    then (pure (0))
    else
      (do
        let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
        let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
        let result : Int := ((RoundTowardsZero (div_real (to_real w__0) (to_real w__1))) : Int)
        (pure (result))) ) : SailM Int )
  let result : Int := result
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: msb : Nat, n : Nat, 0 ≤ n ∧ n ≤ 31 ∧ List.elem msb [7, 15] -/
def execute_aarch64_instrs_integer_flags_setf (msb : Nat) (n : Nat) : SailM Unit := do
  let tmpreg ← (( do (X_read n 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tmpreg msb)])) }
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with Z := if (((Sail.BitVec.castWidth (m := (msb + 1)) (Sail.BitVec.extractLsb
           tmpreg msb 0)) == (Sail.BitVec.castWidth (Zeros
           (n := (Sail.Int.toNatChecked ((msb +i 1))))))) : Bool)
    then 1#1
    else 0#1 }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with V := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access tmpreg
          (Sail.Int.toNatChecked ((msb +i 1))))])) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          tmpreg msb)]))) }


/-- Type quantifiers: a : Nat, d : Nat, datasize : Nat, destsize : Nat, k_is_unsigned : Bool, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ destsize = 64 ∧ datasize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_mul_widening_32_64 (a : Nat) (d : Nat) (datasize : Nat) (destsize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read a destsize)) ) : SailM
    (BitVec destsize) )
  let result ← (( do (undefined_int_at (← occLabel 4820) ()) ) : SailM Int )
  let result ← (( do
    if (sub_op : Bool)
    then
      (do
        let w__0 ← (( do (asl_Int operand3 is_unsigned) ) : SailM Int )
        let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
        let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
        let result : Int := ((w__0 -i (w__1 *i w__2)) : Int)
        (pure (result)))
    else
      (do
        let w__3 ← (( do (asl_Int operand3 is_unsigned) ) : SailM Int )
        let w__4 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
        let w__5 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
        let result : Int := ((w__3 +i (w__4 *i w__5)) : Int)
        (pure (result))) ) : SailM Int )
  let result : Int := result
  (X_set d 64 (integer_subrange result 63 0))


/-- Type quantifiers: d : Nat, datasize : Nat, imm : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_smax_imm (d : Nat) (datasize : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (Max.max (BitVec.toInt operand1) imm)
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_smax_reg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (Max.max (BitVec.toInt operand1) (BitVec.toInt operand2))
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, imm : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_smin_imm (d : Nat) (datasize : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (Min.min (BitVec.toInt operand1) imm)
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_smin_reg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (Min.min (BitVec.toInt operand1) (BitVec.toInt operand2))
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ datasize = 64 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_mul_widening_64_128hi (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
  let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
  let result : Int := (w__0 *i w__1)
  (X_set d 64 (integer_subrange result 127 64))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let operand2 ← (( do
    if ((m == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read m 64)) ) : SailM (BitVec 64) )
  let operand1 : (BitVec 64) := (sign_extend (Sail.BitVec.extractLsb operand1 55 0) 64)
  let operand2 : (BitVec 64) := (sign_extend (Sail.BitVec.extractLsb operand2 55 0) 64)
  let result ← (( do (undefined_bitvector_at (← occLabel 5008) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 5009) 4) ) : SailM (BitVec 4) )
  let operand2 : (BitVec 64) := (Complement.complement operand2)
  let (tup__0, tup__1) := ((AddWithCarry operand1 operand2 1#1) : ((BitVec 64) × (BitVec 4)))
  let result : (BitVec 64) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))
  (X_set d 64 result)


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let operand2 ← (( do
    if ((m == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read m 64)) ) : SailM (BitVec 64) )
  let operand1 : (BitVec 64) := (sign_extend (Sail.BitVec.extractLsb operand1 55 0) 64)
  let operand2 : (BitVec 64) := (sign_extend (Sail.BitVec.extractLsb operand2 55 0) 64)
  let result ← (( do (undefined_bitvector_at (← occLabel 5010) 64) ) : SailM (BitVec 64) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 5011) 4) ) : SailM (BitVec 4) )
  let operand2 : (BitVec 64) := (Complement.complement operand2)
  let (tup__0, tup__1) := ((AddWithCarry operand1 operand2 1#1) : ((BitVec 64) × (BitVec 4)))
  let result : (BitVec 64) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))
  (X_set d 64 result)


/-- Type quantifiers: d : Nat, datasize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ imm ∧ imm ≤ 255 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_umax_imm (d : Nat) (datasize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (Max.max (BitVec.toNat operand1) imm)
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_umax_reg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (Max.max (BitVec.toNat operand1) (BitVec.toNat operand2))
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_umin_reg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (Min.min (BitVec.toNat operand1) (BitVec.toNat operand2))
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


/-- Type quantifiers: d : Nat, datasize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ imm ∧ imm ≤ 255 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_max_min_umin_imm (d : Nat) (datasize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int := (Min.min (BitVec.toNat operand1) imm)
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


def decode_xaflag_aarch64_instrs_integer_flags_xaflag (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFlagFormatExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch64_instrs_integer_flags_xaflag ())


/-- Type quantifiers: shift : Int, j : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def place_subrange_signed {m : _} (xs : (BitVec k_n)) (i : Int) (j : Int) (shift : Int) : (BitVec m) :=
  (Sail.BitVec.castWidth (place_slice_signed (m := m) xs j ((i -i j) +i 1) shift))


def InitFeatureImpl (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__1 ← (( do readReg FEAT_AA32EL0_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__0 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA32EL0)))
    w__1)
  let w__2 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__3 ← (( do readReg FEAT_AA32EL1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__2 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA32EL1)))
    w__3)
  let w__4 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__5 ← (( do readReg FEAT_AA32EL2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__4 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA32EL2)))
    w__5)
  let w__6 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__7 ← (( do readReg FEAT_AA32EL3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__6 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA32EL3)))
    w__7)
  let w__8 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__9 ← (( do readReg FEAT_AA64EL0_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__8 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL0)))
    w__9)
  let w__10 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__11 ← (( do readReg FEAT_AA64EL1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__10 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL1)))
    w__11)
  let w__12 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__13 ← (( do readReg FEAT_AA64EL2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__12 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL2)))
    w__13)
  let w__14 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__15 ← (( do readReg FEAT_AA64EL3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__14 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA64EL3)))
    w__15)
  let w__16 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__17 ← (( do readReg FEAT_EL0_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__16 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EL0))) w__17)
  let w__18 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__19 ← (( do readReg FEAT_EL1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__18 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EL1))) w__19)
  let w__20 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__21 ← (( do readReg FEAT_EL2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__20 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EL2))) w__21)
  let w__22 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__23 ← (( do readReg FEAT_EL3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__22 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EL3))) w__23)
  let w__24 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__25 ← (( do readReg FEAT_AES_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__24 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AES))) w__25)
  let w__26 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__27 ← (( do readReg FEAT_AdvSIMD_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__26 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AdvSIMD)))
    w__27)
  let w__28 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__29 ← (( do readReg FEAT_CSV2_1p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__28 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CSV2_1p1)))
    w__29)
  let w__30 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__31 ← (( do readReg FEAT_CSV2_1p2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__30 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CSV2_1p2)))
    w__31)
  let w__32 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__33 ← (( do readReg FEAT_CSV2_2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__32 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CSV2_2)))
    w__33)
  let w__34 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__35 ← (( do readReg FEAT_CSV2_3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__34 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CSV2_3)))
    w__35)
  let w__36 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__37 ← (( do readReg FEAT_DoubleLock_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__36
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_DoubleLock))) w__37)
  let w__38 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__39 ← (( do readReg FEAT_ETMv4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__38 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETMv4)))
    w__39)
  let w__40 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__41 ← (( do readReg FEAT_ETMv4p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__40 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETMv4p1)))
    w__41)
  let w__42 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__43 ← (( do readReg FEAT_ETMv4p2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__42 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETMv4p2)))
    w__43)
  let w__44 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__45 ← (( do readReg FEAT_ETMv4p3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__44 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETMv4p3)))
    w__45)
  let w__46 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__47 ← (( do readReg FEAT_ETMv4p4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__46 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETMv4p4)))
    w__47)
  let w__48 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__49 ← (( do readReg FEAT_ETMv4p5_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__48 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETMv4p5)))
    w__49)
  let w__50 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__51 ← (( do readReg FEAT_ETMv4p6_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__50 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETMv4p6)))
    w__51)
  let w__52 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__53 ← (( do readReg FEAT_ETS2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__52 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETS2)))
    w__53)
  let w__54 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__55 ← (( do readReg FEAT_FP_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__54 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FP))) w__55)
  let w__56 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__57 ← (( do readReg FEAT_GICv3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__56 (Sail.Int.toNatChecked ((num_of_Feature FEAT_GICv3)))
    w__57)
  let w__58 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__59 ← (( do readReg FEAT_GICv3_LEGACY_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__58
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_GICv3_LEGACY))) w__59)
  let w__60 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__61 ← (( do readReg FEAT_GICv3_TDIR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__60
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_GICv3_TDIR))) w__61)
  let w__62 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__63 ← (( do readReg FEAT_GICv3p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__62 (Sail.Int.toNatChecked ((num_of_Feature FEAT_GICv3p1)))
    w__63)
  let w__64 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__65 ← (( do readReg FEAT_GICv4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__64 (Sail.Int.toNatChecked ((num_of_Feature FEAT_GICv4)))
    w__65)
  let w__66 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__67 ← (( do readReg FEAT_GICv4p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__66 (Sail.Int.toNatChecked ((num_of_Feature FEAT_GICv4p1)))
    w__67)
  let w__68 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__69 ← (( do readReg FEAT_IVIPT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__68 (Sail.Int.toNatChecked ((num_of_Feature FEAT_IVIPT)))
    w__69)
  let w__70 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__71 ← (( do readReg FEAT_PCSRv8_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__70 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PCSRv8)))
    w__71)
  let w__72 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__73 ← (( do readReg FEAT_PMULL_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__72 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMULL)))
    w__73)
  let w__74 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__75 ← (( do readReg FEAT_PMUv3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__74 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3)))
    w__75)
  let w__76 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__77 ← (( do readReg FEAT_PMUv3_EXT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__76 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3_EXT)))
    w__77)
  let w__78 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__79 ← (( do readReg FEAT_PMUv3_EXT32_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__78
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3_EXT32))) w__79)
  let w__80 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__81 ← (( do readReg FEAT_SHA1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__80 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SHA1)))
    w__81)
  let w__82 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__83 ← (( do readReg FEAT_SHA256_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__82 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SHA256)))
    w__83)
  let w__84 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__85 ← (( do readReg FEAT_TRC_EXT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__84 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TRC_EXT)))
    w__85)
  let w__86 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__87 ← (( do readReg FEAT_TRC_SR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__86 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TRC_SR)))
    w__87)
  let w__88 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__89 ← (( do readReg FEAT_nTLBPA_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__88 (Sail.Int.toNatChecked ((num_of_Feature FEAT_nTLBPA)))
    w__89)
  let w__90 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__91 ← (( do readReg FEAT_CRC32_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__90 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CRC32)))
    w__91)
  let w__92 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__93 ← (( do readReg FEAT_Debugv8p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__92 (Sail.Int.toNatChecked ((num_of_Feature FEAT_Debugv8p1)))
    w__93)
  let w__94 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__95 ← (( do readReg FEAT_HAFDBS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__94 (Sail.Int.toNatChecked ((num_of_Feature FEAT_HAFDBS)))
    w__95)
  let w__96 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__97 ← (( do readReg FEAT_HPDS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__96 (Sail.Int.toNatChecked ((num_of_Feature FEAT_HPDS)))
    w__97)
  let w__98 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__99 ← (( do readReg FEAT_LOR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__98 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LOR))) w__99)
  let w__100 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__101 ← (( do readReg FEAT_LSE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__100 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LSE)))
    w__101)
  let w__102 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__103 ← (( do readReg FEAT_PAN_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__102 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PAN)))
    w__103)
  let w__104 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__105 ← (( do readReg FEAT_PMUv3p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__104 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3p1)))
    w__105)
  let w__106 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__107 ← (( do readReg FEAT_RDM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__106 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RDM)))
    w__107)
  let w__108 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__109 ← (( do readReg FEAT_VHE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__108 (Sail.Int.toNatChecked ((num_of_Feature FEAT_VHE)))
    w__109)
  let w__110 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__111 ← (( do readReg FEAT_VMID16_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__110 (Sail.Int.toNatChecked ((num_of_Feature FEAT_VMID16)))
    w__111)
  let w__112 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__113 ← (( do readReg FEAT_AA32BF16_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__112 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA32BF16)))
    w__113)
  let w__114 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__115 ← (( do readReg FEAT_AA32HPD_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__114 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA32HPD)))
    w__115)
  let w__116 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__117 ← (( do readReg FEAT_AA32I8MM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__116 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AA32I8MM)))
    w__117)
  let w__118 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__119 ← (( do readReg FEAT_ASMv8p2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__118 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ASMv8p2)))
    w__119)
  let w__120 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__121 ← (( do readReg FEAT_DPB_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__120 (Sail.Int.toNatChecked ((num_of_Feature FEAT_DPB)))
    w__121)
  let w__122 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__123 ← (( do readReg FEAT_Debugv8p2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__122
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_Debugv8p2))) w__123)
  let w__124 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__125 ← (( do readReg FEAT_EDHSR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__124 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EDHSR)))
    w__125)
  let w__126 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__127 ← (( do readReg FEAT_F32MM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__126 (Sail.Int.toNatChecked ((num_of_Feature FEAT_F32MM)))
    w__127)
  let w__128 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__129 ← (( do readReg FEAT_F64MM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__128 (Sail.Int.toNatChecked ((num_of_Feature FEAT_F64MM)))
    w__129)
  let w__130 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__131 ← (( do readReg FEAT_FP16_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__130 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FP16)))
    w__131)
  let w__132 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__133 ← (( do readReg FEAT_HPDS2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__132 (Sail.Int.toNatChecked ((num_of_Feature FEAT_HPDS2)))
    w__133)
  let w__134 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__135 ← (( do readReg FEAT_I8MM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__134 (Sail.Int.toNatChecked ((num_of_Feature FEAT_I8MM)))
    w__135)
  let w__136 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__137 ← (( do readReg FEAT_IESB_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__136 (Sail.Int.toNatChecked ((num_of_Feature FEAT_IESB)))
    w__137)
  let w__138 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__139 ← (( do readReg FEAT_LPA_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__138 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LPA)))
    w__139)
  let w__140 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__141 ← (( do readReg FEAT_LSMAOC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__140 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LSMAOC)))
    w__141)
  let w__142 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__143 ← (( do readReg FEAT_LVA_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__142 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LVA)))
    w__143)
  let w__144 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__145 ← (( do readReg FEAT_MPAM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__144 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MPAM)))
    w__145)
  let w__146 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__147 ← (( do readReg FEAT_PAN2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__146 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PAN2)))
    w__147)
  let w__148 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__149 ← (( do readReg FEAT_PCSRv8p2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__148 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PCSRv8p2)))
    w__149)
  let w__150 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__151 ← (( do readReg FEAT_RAS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__150 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RAS)))
    w__151)
  let w__152 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__153 ← (( do readReg FEAT_SHA3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__152 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SHA3)))
    w__153)
  let w__154 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__155 ← (( do readReg FEAT_SHA512_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__154 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SHA512)))
    w__155)
  let w__156 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__157 ← (( do readReg FEAT_SM3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__156 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SM3)))
    w__157)
  let w__158 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__159 ← (( do readReg FEAT_SM4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__158 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SM4)))
    w__159)
  let w__160 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__161 ← (( do readReg FEAT_SPE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__160 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPE)))
    w__161)
  let w__162 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__163 ← (( do readReg FEAT_SVE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__162 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE)))
    w__163)
  let w__164 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__165 ← (( do readReg FEAT_TTCNP_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__164 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TTCNP)))
    w__165)
  let w__166 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__167 ← (( do readReg FEAT_UAO_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__166 (Sail.Int.toNatChecked ((num_of_Feature FEAT_UAO)))
    w__167)
  let w__168 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__169 ← (( do readReg FEAT_VPIPT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__168 (Sail.Int.toNatChecked ((num_of_Feature FEAT_VPIPT)))
    w__169)
  let w__170 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__171 ← (( do readReg FEAT_XNX_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__170 (Sail.Int.toNatChecked ((num_of_Feature FEAT_XNX)))
    w__171)
  let w__172 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__173 ← (( do readReg FEAT_CCIDX_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__172 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CCIDX)))
    w__173)
  let w__174 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__175 ← (( do readReg FEAT_CONSTPACFIELD_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__174
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_CONSTPACFIELD))) w__175)
  let w__176 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__177 ← (( do readReg FEAT_EPAC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__176 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EPAC)))
    w__177)
  let w__178 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__179 ← (( do readReg FEAT_FCMA_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__178 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FCMA)))
    w__179)
  let w__180 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__181 ← (( do readReg FEAT_FPAC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__180 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FPAC)))
    w__181)
  let w__182 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__183 ← (( do readReg FEAT_FPACCOMBINE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__182
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_FPACCOMBINE))) w__183)
  let w__184 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__185 ← (( do readReg FEAT_JSCVT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__184 (Sail.Int.toNatChecked ((num_of_Feature FEAT_JSCVT)))
    w__185)
  let w__186 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__187 ← (( do readReg FEAT_LRCPC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__186 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LRCPC)))
    w__187)
  let w__188 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__189 ← (( do readReg FEAT_NV_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__188 (Sail.Int.toNatChecked ((num_of_Feature FEAT_NV)))
    w__189)
  let w__190 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__191 ← (( do readReg FEAT_PACIMP_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__190 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PACIMP)))
    w__191)
  let w__192 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__193 ← (( do readReg FEAT_PACQARMA3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__192
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_PACQARMA3))) w__193)
  let w__194 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__195 ← (( do readReg FEAT_PACQARMA5_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__194
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_PACQARMA5))) w__195)
  let w__196 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__197 ← (( do readReg FEAT_PAuth_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__196 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PAuth)))
    w__197)
  let w__198 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__199 ← (( do readReg FEAT_SPEv1p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__198 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPEv1p1)))
    w__199)
  let w__200 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__201 ← (( do readReg FEAT_AMUv1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__200 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AMUv1)))
    w__201)
  let w__202 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__203 ← (( do readReg FEAT_BBM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__202 (Sail.Int.toNatChecked ((num_of_Feature FEAT_BBM)))
    w__203)
  let w__204 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__205 ← (( do readReg FEAT_CNTSC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__204 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CNTSC)))
    w__205)
  let w__206 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__207 ← (( do readReg FEAT_DIT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__206 (Sail.Int.toNatChecked ((num_of_Feature FEAT_DIT)))
    w__207)
  let w__208 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__209 ← (( do readReg FEAT_Debugv8p4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__208
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_Debugv8p4))) w__209)
  let w__210 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__211 ← (( do readReg FEAT_DotProd_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__210 (Sail.Int.toNatChecked ((num_of_Feature FEAT_DotProd)))
    w__211)
  let w__212 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__213 ← (( do readReg FEAT_DoubleFault_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__212
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_DoubleFault))) w__213)
  let w__214 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__215 ← (( do readReg FEAT_FHM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__214 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FHM)))
    w__215)
  let w__216 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__217 ← (( do readReg FEAT_FlagM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__216 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FlagM)))
    w__217)
  let w__218 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__219 ← (( do readReg FEAT_IDST_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__218 (Sail.Int.toNatChecked ((num_of_Feature FEAT_IDST)))
    w__219)
  let w__220 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__221 ← (( do readReg FEAT_LRCPC2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__220 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LRCPC2)))
    w__221)
  let w__222 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__223 ← (( do readReg FEAT_LSE2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__222 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LSE2)))
    w__223)
  let w__224 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__225 ← (( do readReg FEAT_NV2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__224 (Sail.Int.toNatChecked ((num_of_Feature FEAT_NV2)))
    w__225)
  let w__226 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__227 ← (( do readReg FEAT_PMUv3p4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__226 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3p4)))
    w__227)
  let w__228 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__229 ← (( do readReg FEAT_RASSAv1p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__228
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_RASSAv1p1))) w__229)
  let w__230 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__231 ← (( do readReg FEAT_RASv1p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__230 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RASv1p1)))
    w__231)
  let w__232 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__233 ← (( do readReg FEAT_S2FWB_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__232 (Sail.Int.toNatChecked ((num_of_Feature FEAT_S2FWB)))
    w__233)
  let w__234 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__235 ← (( do readReg FEAT_SEL2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__234 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SEL2)))
    w__235)
  let w__236 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__237 ← (( do readReg FEAT_TLBIOS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__236 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TLBIOS)))
    w__237)
  let w__238 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__239 ← (( do readReg FEAT_TLBIRANGE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__238
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_TLBIRANGE))) w__239)
  let w__240 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__241 ← (( do readReg FEAT_TRF_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__240 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TRF)))
    w__241)
  let w__242 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__243 ← (( do readReg FEAT_TTL_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__242 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TTL)))
    w__243)
  let w__244 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__245 ← (( do readReg FEAT_TTST_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__244 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TTST)))
    w__245)
  let w__246 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__247 ← (( do readReg FEAT_BTI_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__246 (Sail.Int.toNatChecked ((num_of_Feature FEAT_BTI)))
    w__247)
  let w__248 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__249 ← (( do readReg FEAT_CSV2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__248 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CSV2)))
    w__249)
  let w__250 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__251 ← (( do readReg FEAT_CSV3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__250 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CSV3)))
    w__251)
  let w__252 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__253 ← (( do readReg FEAT_DPB2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__252 (Sail.Int.toNatChecked ((num_of_Feature FEAT_DPB2)))
    w__253)
  let w__254 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__255 ← (( do readReg FEAT_E0PD_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__254 (Sail.Int.toNatChecked ((num_of_Feature FEAT_E0PD)))
    w__255)
  let w__256 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__257 ← (( do readReg FEAT_EVT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__256 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EVT)))
    w__257)
  let w__258 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__259 ← (( do readReg FEAT_ExS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__258 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ExS)))
    w__259)
  let w__260 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__261 ← (( do readReg FEAT_FRINTTS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__260 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FRINTTS)))
    w__261)
  let w__262 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__263 ← (( do readReg FEAT_FlagM2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__262 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FlagM2)))
    w__263)
  let w__264 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__265 ← (( do readReg FEAT_GTG_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__264 (Sail.Int.toNatChecked ((num_of_Feature FEAT_GTG)))
    w__265)
  let w__266 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__267 ← (( do readReg FEAT_MTE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__266 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE)))
    w__267)
  let w__268 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__269 ← (( do readReg FEAT_MTE2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__268 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE2)))
    w__269)
  let w__270 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__271 ← (( do readReg FEAT_PMUv3p5_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__270 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3p5)))
    w__271)
  let w__272 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__273 ← (( do readReg FEAT_RNG_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__272 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RNG)))
    w__273)
  let w__274 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__275 ← (( do readReg FEAT_RNG_TRAP_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__274 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RNG_TRAP)))
    w__275)
  let w__276 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__277 ← (( do readReg FEAT_SB_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__276 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SB)))
    w__277)
  let w__278 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__279 ← (( do readReg FEAT_SPECRES_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__278 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPECRES)))
    w__279)
  let w__280 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__281 ← (( do readReg FEAT_SSBS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__280 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SSBS)))
    w__281)
  let w__282 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__283 ← (( do readReg FEAT_SSBS2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__282 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SSBS2)))
    w__283)
  let w__284 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__285 ← (( do readReg FEAT_AMUv1p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__284 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AMUv1p1)))
    w__285)
  let w__286 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__287 ← (( do readReg FEAT_BF16_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__286 (Sail.Int.toNatChecked ((num_of_Feature FEAT_BF16)))
    w__287)
  let w__288 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__289 ← (( do readReg FEAT_DGH_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__288 (Sail.Int.toNatChecked ((num_of_Feature FEAT_DGH)))
    w__289)
  let w__290 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__291 ← (( do readReg FEAT_ECV_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__290 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ECV)))
    w__291)
  let w__292 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__293 ← (( do readReg FEAT_FGT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__292 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FGT)))
    w__293)
  let w__294 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__295 ← (( do readReg FEAT_HPMN0_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__294 (Sail.Int.toNatChecked ((num_of_Feature FEAT_HPMN0)))
    w__295)
  let w__296 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__297 ← (( do readReg FEAT_MPAMv0p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__296 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MPAMv0p1)))
    w__297)
  let w__298 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__299 ← (( do readReg FEAT_MPAMv1p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__298 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MPAMv1p1)))
    w__299)
  let w__300 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__301 ← (( do readReg FEAT_MTPMU_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__300 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTPMU)))
    w__301)
  let w__302 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__303 ← (( do readReg FEAT_PAuth2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__302 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PAuth2)))
    w__303)
  let w__304 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__305 ← (( do readReg FEAT_TWED_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__304 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TWED)))
    w__305)
  let w__306 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__307 ← (( do readReg FEAT_AFP_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__306 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AFP)))
    w__307)
  let w__308 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__309 ← (( do readReg FEAT_EBF16_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__308 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EBF16)))
    w__309)
  let w__310 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__311 ← (( do readReg FEAT_HCX_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__310 (Sail.Int.toNatChecked ((num_of_Feature FEAT_HCX)))
    w__311)
  let w__312 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__313 ← (( do readReg FEAT_LPA2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__312 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LPA2)))
    w__313)
  let w__314 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__315 ← (( do readReg FEAT_LS64_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__314 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LS64)))
    w__315)
  let w__316 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__317 ← (( do readReg FEAT_LS64_ACCDATA_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__316
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_LS64_ACCDATA))) w__317)
  let w__318 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__319 ← (( do readReg FEAT_LS64_V_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__318 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LS64_V)))
    w__319)
  let w__320 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__321 ← (( do readReg FEAT_MTE3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__320 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE3)))
    w__321)
  let w__322 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__323 ← (( do readReg FEAT_PAN3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__322 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PAN3)))
    w__323)
  let w__324 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__325 ← (( do readReg FEAT_PMUv3p7_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__324 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3p7)))
    w__325)
  let w__326 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__327 ← (( do readReg FEAT_RPRES_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__326 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RPRES)))
    w__327)
  let w__328 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__329 ← (( do readReg FEAT_SPEv1p2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__328 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPEv1p2)))
    w__329)
  let w__330 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__331 ← (( do readReg FEAT_WFxT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__330 (Sail.Int.toNatChecked ((num_of_Feature FEAT_WFxT)))
    w__331)
  let w__332 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__333 ← (( do readReg FEAT_XS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__332 (Sail.Int.toNatChecked ((num_of_Feature FEAT_XS)))
    w__333)
  let w__334 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__335 ← (( do readReg FEAT_CMOW_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__334 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CMOW)))
    w__335)
  let w__336 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__337 ← (( do readReg FEAT_Debugv8p8_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__336
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_Debugv8p8))) w__337)
  let w__338 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__339 ← (( do readReg FEAT_GICv3_NMI_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__338
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_GICv3_NMI))) w__339)
  let w__340 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__341 ← (( do readReg FEAT_HBC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__340 (Sail.Int.toNatChecked ((num_of_Feature FEAT_HBC)))
    w__341)
  let w__342 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__343 ← (( do readReg FEAT_MOPS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__342 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MOPS)))
    w__343)
  let w__344 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__345 ← (( do readReg FEAT_NMI_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__344 (Sail.Int.toNatChecked ((num_of_Feature FEAT_NMI)))
    w__345)
  let w__346 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__347 ← (( do readReg FEAT_PMUv3_EXT64_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__346
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3_EXT64))) w__347)
  let w__348 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__349 ← (( do readReg FEAT_PMUv3_TH_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__348 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3_TH)))
    w__349)
  let w__350 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__351 ← (( do readReg FEAT_PMUv3p8_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__350 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3p8)))
    w__351)
  let w__352 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__353 ← (( do readReg FEAT_SCTLR2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__352 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SCTLR2)))
    w__353)
  let w__354 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__355 ← (( do readReg FEAT_SPEv1p3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__354 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPEv1p3)))
    w__355)
  let w__356 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__357 ← (( do readReg FEAT_TCR2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__356 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TCR2)))
    w__357)
  let w__358 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__359 ← (( do readReg FEAT_TIDCP1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__358 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TIDCP1)))
    w__359)
  let w__360 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__361 ← (( do readReg FEAT_ADERR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__360 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ADERR)))
    w__361)
  let w__362 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__363 ← (( do readReg FEAT_AIE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__362 (Sail.Int.toNatChecked ((num_of_Feature FEAT_AIE)))
    w__363)
  let w__364 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__365 ← (( do readReg FEAT_ANERR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__364 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ANERR)))
    w__365)
  let w__366 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__367 ← (( do readReg FEAT_CLRBHB_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__366 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CLRBHB)))
    w__367)
  let w__368 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__369 ← (( do readReg FEAT_CSSC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__368 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CSSC)))
    w__369)
  let w__370 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__371 ← (( do readReg FEAT_Debugv8p9_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__370
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_Debugv8p9))) w__371)
  let w__372 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__373 ← (( do readReg FEAT_DoubleFault2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__372
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_DoubleFault2))) w__373)
  let w__374 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__375 ← (( do readReg FEAT_ECBHB_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__374 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ECBHB)))
    w__375)
  let w__376 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__377 ← (( do readReg FEAT_FGT2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__376 (Sail.Int.toNatChecked ((num_of_Feature FEAT_FGT2)))
    w__377)
  let w__378 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__379 ← (( do readReg FEAT_HAFT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__378 (Sail.Int.toNatChecked ((num_of_Feature FEAT_HAFT)))
    w__379)
  let w__380 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__381 ← (( do readReg FEAT_LRCPC3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__380 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LRCPC3)))
    w__381)
  let w__382 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__383 ← (( do readReg FEAT_MTE4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__382 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE4)))
    w__383)
  let w__384 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__385 ← (( do readReg FEAT_MTE_ASYM_FAULT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__384
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE_ASYM_FAULT))) w__385)
  let w__386 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__387 ← (( do readReg FEAT_MTE_ASYNC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__386
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE_ASYNC))) w__387)
  let w__388 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__389 ← (( do readReg FEAT_MTE_CANONICAL_TAGS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__388
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE_CANONICAL_TAGS))) w__389)
  let w__390 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__391 ← (( do readReg FEAT_MTE_NO_ADDRESS_TAGS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__390
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE_NO_ADDRESS_TAGS))) w__391)
  let w__392 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__393 ← (( do readReg FEAT_MTE_PERM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__392 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE_PERM)))
    w__393)
  let w__394 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__395 ← (( do readReg FEAT_MTE_STORE_ONLY_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__394
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE_STORE_ONLY))) w__395)
  let w__396 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__397 ← (( do readReg FEAT_MTE_TAGGED_FAR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__396
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_MTE_TAGGED_FAR))) w__397)
  let w__398 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__399 ← (( do readReg FEAT_PCSRv8p9_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__398 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PCSRv8p9)))
    w__399)
  let w__400 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__401 ← (( do readReg FEAT_PFAR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__400 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PFAR)))
    w__401)
  let w__402 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__403 ← (( do readReg FEAT_PMUv3_EDGE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__402
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3_EDGE))) w__403)
  let w__404 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__405 ← (( do readReg FEAT_PMUv3_ICNTR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__404
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3_ICNTR))) w__405)
  let w__406 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__407 ← (( do readReg FEAT_PMUv3_SS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__406 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3_SS)))
    w__407)
  let w__408 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__409 ← (( do readReg FEAT_PMUv3p9_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__408 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PMUv3p9)))
    w__409)
  let w__410 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__411 ← (( do readReg FEAT_PRFMSLC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__410 (Sail.Int.toNatChecked ((num_of_Feature FEAT_PRFMSLC)))
    w__411)
  let w__412 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__413 ← (( do readReg FEAT_RASSAv2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__412 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RASSAv2)))
    w__413)
  let w__414 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__415 ← (( do readReg FEAT_RASv2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__414 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RASv2)))
    w__415)
  let w__416 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__417 ← (( do readReg FEAT_RPRFM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__416 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RPRFM)))
    w__417)
  let w__418 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__419 ← (( do readReg FEAT_S1PIE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__418 (Sail.Int.toNatChecked ((num_of_Feature FEAT_S1PIE)))
    w__419)
  let w__420 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__421 ← (( do readReg FEAT_S1POE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__420 (Sail.Int.toNatChecked ((num_of_Feature FEAT_S1POE)))
    w__421)
  let w__422 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__423 ← (( do readReg FEAT_S2PIE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__422 (Sail.Int.toNatChecked ((num_of_Feature FEAT_S2PIE)))
    w__423)
  let w__424 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__425 ← (( do readReg FEAT_S2POE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__424 (Sail.Int.toNatChecked ((num_of_Feature FEAT_S2POE)))
    w__425)
  let w__426 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__427 ← (( do readReg FEAT_SPECRES2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__426 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPECRES2)))
    w__427)
  let w__428 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__429 ← (( do readReg FEAT_SPE_CRR_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__428 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPE_CRR)))
    w__429)
  let w__430 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__431 ← (( do readReg FEAT_SPE_FDS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__430 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPE_FDS)))
    w__431)
  let w__432 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__433 ← (( do readReg FEAT_SPEv1p4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__432 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPEv1p4)))
    w__433)
  let w__434 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__435 ← (( do readReg FEAT_SPMU_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__434 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SPMU)))
    w__435)
  let w__436 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__437 ← (( do readReg FEAT_THE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__436 (Sail.Int.toNatChecked ((num_of_Feature FEAT_THE)))
    w__437)
  let w__438 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__439 ← (( do readReg FEAT_DoPD_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__438 (Sail.Int.toNatChecked ((num_of_Feature FEAT_DoPD)))
    w__439)
  let w__440 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__441 ← (( do readReg FEAT_ETE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__440 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETE)))
    w__441)
  let w__442 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__443 ← (( do readReg FEAT_SVE2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__442 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE2)))
    w__443)
  let w__444 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__445 ← (( do readReg FEAT_SVE_AES_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__444 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE_AES)))
    w__445)
  let w__446 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__447 ← (( do readReg FEAT_SVE_BitPerm_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__446
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE_BitPerm))) w__447)
  let w__448 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__449 ← (( do readReg FEAT_SVE_PMULL128_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__448
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE_PMULL128))) w__449)
  let w__450 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__451 ← (( do readReg FEAT_SVE_SHA3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__450 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE_SHA3)))
    w__451)
  let w__452 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__453 ← (( do readReg FEAT_SVE_SM4_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__452 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE_SM4)))
    w__453)
  let w__454 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__455 ← (( do readReg FEAT_TME_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__454 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TME)))
    w__455)
  let w__456 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__457 ← (( do readReg FEAT_TRBE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__456 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TRBE)))
    w__457)
  let w__458 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__459 ← (( do readReg FEAT_ETEv1p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__458 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETEv1p1)))
    w__459)
  let w__460 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__461 ← (( do readReg FEAT_BRBE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__460 (Sail.Int.toNatChecked ((num_of_Feature FEAT_BRBE)))
    w__461)
  let w__462 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__463 ← (( do readReg FEAT_ETEv1p2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__462 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETEv1p2)))
    w__463)
  let w__464 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__465 ← (( do readReg FEAT_RME_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__464 (Sail.Int.toNatChecked ((num_of_Feature FEAT_RME)))
    w__465)
  let w__466 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__467 ← (( do readReg FEAT_SME_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__466 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SME)))
    w__467)
  let w__468 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__469 ← (( do readReg FEAT_SME_F64F64_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__468
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_SME_F64F64))) w__469)
  let w__470 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__471 ← (( do readReg FEAT_SME_FA64_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__470 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SME_FA64)))
    w__471)
  let w__472 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__473 ← (( do readReg FEAT_SME_I16I64_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__472
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_SME_I16I64))) w__473)
  let w__474 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__475 ← (( do readReg FEAT_BRBEv1p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__474 (Sail.Int.toNatChecked ((num_of_Feature FEAT_BRBEv1p1)))
    w__475)
  let w__476 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__477 ← (( do readReg FEAT_MEC_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__476 (Sail.Int.toNatChecked ((num_of_Feature FEAT_MEC)))
    w__477)
  let w__478 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__479 ← (( do readReg FEAT_SME2_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__478 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SME2)))
    w__479)
  let w__480 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__481 ← (( do readReg FEAT_ABLE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__480 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ABLE)))
    w__481)
  let w__482 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__483 ← (( do readReg FEAT_CHK_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__482 (Sail.Int.toNatChecked ((num_of_Feature FEAT_CHK)))
    w__483)
  let w__484 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__485 ← (( do readReg FEAT_D128_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__484 (Sail.Int.toNatChecked ((num_of_Feature FEAT_D128)))
    w__485)
  let w__486 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__487 ← (( do readReg FEAT_EBEP_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__486 (Sail.Int.toNatChecked ((num_of_Feature FEAT_EBEP)))
    w__487)
  let w__488 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__489 ← (( do readReg FEAT_ETEv1p3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__488 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ETEv1p3)))
    w__489)
  let w__490 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__491 ← (( do readReg FEAT_GCS_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__490 (Sail.Int.toNatChecked ((num_of_Feature FEAT_GCS)))
    w__491)
  let w__492 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__493 ← (( do readReg FEAT_ITE_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__492 (Sail.Int.toNatChecked ((num_of_Feature FEAT_ITE)))
    w__493)
  let w__494 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__495 ← (( do readReg FEAT_LSE128_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__494 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LSE128)))
    w__495)
  let w__496 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__497 ← (( do readReg FEAT_LVA3_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__496 (Sail.Int.toNatChecked ((num_of_Feature FEAT_LVA3)))
    w__497)
  let w__498 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__499 ← (( do readReg FEAT_SEBEP_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__498 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SEBEP)))
    w__499)
  let w__500 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__501 ← (( do readReg FEAT_SME2p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__500 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SME2p1)))
    w__501)
  let w__502 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__503 ← (( do readReg FEAT_SME_F16F16_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__502
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_SME_F16F16))) w__503)
  let w__504 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__505 ← (( do readReg FEAT_SVE2p1_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__504 (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE2p1)))
    w__505)
  let w__506 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__507 ← (( do readReg FEAT_SVE_B16B16_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__506
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_SVE_B16B16))) w__507)
  let w__508 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__509 ← (( do readReg FEAT_SYSINSTR128_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__508
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_SYSINSTR128))) w__509)
  let w__510 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__511 ← (( do readReg FEAT_SYSREG128_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__510
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_SYSREG128))) w__511)
  let w__512 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__513 ← (( do readReg FEAT_TRBE_EXT_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__512 (Sail.Int.toNatChecked ((num_of_Feature FEAT_TRBE_EXT)))
    w__513)
  let w__514 ← (( do readReg FeatureImpl ) : SailM (Vector Bool 259) )
  let w__515 ← (( do readReg FEAT_TRBE_MPAM_IMPLEMENTED ) : SailM Bool )
  writeReg FeatureImpl (vectorUpdate w__514
    (Sail.Int.toNatChecked ((num_of_Feature FEAT_TRBE_MPAM))) w__515)
  (C27cEnsureDebugConfig ())


end ArmFull.Functions
