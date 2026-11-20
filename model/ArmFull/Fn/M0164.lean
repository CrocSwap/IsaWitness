module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0114
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147 set_option backward.proofsInPublic true @[expose] public section

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
        ArmFull.assert ((0 ≤b s) && (s <b datasize)) "sail-inputs/15-instrs64.sail:2923.53-2923.54"
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
  ArmFull.assert (((lsb +i datasize) -i 1) <b (2 *i datasize)) "sail-inputs/15-instrs64.sail:10732.59-10732.60"
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
  ArmFull.assert ((pos +i 15) <b datasize) "sail-inputs/15-instrs64.sail:38730.44-38730.45"
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
                ArmFull.assert ((0 ≤b rev_index) && ((rev_index +i 7) <b datasize)) "sail-inputs/15-instrs64.sail:41065.83-41065.84"
                ArmFull.assert ((0 ≤b index) && ((index +i 7) <b datasize)) "sail-inputs/15-instrs64.sail:41066.75-41066.76"
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


end ArmFull.Functions
