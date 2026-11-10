import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork

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

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x


/-- Type quantifiers: k_ex10454715_ : Bool, k_ex10454714_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))


/-- Type quantifiers: k_n : Nat, y : Nat, k_n ≥ 0 ∧ y ≥ 0 -/
def eq_bits_int (x : (BitVec k_n)) (y : Nat) : Bool :=
  ((BitVec.toNatInt x) == y)


/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftl m (Sail.Int.toNatChecked (n)))
  else (Int.shiftr m (Sail.Int.toNatChecked ((Neg.neg n))))


/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftr m (Sail.Int.toNatChecked (n)))
  else (Int.shiftl m (Sail.Int.toNatChecked ((Neg.neg n))))


/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (((n <b 0) && (m >b 0)) : Bool)
  then ((Int.tdiv (n +i 1) m) -i 1)
  else
    (if (((n >b 0) && (m <b 0)) : Bool)
    then ((Int.tdiv (n -i 1) m) -i 1)
    else (Int.tdiv n m))


def enable_tracing (_ : Unit) : Unit :=
  ()


def disable_tracing (_ : Unit) : Unit :=
  ()


def is_tracing (_ : Unit) : Bool :=
  false


/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if ((len ≤b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.castWidth (Sail.BitVec.truncate v len))
  else (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend v len))


/-- Type quantifiers: i : Int, hi : Int, lo : Int, (Sail.Int.toNatChecked (lo : Int)) ≤
  (Sail.Int.toNatChecked (hi : Int)) -/
def integer_subrange (i : Int) (hi : Int) (lo : Int) : (BitVec (Sail.Int.toNatChecked (((hi : Int) -i (lo : Int)) +i (1 : Int)))) :=
  (Sail.BitVec.castWidth (get_slice_int (Sail.Int.toNatChecked (((hi -i lo) +i 1))) i
    (Sail.Int.toNatChecked (lo))))


/-- Type quantifiers: i : Int, hi : Nat, lo : Nat, 0 ≤ lo ∧ lo ≤ hi -/
def integer_update_subrange (i : Int) (hi : Nat) (lo : Nat) (x : (BitVec (hi - lo + 1))) : Int :=
  (set_slice_int (Sail.Int.toNatChecked (((hi -i lo) +i 1))) i lo (Sail.BitVec.castWidth x))


/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Sail.BitVec.castWidth (Complement.complement (BitVec.zero n)))


/-- Type quantifiers: k_n : Int -/
def concat_str_bits (str : String) (x : (BitVec k_n)) : String :=
  (HAppend.hAppend str (BitVec.toFormatted x))


/-- Type quantifiers: x : Int -/
def concat_str_dec (str : String) (x : Int) : String :=
  (HAppend.hAppend str (Int.repr x))


/-- Type quantifiers: k_n : Nat, List.elem k_n [8, 16, 32, 64, 128] -/
def reverse_endianness (xs : (BitVec k_n)) : (BitVec k_n) :=
  let len : Nat := (Sail.BitVec.length xs)
  if ((len == 8) : Bool)
  then (Sail.BitVec.castWidth xs)
  else
    (if ((len == 16) : Bool)
    then
      (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb xs 7 0) +++ (Sail.BitVec.extractLsb xs 15 8)))
    else
      (if ((len == 32) : Bool)
      then
        (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb xs 7 0) +++ ((Sail.BitVec.extractLsb xs 15 8) +++ ((Sail.BitVec.extractLsb
                xs 23 16) +++ (Sail.BitVec.extractLsb xs 31 24)))))
      else
        (if ((len == 64) : Bool)
        then
          (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb xs 7 0) +++ ((Sail.BitVec.extractLsb xs 15
                8) +++ ((Sail.BitVec.extractLsb xs 23 16) +++ ((Sail.BitVec.extractLsb xs 31 24) +++ ((Sail.BitVec.extractLsb
                      xs 39 32) +++ ((Sail.BitVec.extractLsb xs 47 40) +++ ((Sail.BitVec.extractLsb
                          xs 55 48) +++ (Sail.BitVec.extractLsb xs 63 56)))))))))
        else
          (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb xs 7 0) +++ ((Sail.BitVec.extractLsb xs 15
                8) +++ ((Sail.BitVec.extractLsb xs 23 16) +++ ((Sail.BitVec.extractLsb xs 31 24) +++ ((Sail.BitVec.extractLsb
                      xs 39 32) +++ ((Sail.BitVec.extractLsb xs 47 40) +++ ((Sail.BitVec.extractLsb
                          xs 55 48) +++ ((Sail.BitVec.extractLsb xs 63 56) +++ ((Sail.BitVec.extractLsb
                              xs 71 64) +++ ((Sail.BitVec.extractLsb xs 79 72) +++ ((Sail.BitVec.extractLsb
                                  xs 87 80) +++ ((Sail.BitVec.extractLsb xs 95 88) +++ ((Sail.BitVec.extractLsb
                                      xs 103 96) +++ ((Sail.BitVec.extractLsb xs 111 104) +++ ((Sail.BitVec.extractLsb
                                          xs 119 112) +++ (Sail.BitVec.extractLsb xs 127 120))))))))))))))))))))


/-- Type quantifiers: k_a : Type -/
def is_none (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => false
  | none => true


/-- Type quantifiers: k_a : Type -/
def is_some (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => true
  | none => false


/-- Type quantifiers: k_n : Int, m : Nat, m ≥ 0 -/
def extzv {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  if ((m <b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.castWidth (Sail.BitVec.truncate v m))
  else (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend v m))


/-- Type quantifiers: k_n : Int, m : Nat, m ≥ 0 -/
def extsv {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  if ((m <b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.castWidth (Sail.BitVec.truncate v m))
  else (Sail.BitVec.castWidth (Sail.BitVec.signExtend v m))


/-- Type quantifiers: k_a : Type, k_b : Type -/
def is_ok (r : (Result k_a k_b)) : Bool :=
  match r with
  | .Ok _ => true
  | .Err _ => false


/-- Type quantifiers: k_a : Type, k_b : Type -/
def is_err (r : (Result k_a k_b)) : Bool :=
  match r with
  | .Ok _ => false
  | .Err _ => true


/-- Type quantifiers: k_a : Type, k_b : Type -/
def ok_option (r : (Result k_a k_b)) : (Option k_a) :=
  match r with
  | .Ok x => (some x)
  | .Err _ => none


/-- Type quantifiers: k_a : Type, k_b : Type -/
def err_option (r : (Result k_a k_b)) : (Option k_b) :=
  match r with
  | .Ok _ => none
  | .Err err => (some err)


/-- Type quantifiers: k_a : Type, k_b : Type -/
def unwrap_or (r : (Result k_a k_b)) (y : k_a) : k_a :=
  match r with
  | .Ok x => x
  | .Err _ => y


/-- Type quantifiers: k_n : Nat, k_n > 0 -/
def sail_instr_announce (x_0 : (BitVec k_n)) : Unit :=
  ()


/-- Type quantifiers: x_0 : Nat, List.elem x_0 [32, 64] -/
def sail_branch_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()


def sail_reset_registers (_ : Unit) : Unit :=
  ()


def sail_synchronize_registers (_ : Unit) : Unit :=
  ()


/-- Type quantifiers: k_a : Type -/
def sail_mark_register (x_0 : (RegisterRef k_a)) (x_1 : String) : Unit :=
  ()


/-- Type quantifiers: k_a : Type, k_b : Type -/
def sail_mark_register_pair (x_0 : (RegisterRef k_a)) (x_1 : (RegisterRef k_b)) (x_2 : String) : Unit :=
  ()


/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def __monomorphize (bv : (BitVec k_n)) : (BitVec k_n) :=
  (Sail.BitVec.castWidth bv)


/-- Type quantifiers: n : Int -/
def __monomorphize_int (n : Int) : Int :=
  n


/-- Type quantifiers: k_b : Bool -/
def __monomorphize_bool (b : Bool) : Bool :=
  b


def undefined_Access_variety (ℓ : ChoiceLabel) (_ : Unit) : SailM Access_variety := do
  (internal_pick_at (ℓ.child 0) [AV_plain, AV_exclusive, AV_atomic_rmw])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Access_variety_of_num (arg_ : Nat) : Access_variety :=
  match arg_ with
  | 0 => AV_plain
  | 1 => AV_exclusive
  | _ => AV_atomic_rmw


def num_of_Access_variety (arg_ : Access_variety) : Int :=
  match arg_ with
  | .AV_plain => 0
  | .AV_exclusive => 1
  | .AV_atomic_rmw => 2


def undefined_Access_strength (ℓ : ChoiceLabel) (_ : Unit) : SailM Access_strength := do
  (internal_pick_at (ℓ.child 0) [AS_normal, AS_rel_or_acq, AS_acq_rcpc])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Access_strength_of_num (arg_ : Nat) : Access_strength :=
  match arg_ with
  | 0 => AS_normal
  | 1 => AS_rel_or_acq
  | _ => AS_acq_rcpc


def num_of_Access_strength (arg_ : Access_strength) : Int :=
  match arg_ with
  | .AS_normal => 0
  | .AS_rel_or_acq => 1
  | .AS_acq_rcpc => 2


/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_read_request_is_exclusive (request : (Mem_read_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_explicit eak =>
    (match eak.variety with
    | .AV_exclusive => true
    | _ => false)
  | _ => false


/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_read_request_is_ifetch (request : (Mem_read_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_ifetch () => true
  | _ => false


def __monomorphize_reads : Bool := false


def __monomorphize_writes : Bool := false


/-- Type quantifiers: k_n : Nat, k_vasize : Nat, k_pa : Type, k_translation_summary : Type, k_arch_ak
  : Type, k_n > 0 ∧ k_vasize > 0 -/
def mem_write_request_is_exclusive (request : (Mem_write_request k_n k_vasize k_pa k_translation_summary k_arch_ak)) : Bool :=
  match request.access_kind with
  | .AK_explicit eak =>
    (match eak.variety with
    | .AV_exclusive => true
    | _ => false)
  | _ => false


/-- Type quantifiers: x_0 : Nat, List.elem x_0 [32, 64] -/
def sail_address_announce (x_0 : Nat) (x_1 : (BitVec x_0)) : Unit :=
  ()


/-- Type quantifiers: k_ex10455118_ : Bool, k_ex10455117_ : Bool -/
def implies (p : Bool) (q : Bool) : Bool :=
  ((! p) || q)


/-- Type quantifiers: n : Int, i : Int, j : Int -/
def in_range (n : Int) (i : Int) (j : Int) : Bool :=
  if ((i <b j) : Bool)
  then ((i ≤b n) && (n ≤b j))
  else ((j ≤b n) && (n ≤b i))


def min_real (n : real) (m : real) : real :=
  if ((lteq_real n m) : Bool)
  then n
  else m


def max_real (n : real) (m : real) : real :=
  if ((lteq_real n m) : Bool)
  then m
  else n


/-- Type quantifiers: n : Int -/
def UInt1 (n : Int) (x : (BitVec (Sail.Int.toNatChecked (n : Int)))) : Int :=
  (BitVec.toNatInt x)


/-- Type quantifiers: n : Nat, n > 0 -/
def SInt1 (n : Nat) (x : (BitVec n)) : Int :=
  (BitVec.toInt x)


/-- Type quantifiers: n : Nat, k_m : Nat, n ≥ 0 ∧ k_m > 0 ∧ (n % k_m) = 0 -/
def Replicate__1 {n : _} (x : (BitVec k_m)) : (BitVec n) :=
  (Sail.BitVec.castWidth (BitVec.replicateBits x
    (Sail.Int.toNatChecked ((Int.ediv n (Sail.BitVec.length x))))))


/-- Type quantifiers: n : Nat, n ≥ 0 -/
def Zeros {n : _} : (BitVec n) :=
  (Sail.BitVec.castWidth (BitVec.zero n))


/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def IsZero (x : (BitVec k_n)) : Bool :=
  (x == (Sail.BitVec.castWidth (BitVec.zero (Sail.BitVec.length x))))


def Bit (b : (BitVec 1)) : (BitVec 1) :=
  (BitVec.access b 0)


def Bits (b : (BitVec 1)) : (BitVec 1) :=
  if ((b == 1#1) : Bool)
  then 1#1
  else 0#1


/-- Type quantifiers: k_n : Nat, m : Nat, k_n > 0 ∧ m ≥ k_n -/
def SignExtend1 {m : _} (x : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.castWidth (sign_extend x m))


/-- Type quantifiers: k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ k_n -/
def ZeroExtend1 {m : _} (x : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend x m))


/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def Slice_int (i : Int) (l : Int) (n : Nat) : (BitVec n) :=
  (Sail.BitVec.castWidth (get_slice_int n i (Sail.Int.toNatChecked (l))))


def RoundTowardsZero (r : real) : Int :=
  if ((lt_real r (to_real 0)) : Bool)
  then (round_up r)
  else (round_down r)


def undefined_signal (ℓ : ChoiceLabel) (_ : Unit) : SailM signal := do
  (internal_pick_at (ℓ.child 0) [LOW, HIGH])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def signal_of_num (arg_ : Nat) : signal :=
  match arg_ with
  | 0 => LOW
  | _ => HIGH


def num_of_signal (arg_ : signal) : Int :=
  match arg_ with
  | .LOW => 0
  | .HIGH => 1


def IsUNDEFINED (ex : exception) : Bool :=
  match ex with
  | .Error_Undefined () => true
  | _ => false


def IsUNPREDICTABLE (ex : exception) : Bool :=
  match ex with
  | .Error_Unpredictable () => true
  | _ => false


def IsSEE (ex : exception) : Bool :=
  match ex with
  | .Error_See _ => true
  | _ => false


def IsExceptionTaken (ex : exception) : Bool :=
  match ex with
  | .Error_ExceptionTaken () => true
  | _ => false


def IsSError (ex : exception) : Bool :=
  match ex with
  | .Error_SError _ => true
  | _ => false


/-- Type quantifiers: k_ex10455127_ : Bool -/
def ThrowSError (iesb_req : Bool) : SailM Unit := do
  sailThrow ((Error_SError iesb_req))


def ReservedEncoding (_ : Unit) : SailM Unit := do
  sailThrow ((Error_ReservedEncoding ()))


/-- Type quantifiers: k_ex10455130_ : Bool -/
def BoolStr (b : Bool) : String :=
  match b with
  | true => "true"
  | false => "false"


/-- Type quantifiers: n : Int -/
def append_int (str : String) (n : Int) : String :=
  (String.append str (dec_str n))


/-- Type quantifiers: k_ex10455132_ : Bool -/
def append_bool (str : String) (b : Bool) : String :=
  (String.append str
    (if (b : Bool)
    then "true"
    else "false"))


/-- Type quantifiers: i : Int -/
def print_integer (i : Int) : Unit :=
  (print_int "" i)


def print_newline (_ : Unit) : Unit :=
  (print_endline "")


def __UNKNOWN_integer (_ : Unit) : SailM Int := do
  (undefined_int_at (← occLabel 7) ())


def __UNKNOWN_boolean (_ : Unit) : SailM Bool := do
  (undefined_bool_at (← occLabel 8) ())


def __UNKNOWN_real (_ : Unit) : SailM real := do
  (undefined_real_at (.site 9) ())


def __UNKNOWN_string (_ : Unit) : SailM String := do
  (undefined_string_at (.site 10) ())


def __UNKNOWN_bit (_ : Unit) : SailM (BitVec 1) := do
  (undefined_bitvector_at (← occLabel 11) 1)


/-- Type quantifiers: vl : Nat, vl ≥ 0 -/
def PL_of_VL (vl : Nat) : Nat :=
  (Sail.Int.toNatChecked ((Int.ediv vl 8)))


def __GetVerbosity (_ : Unit) : SailM (BitVec 64) := do
  (pure (0x0000000000000000#64))


def EndOfInstruction (_ : Unit) : SailM Unit := do
  sailThrow ((Error_ExceptionTaken ()))


def EncodingSpecificOperations (_ : Unit) : Unit :=
  ()


/-- Type quantifiers: k_N : Int, shift : Int -/
def LSL_C (x : (BitVec k_N)) (shift : Int) : ((BitVec k_N) × (BitVec 1)) :=
  let carry_out :=
    if (((shift >b 0) && (shift ≤b (Sail.BitVec.length x))) : Bool)
    then (BitVec.access x (Sail.Int.toNatChecked (((Sail.BitVec.length x) -i shift))))
    else 0#1
  ((x <<< shift), (BitVec.setWidth 1 (BitVec.join1 [carry_out])))


/-- Type quantifiers: k_N : Int, shift : Int -/
def LSR_C (x : (BitVec k_N)) (shift : Int) : ((BitVec k_N) × (BitVec 1)) :=
  let carry_out :=
    if (((shift >b 0) && (shift ≤b (Sail.BitVec.length x))) : Bool)
    then (BitVec.access x (Sail.Int.toNatChecked ((shift -i 1))))
    else 0#1
  ((x >>> shift), (BitVec.setWidth 1 (BitVec.join1 [carry_out])))


/-- Type quantifiers: k_N : Nat, shift : Int, k_N > 0 -/
def ROR_C (x : (BitVec k_N)) (shift : Int) : SailM ((BitVec k_N) × (BitVec 1)) := do
  ArmFull.assert (shift >b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/builtins.sail:100.20-100.21"
  let m : Nat := (Nat.mod (Sail.Int.toNatChecked (shift)) (Sail.BitVec.length x))
  let result : (BitVec k_N) := ((x >>> m) ||| (x <<< ((Sail.BitVec.length x) -i m)))
  let carry_out : (BitVec 1) :=
    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
        (Sail.Int.toNatChecked (((Sail.BitVec.length x) -i 1))))]))
  (pure ((result, carry_out)))


/-- Type quantifiers: k_N : Nat, shift : Nat, k_N > 0 ∧ shift ≥ 0 -/
def ROR (x : (BitVec k_N)) (shift : Nat) : (BitVec k_N) :=
  if ((shift == 0) : Bool)
  then (Sail.BitVec.castWidth x)
  else
    (let m : Nat := (Nat.mod shift (Sail.BitVec.length x))
    (Sail.BitVec.castWidth ((x >>> m) ||| (x <<< ((Sail.BitVec.length x) -i m)))))


/-- Type quantifiers: k_N : Nat, k_is_unsigned : Bool, k_N ≥ 0 -/
def asl_Int (x : (BitVec k_N)) (is_unsigned : Bool) : SailM Int := do
  let result ← (( do
    if (is_unsigned : Bool)
    then (pure ((BitVec.toNat x)))
    else
      (do
        ArmFull.assert ((Sail.BitVec.length x) >b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/builtins.sail:134.33-134.34"
        (pure ((BitVec.toInt x)))) ) : SailM Int )
  (pure (result))


/-- Type quantifiers: k_N : Nat, e : Int, size : Nat, k_N ≥ 0 ∧
  size ≥ 0 ∧
  (Sail.Int.toNatChecked ((e : Int) *i (size : Int))) ≤
  (Sail.Int.toNatChecked ((((e : Int) *i (size : Int)) +i (size : Int)) -i (1 : Int))) ∨
  (not
  ((Sail.Int.toNatChecked (e : Int)) ≥ 0 ∧
  (Sail.Int.toNatChecked (((e : Int) +i (1 : Int)) *i (size : Int))) ≤ k_N)) -/
def Elem_read (vector_name : (BitVec k_N)) (e : Int) (size : Nat) : SailM (BitVec size) := do
  ArmFull.assert ((e ≥b 0) && (((e +i 1) *i size) ≤b (Sail.BitVec.length vector_name))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/builtins.sail:195.40-195.41"
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb vector_name
      (Sail.Int.toNatChecked ((((e *i size) +i size) -i 1))) (Sail.Int.toNatChecked ((e *i size)))))))


/-- Type quantifiers: k_N : Nat, e : Int, size : Nat, k_N ≥ 0 ∧
  size ≥ 0 ∧
  (Sail.Int.toNatChecked ((e : Int) *i (size : Int))) ≤
  (Sail.Int.toNatChecked ((((e : Int) +i (1 : Int)) *i (size : Int)) -i (1 : Int))) ∨
  (not
  ((Sail.Int.toNatChecked (e : Int)) ≥ 0 ∧
  (Sail.Int.toNatChecked (((e : Int) +i (1 : Int)) *i (size : Int))) ≤ k_N)) -/
def Elem_set (vector_name__arg : (BitVec k_N)) (e : Int) (size : Nat) (value_name : (BitVec size)) : SailM (BitVec k_N) := do
  let vector_name : (BitVec k_N) := vector_name__arg
  ArmFull.assert ((e ≥b 0) && (((e +i 1) *i size) ≤b (Sail.BitVec.length vector_name__arg))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/builtins.sail:205.40-205.41"
  let vector_name : (BitVec k_N) :=
    (Sail.BitVec.updateSubrange vector_name (Sail.Int.toNatChecked ((((e +i 1) *i size) -i 1)))
      (Sail.Int.toNatChecked ((e *i size))) (Sail.BitVec.castWidth value_name))
  (pure ((Sail.BitVec.castWidth vector_name)))


def undefined_Configuration_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_Configuration_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_Configuration_Type_bits (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v (Sail.Int.toNatChecked ((32 -i 1))) 0)


def _update_Configuration_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_ACCDATA_EL1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCFGR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCFGR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCG1IDR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCGCR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCGCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCIDR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCIDR2_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCIDR3_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCNTENCLR0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCNTENCLR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCNTENCLR1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCNTENCLR1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCNTENSET0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCNTENSET0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCNTENSET1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCNTENSET1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMCR_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMCR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMDEVARCH_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMDEVTYPE_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMEVCNTR0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMEVCNTR0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMEVCNTR1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMEVCNTR1_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMEVTYPER0_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMEVTYPER0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMEVTYPER1_EL0_Type_bits (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((64 -i 1))) 0 x)


def _update_AMEVTYPER1_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMIIDR_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


def _update_AMPIDR0_Type_bits (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v (Sail.Int.toNatChecked ((32 -i 1))) 0 x)


end ArmFull.Functions
