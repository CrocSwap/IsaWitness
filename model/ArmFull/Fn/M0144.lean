import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0019
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0099
import ArmFull.Fn.M0108
import ArmFull.Fn.M0111
import ArmFull.Fn.M0113

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

/-- Type quantifiers: k_extended : Bool -/
def C27bDebugCount (extended : Bool) : SailM Int := do
  let limit : Nat :=
    if (extended : Bool)
    then 64
    else 16
  (undefined_range_at (.site 8672) 2 limit)


/-- Type quantifiers: b : Int -/
def C27bContextCount (b : Int) : SailM Int := do
  ArmFull.assert (b ≥b 1) "armcert/armcert_c27b.sail:59.17-59.18"
  (undefined_range_at (.site 8673) 1 b)


/-- Type quantifiers: j : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def is_zero_subrange (xs : (BitVec k_n)) (i : Int) (j : Int) : Bool :=
  ((Sail.BitVec.castWidth (m := k_n) (xs &&& (Sail.BitVec.castWidth (slice_mask
        (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1))))) == (Sail.BitVec.castWidth (extzv
      (m := (Sail.BitVec.length xs)) (0#1 : (BitVec 1)))))


/-- Type quantifiers: l : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def is_zeros_slice (xs : (BitVec k_n)) (i : Int) (l : Int) : Bool :=
  ((Sail.BitVec.castWidth (m := k_n) (xs &&& (Sail.BitVec.castWidth (slice_mask
        (n := (Sail.BitVec.length xs)) i l)))) == (Sail.BitVec.castWidth (extzv
      (m := (Sail.BitVec.length xs)) (0#1 : (BitVec 1)))))


/-- Type quantifiers: j : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def is_ones_subrange (xs : (BitVec k_n)) (i : Int) (j : Int) : Bool :=
  let m : (BitVec k_n) :=
    (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1)))
  ((xs &&& m) == m)


/-- Type quantifiers: j : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def is_ones_slice (xs : (BitVec k_n)) (i : Int) (j : Int) : Bool :=
  let m : (BitVec k_n) := (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) i j))
  ((xs &&& m) == m)


/-- Type quantifiers: l' : Int, i' : Int, l : Int, i : Int, k_n : Nat, k_m : Nat, r : Nat, k_n ≥ 0
  ∧ k_m ≥ 0 ∧ r ≥ 0 -/
def slice_slice_concat {r : _} (xs : (BitVec k_n)) (i : Int) (l : Int) (ys : (BitVec k_m)) (i' : Int) (l' : Int) : (BitVec r) :=
  let xs := ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) i l))) >>> i)
  let ys :=
    ((ys &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length ys)) i' l'))) >>> i')
  (Sail.BitVec.castWidth ((Sail.BitVec.castWidth (m := r) ((extzv (m := r) xs) <<< l')) ||| (Sail.BitVec.castWidth (extzv
      (m := r) ys))))


/-- Type quantifiers: i : Int, k_n : Nat, l : Int, l' : Int, k_n ≥ 0 ∧
  (Sail.Int.toNatChecked ((l : Int) +i (l' : Int))) ≥ 0 -/
def slice_zeros_concat (xs : (BitVec k_n)) (i : Int) (l : Int) (l' : Int) : (BitVec (Sail.Int.toNatChecked ((l : Int) +i (l' : Int)))) :=
  let xs := ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) i l))) >>> i)
  (Sail.BitVec.castWidth ((extzv (m := (Sail.Int.toNatChecked ((l +i l')))) xs) <<< l'))


/-- Type quantifiers: j' : Int, i' : Int, j : Int, i : Int, k_n : Nat, k_n ≥ 0 -/
def subrange_subrange_eq (xs : (BitVec k_n)) (i : Int) (j : Int) (ys : (BitVec k_n)) (i' : Int) (j' : Int) : Bool :=
  let xs :=
    ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length ys)) j ((i -i j) +i 1)))) >>> j)
  let ys :=
    ((ys &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length ys)) j' ((i' -i j') +i 1)))) >>> j')
  (xs == ys)


/-- Type quantifiers: k_n : Nat, i : Int, j : Int, k_m : Nat, i' : Int, j' : Int, s : Nat, s ≥ 0
  ∧ k_n ≥ 0 ∧ k_m ≥ 0 -/
def subrange_subrange_concat {s : _} (xs : (BitVec k_n)) (i : Int) (j : Int) (ys : (BitVec k_m)) (i' : Int) (j' : Int) : (BitVec s) :=
  let xs :=
    ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1)))) >>> j)
  let ys :=
    ((ys &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length ys)) j' ((i' -i j') +i 1)))) >>> j')
  (Sail.BitVec.castWidth ((Sail.BitVec.castWidth (m := s) ((extzv (m := s) xs) <<< ((i' -i j') +i 1))) ||| (Sail.BitVec.castWidth (extzv
      (m := s) ys))))


/-- Type quantifiers: shift : Int, j : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def place_subrange {m : _} (xs : (BitVec k_n)) (i : Int) (j : Int) (shift : Int) : (BitVec m) :=
  let xs :=
    ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1)))) >>> j)
  (Sail.BitVec.castWidth ((extzv (m := m) xs) <<< shift))


/-- Type quantifiers: shift : Int, l : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def place_slice {m : _} (xs : (BitVec k_n)) (i : Int) (l : Int) (shift : Int) : (BitVec m) :=
  let xs := ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) i l))) >>> i)
  (Sail.BitVec.castWidth ((extzv (m := m) xs) <<< shift))


/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def set_slice_zeros {n : _} (xs : (BitVec n)) (i : Int) (l : Int) : (BitVec n) :=
  let ys : (BitVec n) := (Sail.BitVec.castWidth (slice_mask (n := n) i l))
  (Sail.BitVec.castWidth (xs &&& (Complement.complement ys)))


/-- Type quantifiers: l : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def zext_slice {m : _} (xs : (BitVec k_n)) (i : Int) (l : Int) : (BitVec m) :=
  let xs := ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) i l))) >>> i)
  (Sail.BitVec.castWidth (extzv (m := m) xs))


/-- Type quantifiers: l : Int, i : Int, k_n : Nat, m : Nat, k_n ≥ 0 ∧ m ≥ 0 -/
def sext_slice {m : _} (xs : (BitVec k_n)) (i : Int) (l : Int) : (BitVec m) :=
  let xs :=
    (BitVec.sshiftRight
      ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) i l))) <<< (((Sail.BitVec.length
              xs) -i i) -i l)) (Sail.Int.toNatChecked (((Sail.BitVec.length xs) -i l))))
  (Sail.BitVec.castWidth (extsv (m := m) xs))


/-- Type quantifiers: i : Int, k_n : Nat, l : Nat, k_n ≥ 0 ∧ l ≥ 0 -/
def unsigned_slice (xs : (BitVec k_n)) (i : Int) (l : Nat) : Int :=
  let xs := ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) i l))) >>> i)
  (Nat.mod (BitVec.toNat xs) (Sail.Int.toNatChecked ((pow2 l))))


/-- Type quantifiers: k_n : Nat, i : Int, j : Int, k_n ≥ 0 ∧
  (Sail.Int.toNatChecked ((i : Int) -i (j : Int))) ≥ 0 -/
def unsigned_subrange (xs : (BitVec k_n)) (i : Int) (j : Int) : Int :=
  let xs :=
    ((xs &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length xs)) j ((i -i j) +i 1)))) >>> j)
  (Nat.mod (BitVec.toNat xs)
    (Sail.Int.toNatChecked ((pow2 (Sail.Int.toNatChecked (((i -i j) +i 1)))))))


/-- Type quantifiers: n : Nat, s1 : Nat, e1 : Nat, k_n2 : Nat, s2 : Nat, e2 : Nat, 0 ≤ e1 ∧
  e1 ≤ s1 ∧ s1 < n ∧ 0 ≤ e2 ∧ e2 ≤ s2 ∧ s2 < k_n2 ∧ (s1 - e1) = (s2 - e2) -/
def vector_update_subrange_from_subrange {n : _} (v1 : (BitVec n)) (s1 : Nat) (e1 : Nat) (v2 : (BitVec k_n2)) (s2 : Nat) (e2 : Nat) : (BitVec n) :=
  let xs :=
    ((v2 &&& (Sail.BitVec.castWidth (slice_mask (n := (Sail.BitVec.length v2)) e2 ((s2 -i e2) +i 1)))) >>> e2)
  let xs := ((extzv (m := n) xs) <<< e1)
  let ys :=
    (v1 &&& (Sail.BitVec.castWidth (Complement.complement
        (slice_mask (n := (Sail.BitVec.length xs)) e1 ((s1 -i e1) +i 1)))))
  (Sail.BitVec.castWidth (xs ||| ys))


/-- Type quantifiers: y : Int, k_n : Nat, k_n ≥ 0 -/
def Align_bits (x : (BitVec k_n)) (y : Int) : (BitVec k_n) :=
  (Sail.BitVec.castWidth (Slice_int (Align_int (BitVec.toNatInt x) y) 0 (Sail.BitVec.length x)))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def CountLeadingZeroBits (x : (BitVec k_N)) : Int :=
  ((Sail.BitVec.length x) -i ((HighestSetBit x) +i 1))


def Havev8p9Debug (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_Debugv8p9)


def undefined_AccessDescriptor (ℓ : ChoiceLabel) (_ : Unit) : SailM AccessDescriptor := do
  let w__0 ← (( do (undefined_AccessType (ℓ.child 0) ()) ) : SailM AccessType )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 2) ) : SailM (BitVec 2) )
  let w__2 ← (( do (undefined_SecurityState (ℓ.child 2) ()) ) : SailM SecurityState )
  let w__3 ← (( do (undefined_bool_at (ℓ.child 3) ()) ) : SailM Bool )
  let w__4 ← (( do (undefined_bool_at (ℓ.child 4) ()) ) : SailM Bool )
  let w__5 ← (( do (undefined_bool_at (ℓ.child 5) ()) ) : SailM Bool )
  let w__6 ← (( do (undefined_bool_at (ℓ.child 6) ()) ) : SailM Bool )
  let w__7 ← (( do (undefined_bool_at (ℓ.child 7) ()) ) : SailM Bool )
  let w__8 ← (( do (undefined_bool_at (ℓ.child 8) ()) ) : SailM Bool )
  let w__9 ← (( do (undefined_MemAtomicOp (ℓ.child 9) ()) ) : SailM MemAtomicOp )
  let w__10 ← (( do (undefined_bool_at (ℓ.child 10) ()) ) : SailM Bool )
  let w__11 ← (( do (undefined_bool_at (ℓ.child 11) ()) ) : SailM Bool )
  let w__12 ← (( do (undefined_bool_at (ℓ.child 12) ()) ) : SailM Bool )
  let w__13 ← (( do (undefined_CacheOp (ℓ.child 13) ()) ) : SailM CacheOp )
  let w__14 ← (( do (undefined_CacheOpScope (ℓ.child 14) ()) ) : SailM CacheOpScope )
  let w__15 ← (( do (undefined_CacheType (ℓ.child 15) ()) ) : SailM CacheType )
  let w__16 ← (( do (undefined_bool_at (ℓ.child 16) ()) ) : SailM Bool )
  let w__17 ← (( do (undefined_bool_at (ℓ.child 17) ()) ) : SailM Bool )
  let w__18 ← (( do (undefined_bool_at (ℓ.child 18) ()) ) : SailM Bool )
  let w__19 ← (( do (undefined_bool_at (ℓ.child 19) ()) ) : SailM Bool )
  let w__20 ← (( do (undefined_bool_at (ℓ.child 20) ()) ) : SailM Bool )
  let w__21 ← (( do (undefined_bool_at (ℓ.child 21) ()) ) : SailM Bool )
  let w__22 ← (( do (undefined_bool_at (ℓ.child 22) ()) ) : SailM Bool )
  let w__23 ← (( do (undefined_bool_at (ℓ.child 23) ()) ) : SailM Bool )
  let w__24 ← (( do (undefined_bool_at (ℓ.child 24) ()) ) : SailM Bool )
  let w__25 ← (( do (undefined_bool_at (ℓ.child 25) ()) ) : SailM Bool )
  let w__26 ← (( do (undefined_bool_at (ℓ.child 26) ()) ) : SailM Bool )
  let w__27 ← (( do (undefined_bool_at (ℓ.child 27) ()) ) : SailM Bool )
  let w__28 ← (( do (undefined_VARange (ℓ.child 28) ()) ) : SailM VARange )
  let w__29 ← (( do (undefined_bool_at (ℓ.child 29) ()) ) : SailM Bool )
  let w__30 ← (( do (undefined_bool_at (ℓ.child 30) ()) ) : SailM Bool )
  let w__31 ← (( do (undefined_bool_at (ℓ.child 31) ()) ) : SailM Bool )
  let w__32 ← (( do (undefined_MPAMinfo (ℓ.child 32) ()) ) : SailM MPAMinfo )
  (pure ({ acctype := w__0
           el := w__1
           ss := w__2
           acqsc := w__3
           acqpc := w__4
           relsc := w__5
           limitedordered := w__6
           exclusive := w__7
           atomicop := w__8
           modop := w__9
           nontemporal := w__10
           read := w__11
           write := w__12
           cacheop := w__13
           opscope := w__14
           cachetype := w__15
           pan := w__16
           transactional := w__17
           nonfault := w__18
           firstfault := w__19
           first := w__20
           contiguous := w__21
           streamingsve := w__22
           ls64 := w__23
           mops := w__24
           rcw := w__25
           rcws := w__26
           toplevel := w__27
           varange := w__28
           a32lsmd := w__29
           tagchecked := w__30
           tagaccess := w__31
           mpam := w__32 }))


def __UNKNOWN_MemoryAttributes (_ : Unit) : SailM MemoryAttributes := do
  (undefined_MemoryAttributes (← occLabel 135) ())


def __UNKNOWN_FullAddress (_ : Unit) : SailM FullAddress := do
  (undefined_FullAddress (← occLabel 140) ())


def __UNKNOWN_PhysMemRetStatus (_ : Unit) : SailM PhysMemRetStatus := do
  (undefined_PhysMemRetStatus (← occLabel 171) ())


def undefined_CacheRecord (ℓ : ChoiceLabel) (_ : Unit) : SailM CacheRecord := do
  let w__0 ← (( do (undefined_AccessType (ℓ.child 0) ()) ) : SailM AccessType )
  let w__1 ← (( do (undefined_CacheOp (ℓ.child 1) ()) ) : SailM CacheOp )
  let w__2 ← (( do (undefined_CacheOpScope (ℓ.child 2) ()) ) : SailM CacheOpScope )
  let w__3 ← (( do (undefined_CacheType (ℓ.child 3) ()) ) : SailM CacheType )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 64) ) : SailM (BitVec 64) )
  let w__5 ← (( do (undefined_FullAddress (ℓ.child 5) ()) ) : SailM FullAddress )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 64) ) : SailM (BitVec 64) )
  let w__7 ← (( do (undefined_int_at (ℓ.child 7) ()) ) : SailM Int )
  let w__8 ← (( do (undefined_int_at (ℓ.child 8) ()) ) : SailM Int )
  let w__9 ← (( do (undefined_int_at (ℓ.child 9) ()) ) : SailM Int )
  let w__10 ← (( do (undefined_Shareability (ℓ.child 10) ()) ) : SailM Shareability )
  let w__11 ← (( do (undefined_bool_at (ℓ.child 11) ()) ) : SailM Bool )
  let w__12 ← (( do (undefined_bool_at (ℓ.child 12) ()) ) : SailM Bool )
  let w__13 ← (( do (undefined_bitvector_at (ℓ.child 13) 16) ) : SailM (BitVec 16) )
  let w__14 ← (( do (undefined_bool_at (ℓ.child 14) ()) ) : SailM Bool )
  let w__15 ← (( do (undefined_bitvector_at (ℓ.child 15) 16) ) : SailM (BitVec 16) )
  let w__16 ← (( do (undefined_SecurityState (ℓ.child 16) ()) ) : SailM SecurityState )
  let w__17 ← (( do (undefined_CachePASpace (ℓ.child 17) ()) ) : SailM CachePASpace )
  (pure ({ acctype := w__0
           cacheop := w__1
           opscope := w__2
           cachetype := w__3
           regval := w__4
           paddress := w__5
           vaddress := w__6
           setnum := w__7
           waynum := w__8
           level := w__9
           shareability := w__10
           translated := w__11
           is_vmid_valid := w__12
           vmid := w__13
           is_asid_valid := w__14
           asid := w__15
           security := w__16
           cpas := w__17 }))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def ignore_data_dependency (n : Nat) : Unit :=
  if ((n ≤b 30) : Bool)
  then (sail_ignore_write_to (register_ref n))
  else ()


def undefined_ExceptionRecord (ℓ : ChoiceLabel) (_ : Unit) : SailM ExceptionRecord := do
  let w__0 ← (( do (undefined_Exception (ℓ.child 0) ()) ) : SailM Exception )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 25) ) : SailM (BitVec 25) )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 24) ) : SailM (BitVec 24) )
  let w__3 ← (( do (undefined_FullAddress (ℓ.child 3) ()) ) : SailM FullAddress )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 64) ) : SailM (BitVec 64) )
  let w__5 ← (( do (undefined_bool_at (ℓ.child 5) ()) ) : SailM Bool )
  let w__6 ← (( do (undefined_bool_at (ℓ.child 6) ()) ) : SailM Bool )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do (undefined_bitvector_at (ℓ.child 8) 56) ) : SailM (BitVec 56) )
  let w__9 ← (( do (undefined_bool_at (ℓ.child 9) ()) ) : SailM Bool )
  (pure ({ exceptype := w__0
           syndrome := w__1
           syndrome2 := w__2
           paddress := w__3
           vaddress := w__4
           ipavalid := w__5
           pavalid := w__6
           NS := w__7
           ipaddress := w__8
           trappedsyscallinst := w__9 }))


def undefined_TTWState (ℓ : ChoiceLabel) (_ : Unit) : SailM TTWState := do
  let w__0 ← (( do (undefined_bool_at (ℓ.child 0) ()) ) : SailM Bool )
  let w__1 ← (( do (undefined_int_at (ℓ.child 1) ()) ) : SailM Int )
  let w__2 ← (( do (undefined_FullAddress (ℓ.child 2) ()) ) : SailM FullAddress )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 1) ) : SailM (BitVec 1) )
  let w__4 ← (( do (undefined_bool_at (ℓ.child 4) ()) ) : SailM Bool )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 1) ) : SailM (BitVec 1) )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 1) ) : SailM (BitVec 1) )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do (undefined_bitvector_at (ℓ.child 8) 1) ) : SailM (BitVec 1) )
  let w__9 ← (( do (undefined_SDFType (ℓ.child 9) ()) ) : SailM SDFType )
  let w__10 ← (( do (undefined_bitvector_at (ℓ.child 10) 4) ) : SailM (BitVec 4) )
  let w__11 ← (( do (undefined_MemoryAttributes (ℓ.child 11) ()) ) : SailM MemoryAttributes )
  let w__12 ← (( do (undefined_Permissions (ℓ.child 12) ()) ) : SailM Permissions )
  (pure ({ istable := w__0
           level := w__1
           baseaddress := w__2
           contiguous := w__3
           s1assured := w__4
           s2assuredonly := w__5
           disch := w__6
           nG := w__7
           guardedpage := w__8
           sdftype := w__9
           domain := w__10
           memattrs := w__11
           permissions := w__12 }))


def __UNKNOWN_GPTTLBLine (_ : Unit) : SailM GPTTLBLine := do
  (undefined_GPTTLBLine (← occLabel 471) ())


def HaveAArch64 (_ : Unit) : SailM Bool := do
  if ((← do
       if ((← do
            if ((← do
                 (IsFeatureImplemented FEAT_AA64EL0)) : Bool)
            then (pure true)
            else
              (do
                (IsFeatureImplemented FEAT_AA64EL1))) : Bool)
       then (pure true)
       else
         (do
           (IsFeatureImplemented FEAT_AA64EL2))) : Bool)
  then (pure true)
  else
    (do
      (IsFeatureImplemented FEAT_AA64EL3))


def HaveSecureEL2Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SEL2)


def HaveVirtHostExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_VHE)


def HaveStatisticalProfilingv1p2 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SPEv1p2)


def HaveFeatHPMN0 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_HPMN0)


def HavePMUv3ICNTR (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3_ICNTR)


def HavePMUv3 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3)


def HaveRME (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_RME)


def HaveNoninvasiveDebugAuth (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (IsFeatureImplemented FEAT_Debugv8p4) ) : SailM Bool )
  (pure ((! w__0)))


def HaveHPMDExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3p1)


def HaveNoSecurePMUDisableOverride (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_Debugv8p2)


def HavePMUv3p5 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3p5)


def HavePMUv3p7 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3p7)


def HaveStatisticalProfilingv1p1 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SPEv1p1)


def HaveStatisticalProfilingv1p4 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SPEv1p4)


def HavePMUv3EDGE (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3_EDGE)


def HavePMUv3TH (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3_TH)


def HaveECVExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_ECV)


def HaveMTEAsymFaultExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MTE4)


/-- Type quantifiers: N : Nat, N ≥ 0 -/
def __IMPDEF_bits (N : Nat) (x : String) : SailM (BitVec N) := do
  ((Sail.BitVec.castWidth ) <$> (ImpDefBits x N))


def HaveBRBEv1p1 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_BRBEv1p1)


def HavePACExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PAuth)


def BranchEncCycleCount (_ : Unit) : SailM ((BitVec 1) × (BitVec 14)) := do
  let cc ← (( do (BranchRawCycleCount ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (BRBCycleCountingEnabled ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        (FirstBranchAfterProhibited ())) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure ((1#1, (Zeros (n := 14)))))
  else
    (do
      let E ← (( do (undefined_bitvector_at (← occLabel 569) 6) ) : SailM (BitVec 6) )
      let M ← (( do (undefined_bitvector_at (← occLabel 570) 8) ) : SailM (BitVec 8) )
      let (E, M) ← (( do
        if ((cc <b (2 ^i 8)) : Bool)
        then
          (let E : (BitVec 6) := (Zeros (n := 6))
          let M : (BitVec 8) := (integer_subrange cc 7 0)
          (pure (E, M)))
        else
          (do
            let (E, M) ← (( do
              if ((cc ≥b (2 ^i 20)) : Bool)
              then
                (let E : (BitVec 6) := (Ones (n := 6))
                let M : (BitVec 8) := (Ones (n := 8))
                (pure (E, M)))
              else
                (do
                  let E : (BitVec 6) := (integer_subrange 1 5 0)
                  let (E, cc) ← (( do
                    let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (E, cc) => (pure (cc ≥b (2 ^i 9)))) (E, cc)
                      fun (E, cc) => do
                        (pure (let E : (BitVec 6) := (BitVec.addInt E 1)
                          let cc : Int := (fdiv_int cc 2)
                          (E, cc) : ((BitVec 6) × Int)))
                    (pure loop_vars) ) : SailM ((BitVec 6) × Int) )
                  let cc : Int := cc
                  let M : (BitVec 8) := (integer_subrange cc 7 0)
                  (pure (E, M))) ) : SailM ((BitVec 6) × (BitVec 8)) )
            (pure (E, M))) ) : SailM ((BitVec 6) × (BitVec 8)) )
      (pure ((0#1, (E +++ M)))))


def HaveTME (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_TME)


def BadMode (mode : (BitVec 5)) : SailM Bool := do
  let valid_name ← (( do (undefined_bool_at (← occLabel 572) ()) ) : SailM Bool )
  let questionMark := mode
  let valid_name : Bool :=
    if ((questionMark == M32_Monitor) : Bool)
    then (HaveAArch32EL EL3)
    else
      (if ((questionMark == M32_Hyp) : Bool)
      then (HaveAArch32EL EL2)
      else
        (if ((questionMark == M32_FIQ) : Bool)
        then (HaveAArch32EL EL1)
        else
          (if ((questionMark == M32_IRQ) : Bool)
          then (HaveAArch32EL EL1)
          else
            (if ((questionMark == M32_Svc) : Bool)
            then (HaveAArch32EL EL1)
            else
              (if ((questionMark == M32_Abort) : Bool)
              then (HaveAArch32EL EL1)
              else
                (if ((questionMark == M32_Undef) : Bool)
                then (HaveAArch32EL EL1)
                else
                  (if ((questionMark == M32_System) : Bool)
                  then (HaveAArch32EL EL1)
                  else
                    (if ((questionMark == M32_User) : Bool)
                    then (HaveAArch32EL EL0)
                    else false))))))))
  let valid_name := valid_name
  (pure ((! valid_name)))


/-- Type quantifiers: n : Nat, n ≥ 0 ∧ n ≤ 15 -/
def LookUpRIndex (n : Nat) (mode : (BitVec 5)) : SailM Int := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 14)) "sail-arm/v8_base.sail:6344.27-6344.28"
  match n with
  | 8 =>
    (do
      (RBankSelect mode 8 24 8 8 8 8 8))
  | 9 =>
    (do
      (RBankSelect mode 9 25 9 9 9 9 9))
  | 10 =>
    (do
      (RBankSelect mode 10 26 10 10 10 10 10))
  | 11 =>
    (do
      (RBankSelect mode 11 27 11 11 11 11 11))
  | 12 =>
    (do
      (RBankSelect mode 12 28 12 12 12 12 12))
  | 13 =>
    (do
      (RBankSelect mode 13 29 17 19 21 23 15))
  | 14 =>
    (do
      (RBankSelect mode 14 30 16 18 20 22 14))
  | _ => (pure (n))


def HaveBRBExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_BRBE)


def HaveStatisticalProfiling (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SPE)


/-- Type quantifiers: x : Int -/
def IsPow2 (x : Int) : SailM Bool := do
  if ((x ≤b 0) : Bool)
  then (pure (false))
  else
    (do
      let w__0 ← (( do (FloorPow2 x) ) : SailM Nat )
      let w__1 ← (( do (CeilPow2 x) ) : SailM Nat )
      (pure ((w__0 == w__1))))


def HaveSME (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SME)


def HaveGCS (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_GCS)


def HaveSVE (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SVE)


/-- Type quantifiers: n : Int, width : Nat, List.elem width [32, 64] -/
def X_set (n : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:7435.27-7435.28"
  ArmFull.assert ((width == 32) || (width == 64)) "sail-arm/v8_base.sail:7436.36-7436.37"
  if ((n != 31) : Bool)
  then
    (do
      (set_R (Sail.Int.toNatChecked (n)) (Sail.BitVec.zeroExtend value_name 64)))
  else (pure (()))


def HaveBTIExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_BTI)


def HaveDITExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_DIT)


def HaveFeatNMI (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_NMI)


def HaveMTEExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MTE)


def HavePANExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PAN)


def HaveSSBSExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SSBS)


def HaveUAOExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_UAO)


def HaveDoubleLock (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_DoubleLock)


def HavePMUv3p9 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMUv3p9)


def IsHighestEL (el : (BitVec 2)) : Bool :=
  ((HighestEL ()) == el)


def HavePFAR (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PFAR)


def ELR_set__1 (value_name : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  ArmFull.assert (w__0.EL != EL0) "sail-arm/v8_base.sail:9418.27-9418.28"
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  (ELR_set w__1.EL value_name)


def HaveDoubleFaultExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_DoubleFault)


def HaveIESB (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_IESB)


def HaveExtendedECDebugEvents (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_Debugv8p2)


def Havev8p8Debug (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_Debugv8p8)


def HaveNV2Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_NV2)


def HaveNVExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_NV)


def IRQPending (_ : Unit) : SailM (Bool × Bool) := do
  let w__0 ← (( do (__GIC_InterruptPending ()) ) : SailM Bool )
  (pure ((w__0, false)))


def HaveFeatWFxT (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_WFxT)


def HaveTWEDExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_TWED)


end ArmFull.Functions
