import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0034
import ArmFull.Fn.M0051
import ArmFull.Fn.M0118
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0218
import ArmFull.Fn.M0238
import ArmFull.Fn.M0257
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M1142

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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 8 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ (is_VL VL) -/
def execute_ST1B_Z_P_BR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6550) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6551) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6552)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset, src))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__9
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 16 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [8, 16, 32, 64] ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6553) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6554) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6555)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset, src))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            ArmFull.assert ((0 ≤b (msize -i 1)) && ((msize -i 1) <b esize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64_sve.sail:81433.70-81433.71"
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__9
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 32 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6556) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6557) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6558)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset, src))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__9
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 64 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BR__ (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6559) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6560) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6561)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset, src))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__9
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 32 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BR_U128 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6562) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6563) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6564)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset, src))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__9
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 64 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BR_U128 (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6565) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6566) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6567)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset, src))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__9
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6570) 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6571) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6572)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset, src))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
            (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6573) 64) ) : SailM (BitVec 64) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6574) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6575)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset, src))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__8 : Bool)
        then
          (do
            let addr : (BitVec 64) := (BitVec.addInt base (((BitVec.toNat offset) +i e) *i mbytes))
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
            (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
        else (pure (()))
    (pure loop_vars))


end ArmFull.Functions
