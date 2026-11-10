import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0238
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n
  : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 32 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1SW_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6792)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6793) 64) ) : SailM (BitVec 64) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6794)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6795)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        (pure ((base, offset))))
    else (pure ((base, offset))) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
  let base := base
  let (data, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, result) := loop_vars
        loop_vars ← do
          let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
                (BitVec esize) )
              let addr : (BitVec 64) :=
                ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend w__4 64)) + offset)
              let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (msize / 8 * 8)) )
              let data := ((Sail.BitVec.castWidth w__5) : (BitVec msize))
              let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) :
                SailM (BitVec esize) )
              let w__7 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__6)) ) : SailM
                (BitVec VL) )
              let result := (w__7 : (BitVec VL))
              (pure ((data, result))))
          else
            (do
              let w__8 ← (( do
                (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM
                (BitVec VL) )
              let result := (w__8 : (BitVec VL))
              (pure ((data, result))))
      (pure loop_vars)) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 8 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1B_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6796)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6797) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6798)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__3 : (BitVec VL))
        (pure ((base, offset, src))))
    else (pure ((base, offset, src))) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend w__5 64)) + offset)
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__6
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 16 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1H_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6799)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6800) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6801)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__3 : (BitVec VL))
        (pure ((base, offset, src))))
    else (pure ((base, offset, src))) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend w__5 64)) + offset)
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__6
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 32 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_Z_P_AR_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6802)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6803) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6804)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__3 : (BitVec VL))
        (pure ((base, offset, src))))
    else (pure ((base, offset, src))) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend w__5 64)) + offset)
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__6
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 8 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1B_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6805)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6806) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6807)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__3 : (BitVec VL))
        (pure ((base, offset, src))))
    else (pure ((base, offset, src))) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend w__5 64)) + offset)
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__6
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 16 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1H_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6808)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6809) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6810)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__3 : (BitVec VL))
        (pure ((base, offset, src))))
    else (pure ((base, offset, src))) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend w__5 64)) + offset)
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__6
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, t : Nat, 0 ≤
  t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 32 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1W_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6811)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6812) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6813)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__3 : (BitVec VL))
        (pure ((base, offset, src))))
    else (pure ((base, offset, src))) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend w__5 64)) + offset)
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__6
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
def execute_STNT1D_Z_P_AR_D_64_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6814)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6815) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6816)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := true
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__3 : (BitVec VL))
        (pure ((base, offset, src))))
    else (pure ((base, offset, src))) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              ((Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend w__5 64)) + offset)
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__6
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_LD1Q_Z_P_AR_D_64_unscaled (VL : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  (CheckNonStreamingSVEEnabled ())
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6817)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6818) 64) ) : SailM (BitVec 64) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6819)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask 128) ) : SailM Bool )
  let (base, offset) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        (pure ((base, offset))))
    else (pure ((base, offset))) ) : SailM ((BitVec VL) × (BitVec 64)) )
  let offset := offset
  let base := base
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__3 ← (( do (ActivePredicateElement mask e 128) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let w__4 ← (( do (Elem_read base (2 *i e) 64) ) : SailM (BitVec 64) )
              let addr : (BitVec 64) := (w__4 + offset)
              let w__5 ← (( do (Mem_read addr 16 accdesc) ) : SailM (BitVec (16 * 8)) )
              (Elem_set result e 128 w__5))
          else
            (do
              (Elem_set result e 128 (Zeros (n := 128))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) -/
def execute_ST1Q_Z_P_AR_D_64_unscaled (VL : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  (CheckNonStreamingSVEEnabled ())
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6820)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6821) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6822)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask 128) ) : SailM Bool )
  let (base, offset, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__2 : (BitVec 64))
        let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__3 : (BitVec VL))
        (pure ((base, offset, src))))
    else (pure ((base, offset, src))) ) : SailM ((BitVec VL) × (BitVec 64) × (BitVec VL)) )
  let src := src
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__4 ← (( do (ActivePredicateElement mask e 128) ) : SailM Bool )
        if (w__4 : Bool)
        then
          (do
            let w__5 ← (( do (Elem_read base (2 *i e) 64) ) : SailM (BitVec 64) )
            let addr : (BitVec 64) := (w__5 + offset)
            let w__6 ← (( do (Elem_read src e 128) ) : SailM (BitVec (16 * 8)) )
            (Mem_set addr 16 accdesc w__6))
        else (pure (()))
    (pure loop_vars))


end ArmFull.Functions
