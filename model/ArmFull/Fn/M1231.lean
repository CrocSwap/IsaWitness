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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned
  : Bool, scale : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  scale = 1 ∧
  offs_size = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 16 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6675) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6676)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6677)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
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
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__6 : (BitVec VL))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
              (BitVec esize) )
            let off ← (( do
              (asl_Int (Sail.BitVec.extractLsb w__9 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                offs_unsigned) ) : SailM Int )
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
            let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__10
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned
  : Bool, scale : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  scale = 2 ∧
  offs_size = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 32 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6678) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6679)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6680)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
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
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__6 : (BitVec VL))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
              (BitVec esize) )
            let off ← (( do
              (asl_Int (Sail.BitVec.extractLsb w__9 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                offs_unsigned) ) : SailM Int )
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
            let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__10
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, msize : Nat, n : Nat, offs_size : Nat, k_offs_unsigned
  : Bool, scale : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  scale = 3 ∧
  offs_size = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 64 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_BZ_D_64_scaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6681) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6682)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6683)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
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
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__6 : (BitVec VL))
        let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__7 : (BitVec VL))
        (pure ((base, offset, src)))) ) : SailM ((BitVec 64) × (BitVec VL) × (BitVec VL)) )
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
            let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
              (BitVec esize) )
            let off ← (( do
              (asl_Int (Sail.BitVec.extractLsb w__9 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                offs_unsigned) ) : SailM Int )
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
            let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__10
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1B_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6684)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6685)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__2 : (BitVec VL))
        (pure ((base, src))))
    else (pure ((base, src))) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              (BitVec.addInt (Sail.BitVec.zeroExtend w__4 64) (offset *i mbytes))
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__5
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6686)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6687)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__2 : (BitVec VL))
        (pure ((base, src))))
    else (pure ((base, src))) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              (BitVec.addInt (Sail.BitVec.zeroExtend w__4 64) (offset *i mbytes))
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__5
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1W_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6688)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6689)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__2 : (BitVec VL))
        (pure ((base, src))))
    else (pure ((base, src))) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              (BitVec.addInt (Sail.BitVec.zeroExtend w__4 64) (offset *i mbytes))
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__5
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST1D_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6690)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6691)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__2 : (BitVec VL))
        (pure ((base, src))))
    else (pure ((base, src))) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              (BitVec.addInt (Sail.BitVec.zeroExtend w__4 64) (offset *i mbytes))
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__5
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1B_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6692)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6693)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__2 : (BitVec VL))
        (pure ((base, src))))
    else (pure ((base, src))) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              (BitVec.addInt (Sail.BitVec.zeroExtend w__4 64) (offset *i mbytes))
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__5
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, msize : Nat, n : Nat, offset : Nat, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1H_Z_P_AI_S (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6694)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6695)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
        let base := (w__1 : (BitVec VL))
        let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__2 : (BitVec VL))
        (pure ((base, src))))
    else (pure ((base, src))) ) : SailM ((BitVec VL) × (BitVec VL)) )
  let src := src
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
              (BitVec esize) )
            let addr : (BitVec 64) :=
              (BitVec.addInt (Sail.BitVec.zeroExtend w__4 64) (offset *i mbytes))
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec esize) )
            (Mem_set addr mbytes accdesc
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__5
                (Sail.Int.toNatChecked ((msize -i 1))) 0))))
        else (pure (()))
    (pure loop_vars))


end ArmFull.Functions
