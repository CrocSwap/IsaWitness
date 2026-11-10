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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6712) 64) ) : SailM (BitVec 64) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6713)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
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
        (pure ((base, src))))
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
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__6 : (BitVec VL))
        (pure ((base, src)))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__7 : Bool)
        then
          (do
            let eoff : Int := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
            (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6714) 64) ) : SailM (BitVec 64) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6715)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
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
        (pure ((base, src))))
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
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__6 : (BitVec VL))
        (pure ((base, src)))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__7 : Bool)
        then
          (do
            let eoff : Int := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
            (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6716) 64) ) : SailM (BitVec 64) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6717)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, src) ← (( do
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
        (pure ((base, src))))
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
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
        let src := (w__6 : (BitVec VL))
        (pure ((base, src)))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__7 : Bool)
        then
          (do
            let eoff : Int := ((offset *i elements) +i e)
            let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
            let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) : SailM
              (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
            (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST2B_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6718) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6719)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 2 w__0) ) : SailM (Vector (BitVec VL) 2) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__1 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__1) : Bool)
    then
      (do
        let w__3 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure (base)))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64))) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := values_name
      for r in [loop_r_lower:loop_r_upper:1]i do
        let values_name := loop_vars
        loop_vars ← do
          let w__7 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((t +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let values_name :=
            ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__7) : (Vector (BitVec VL) 2))
          (pure (values_name))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_r_lower : Nat := 0
        let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
        (do
          let mut loop_vars_1 := ()
          for r in [loop_r_lower:loop_r_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  let eoff : Int := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                  let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                  let w__9 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read
                      (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize)) ) :
                    SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                  (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
              else (pure (()))
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST2H_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6720) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6721)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 2 w__0) ) : SailM (Vector (BitVec VL) 2) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__1 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__1) : Bool)
    then
      (do
        let w__3 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure (base)))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64))) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := values_name
      for r in [loop_r_lower:loop_r_upper:1]i do
        let values_name := loop_vars
        loop_vars ← do
          let w__7 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((t +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let values_name :=
            ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__7) : (Vector (BitVec VL) 2))
          (pure (values_name))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_r_lower : Nat := 0
        let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
        (do
          let mut loop_vars_1 := ()
          for r in [loop_r_lower:loop_r_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  let eoff : Int := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                  let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                  let w__9 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read
                      (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize)) ) :
                    SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                  (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
              else (pure (()))
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST2W_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6722) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6723)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 2 w__0) ) : SailM (Vector (BitVec VL) 2) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__1 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__1) : Bool)
    then
      (do
        let w__3 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure (base)))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64))) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := values_name
      for r in [loop_r_lower:loop_r_upper:1]i do
        let values_name := loop_vars
        loop_vars ← do
          let w__7 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((t +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let values_name :=
            ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__7) : (Vector (BitVec VL) 2))
          (pure (values_name))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_r_lower : Nat := 0
        let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
        (do
          let mut loop_vars_1 := ()
          for r in [loop_r_lower:loop_r_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  let eoff : Int := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                  let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                  let w__9 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read
                      (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize)) ) :
                    SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                  (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
              else (pure (()))
          (pure loop_vars_1))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_ST2D_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6724) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6725)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 2 w__0) ) : SailM (Vector (BitVec VL) 2) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__1 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__1) : Bool)
    then
      (do
        let w__3 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure (base)))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64))) ) : SailM (BitVec 64) )
  let values_name ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := values_name
      for r in [loop_r_lower:loop_r_upper:1]i do
        let values_name := loop_vars
        loop_vars ← do
          let w__7 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((t +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let values_name :=
            ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__7) : (Vector (BitVec VL) 2))
          (pure (values_name))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 2) )
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let loop_r_lower : Nat := 0
        let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
        (do
          let mut loop_vars_1 := ()
          for r in [loop_r_lower:loop_r_upper:1]i do
            let () := loop_vars_1
            loop_vars_1 ← do
              let w__8 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  let eoff : Int := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                  let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                  let w__9 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read
                      (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize)) ) :
                    SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                  (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
              else (pure (()))
          (pure loop_vars_1))
    (pure loop_vars))


end ArmFull.Functions
