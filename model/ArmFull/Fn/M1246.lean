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
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0238
import ArmFull.Fn.M0257
import ArmFull.Fn.M0582
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNT1H_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6945) 64) ) : SailM (BitVec 64) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let w__1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6946)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 4 w__1) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__2) : Bool)
    then
      (do
        let w__4 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__4 : Bool)
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
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := values_name
            for e in [loop_e_lower:loop_e_upper:1]i do
              let values_name := loop_vars_1
              loop_vars_1 ← do
                let w__8 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__8 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc))
                      ) : SailM (BitVec (esize / 8 * 8)) )
                    let w__10 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__9)) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__10) : (Vector (BitVec VL) 4))
                    (pure (values_name)))
                else
                  (do
                    let w__11 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__11) : (Vector (BitVec VL) 4))
                    (pure (values_name)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (t +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNT1W_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6947) 64) ) : SailM (BitVec 64) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let w__1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6948)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 4 w__1) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__2) : Bool)
    then
      (do
        let w__4 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__4 : Bool)
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
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := values_name
            for e in [loop_e_lower:loop_e_upper:1]i do
              let values_name := loop_vars_1
              loop_vars_1 ← do
                let w__8 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__8 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc))
                      ) : SailM (BitVec (esize / 8 * 8)) )
                    let w__10 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__9)) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__10) : (Vector (BitVec VL) 4))
                    (pure (values_name)))
                else
                  (do
                    let w__11 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__11) : (Vector (BitVec VL) 4))
                    (pure (values_name)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (t +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNT1D_MZ_P_BI_4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6949) 64) ) : SailM (BitVec 64) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let w__1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6950)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 4 w__1) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__2) : Bool)
    then
      (do
        let w__4 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__4 : Bool)
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
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := values_name
            for e in [loop_e_lower:loop_e_upper:1]i do
              let values_name := loop_vars_1
              loop_vars_1 ← do
                let w__8 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__8 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc))
                      ) : SailM (BitVec (esize / 8 * 8)) )
                    let w__10 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__9)) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__10) : (Vector (BitVec VL) 4))
                    (pure (values_name)))
                else
                  (do
                    let w__11 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__11) : (Vector (BitVec VL) 4))
                    (pure (values_name)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (t +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_ST1B_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6951) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6952)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
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
  let src ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := src
      for r in [loop_r_lower:loop_r_upper:1]i do
        let src := loop_vars
        loop_vars ← do
          let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (t +i r) VL)) ) : SailM
            (BitVec VL) )
          let src := (w__7 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__8 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__8 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
                else (pure (()))
            (pure loop_vars_1))
          (pure (src))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_ST1H_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6953) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6954)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
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
  let src ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := src
      for r in [loop_r_lower:loop_r_upper:1]i do
        let src := loop_vars
        loop_vars ← do
          let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (t +i r) VL)) ) : SailM
            (BitVec VL) )
          let src := (w__7 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__8 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__8 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
                else (pure (()))
            (pure loop_vars_1))
          (pure (src))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_ST1W_MZ_P_BI_2 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6955) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6956)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
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
  let src ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := src
      for r in [loop_r_lower:loop_r_upper:1]i do
        let src := loop_vars
        loop_vars ← do
          let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (t +i r) VL)) ) : SailM
            (BitVec VL) )
          let src := (w__7 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__8 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__8 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__9)))
                else (pure (()))
            (pure loop_vars_1))
          (pure (src))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (pure (()))


end ArmFull.Functions
