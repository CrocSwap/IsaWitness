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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 3 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD3Q_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6276) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6277)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 3 w__0) ) : SailM (Vector (BitVec VL) 3) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
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
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := values_name
      for e in [loop_e_lower:loop_e_upper:1]i do
        let values_name := loop_vars
        loop_vars ← do
          let loop_r_lower : Nat := 0
          let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
          (do
            let mut loop_vars_1 := values_name
            for r in [loop_r_lower:loop_r_upper:1]i do
              let values_name := loop_vars_1
              loop_vars_1 ← do
                let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
                if (w__7 : Bool)
                then
                  (do
                    let eoff : Int := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                    let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                    let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc))
                      ) : SailM (BitVec (esize / 8 * 8)) )
                    let w__9 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__8)) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__9) : (Vector (BitVec VL) 3))
                    (pure (values_name)))
                else
                  (do
                    let w__10 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__10) : (Vector (BitVec VL) 3))
                    (pure (values_name)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 3) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (Nat.mod (Sail.Int.toNatChecked ((t +i r))) 32) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t : Nat, 0
  ≤ t ∧
  t ≤ 31 ∧
  nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ (is_VL VL) -/
def execute_LD4Q_Z_P_BI_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6278) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6279)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let values_name ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
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
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := values_name
      for e in [loop_e_lower:loop_e_upper:1]i do
        let values_name := loop_vars
        loop_vars ← do
          let loop_r_lower : Nat := 0
          let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
          (do
            let mut loop_vars_1 := values_name
            for r in [loop_r_lower:loop_r_upper:1]i do
              let values_name := loop_vars_1
              loop_vars_1 ← do
                let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
                if (w__7 : Bool)
                then
                  (do
                    let eoff : Int := ((((offset *i elements) *i nreg) +i (e *i nreg)) +i r)
                    let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                    let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc))
                      ) : SailM (BitVec (esize / 8 * 8)) )
                    let w__9 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth w__8)) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__9) : (Vector (BitVec VL) 4))
                    (pure (values_name)))
                else
                  (do
                    let w__10 ← (( do
                      (Elem_set (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r))) e esize
                        (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM (BitVec VL) )
                    let values_name :=
                      ((vectorUpdate values_name (Sail.Int.toNatChecked (r)) w__10) : (Vector (BitVec VL) 4))
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
        (Z_set (Nat.mod (Sail.Int.toNatChecked ((t +i r))) 32) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! values_name (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1RQB_Z_P_BI_U8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6280) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6281) 128) ) : SailM (BitVec 128) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
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
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              let addr : (BitVec 64) :=
                (BitVec.addInt (BitVec.addInt base (offset *i 16)) (e *i mbytes))
              let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__7))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Z_set t VL
    (Sail.BitVec.castWidth (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 128))))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1RQH_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6282) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6283) 128) ) : SailM (BitVec 128) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
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
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              let addr : (BitVec 64) :=
                (BitVec.addInt (BitVec.addInt base (offset *i 16)) (e *i mbytes))
              let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__7))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Z_set t VL
    (Sail.BitVec.castWidth (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 128))))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RQW_Z_P_BI_U32 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6284) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6285) 128) ) : SailM (BitVec 128) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
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
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              let addr : (BitVec 64) :=
                (BitVec.addInt (BitVec.addInt base (offset *i 16)) (e *i mbytes))
              let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__7))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Z_set t VL
    (Sail.BitVec.castWidth (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 128))))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RQD_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6286) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6287) 128) ) : SailM (BitVec 128) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
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
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              let addr : (BitVec 64) :=
                (BitVec.addInt (BitVec.addInt base (offset *i 16)) (e *i mbytes))
              let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__7))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Z_set t VL
    (Sail.BitVec.castWidth (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 128))))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1ROB_Z_P_BI_U8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  if ((VL <b 256) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 256 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6288) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6289) 256) ) : SailM (BitVec 256) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
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
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              let eoff : Int := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__7))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 256) )
  (Z_set t VL
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
      (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 256)))) VL)))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, offset : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1ROH_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (offset : Int) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  if ((VL <b 256) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 256 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6290) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6291) 256) ) : SailM (BitVec 256) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
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
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__6 : Bool)
          then
            (do
              let eoff : Int := ((offset *i elements) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__7 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__7))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 256) )
  (Z_set t VL
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
      (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 256)))) VL)))


end ArmFull.Functions
