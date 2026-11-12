import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0034
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0120
import ArmFull.Fn.M0147
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0238
import ArmFull.Fn.M0852
import ArmFull.Fn.M1072
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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 16 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SH_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6425)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6426)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let orig ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6427)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVEFF contiguous tagchecked) ) : SailM AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure (base)) ) : SailM (BitVec VL) )
  let base := base
  ArmFull.assert accdesc.first "sail-arm/instrs64_sve.sail:77868.24-77868.25"
  let (accdesc, data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (accdesc, data, fault, faulted, result, unknown)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (accdesc, data, fault, faulted, result, unknown) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let (accdesc, data, fault) ← (( do
            if (w__2 : Bool)
            then
              (do
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
                  (BitVec esize) )
                let addr : (BitVec 64) :=
                  (BitVec.addInt (Sail.BitVec.zeroExtend w__3 64) (offset *i mbytes))
                if (accdesc.first : Bool)
                then
                  (do
                    let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc))
                      ) : SailM (BitVec (msize / 8 * 8)) )
                    let data := ((Sail.BitVec.castWidth w__4) : (BitVec msize))
                    let accdesc : AccessDescriptor := { accdesc with first := false }
                    (pure ((accdesc, data, fault))))
                else
                  (do
                    let w__5 ← (( do
                      ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemNF_read addr
                        mbytes accdesc)) ) : SailM
                      ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool) )
                    let (tup__0, tup__1) :=
                      (w__5 : ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool))
                    let data : (BitVec msize) := (Sail.BitVec.castWidth tup__0)
                    let fault : Bool := tup__1
                    (pure ((accdesc, data, fault)))))
            else
              (let (tup__0, tup__1) :=
                (((Sail.BitVec.castWidth (Zeros (n := msize))), false) : ((BitVec msize) × Bool))
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure ((accdesc, data, fault)))) ) : SailM
            (AccessDescriptor × (BitVec msize) × Bool) )
          let faulted : Bool := (faulted || fault)
          if (faulted : Bool)
          then
            (do
              (ElemFFR_set e esize 0#1))
          else (pure (()))
          let w__7 ← (( do
            if ((unknown : Bool) : Bool)
            then (pure true)
            else
              (do
                let w__6 ← (( do (ElemFFR_read e esize) ) : SailM (BitVec 1) )
                (pure (((w__6 == 0#1) : Bool)))) ) : SailM Bool )
          let unknown := (w__7 : Bool)
          let result ← (( do
            if (unknown : Bool)
            then
              (do
                let w__9 ← (( do
                  if (((! fault) : Bool) : Bool)
                  then
                    (do
                      (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA))
                  else (pure false) ) : SailM Bool )
                if (w__9 : Bool)
                then
                  (do
                    let w__10 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) : SailM
                      (BitVec esize) )
                    (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
                else
                  (do
                    let w__12 ← (( do (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO) ) :
                      SailM Bool )
                    if (w__12 : Bool)
                    then
                      (do
                        (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))))
                    else
                      (do
                        let w__14 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read orig e esize))
                          ) : SailM (BitVec esize) )
                        (Elem_set result e esize (Sail.BitVec.castWidth w__14)))))
            else
              (do
                let w__16 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) )
                  : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__16))) ) : SailM (BitVec VL) )
          (pure ((accdesc, data, fault, faulted, result, unknown)))
      (pure loop_vars)) ) : SailM
    (AccessDescriptor × (BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1W_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6428)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6429)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6430)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure (base)) ) : SailM (BitVec VL) )
  let base := base
  let (data, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
                (BitVec esize) )
              let addr : (BitVec 64) :=
                (BitVec.addInt (Sail.BitVec.zeroExtend w__3 64) (offset *i mbytes))
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (msize / 8 * 8)) )
              let data := ((Sail.BitVec.castWidth w__4) : (BitVec msize))
              let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) :
                SailM (BitVec esize) )
              let w__6 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__5)) ) : SailM
                (BitVec VL) )
              let result := (w__6 : (BitVec VL))
              (pure ((data, result))))
          else
            (do
              let w__7 ← (( do
                (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM
                (BitVec VL) )
              let result := (w__7 : (BitVec VL))
              (pure ((data, result))))
      (pure loop_vars)) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1SW_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6431)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6432)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6433)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure (base)) ) : SailM (BitVec VL) )
  let base := base
  let (data, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
                (BitVec esize) )
              let addr : (BitVec 64) :=
                (BitVec.addInt (Sail.BitVec.zeroExtend w__3 64) (offset *i mbytes))
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (msize / 8 * 8)) )
              let data := ((Sail.BitVec.castWidth w__4) : (BitVec msize))
              let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) :
                SailM (BitVec esize) )
              let w__6 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__5)) ) : SailM
                (BitVec VL) )
              let result := (w__6 : (BitVec VL))
              (pure ((data, result))))
          else
            (do
              let w__7 ← (( do
                (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM
                (BitVec VL) )
              let result := (w__7 : (BitVec VL))
              (pure ((data, result))))
      (pure loop_vars)) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1W_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6434)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6435)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let orig ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6436)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVEFF contiguous tagchecked) ) : SailM AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure (base)) ) : SailM (BitVec VL) )
  let base := base
  ArmFull.assert accdesc.first "sail-arm/instrs64_sve.sail:78132.24-78132.25"
  let (accdesc, data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (accdesc, data, fault, faulted, result, unknown)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (accdesc, data, fault, faulted, result, unknown) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let (accdesc, data, fault) ← (( do
            if (w__2 : Bool)
            then
              (do
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
                  (BitVec esize) )
                let addr : (BitVec 64) :=
                  (BitVec.addInt (Sail.BitVec.zeroExtend w__3 64) (offset *i mbytes))
                if (accdesc.first : Bool)
                then
                  (do
                    let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc))
                      ) : SailM (BitVec (msize / 8 * 8)) )
                    let data := ((Sail.BitVec.castWidth w__4) : (BitVec msize))
                    let accdesc : AccessDescriptor := { accdesc with first := false }
                    (pure ((accdesc, data, fault))))
                else
                  (do
                    let w__5 ← (( do
                      ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemNF_read addr
                        mbytes accdesc)) ) : SailM
                      ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool) )
                    let (tup__0, tup__1) :=
                      (w__5 : ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool))
                    let data : (BitVec msize) := (Sail.BitVec.castWidth tup__0)
                    let fault : Bool := tup__1
                    (pure ((accdesc, data, fault)))))
            else
              (let (tup__0, tup__1) :=
                (((Sail.BitVec.castWidth (Zeros (n := msize))), false) : ((BitVec msize) × Bool))
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure ((accdesc, data, fault)))) ) : SailM
            (AccessDescriptor × (BitVec msize) × Bool) )
          let faulted : Bool := (faulted || fault)
          if (faulted : Bool)
          then
            (do
              (ElemFFR_set e esize 0#1))
          else (pure (()))
          let w__7 ← (( do
            if ((unknown : Bool) : Bool)
            then (pure true)
            else
              (do
                let w__6 ← (( do (ElemFFR_read e esize) ) : SailM (BitVec 1) )
                (pure (((w__6 == 0#1) : Bool)))) ) : SailM Bool )
          let unknown := (w__7 : Bool)
          let result ← (( do
            if (unknown : Bool)
            then
              (do
                let w__9 ← (( do
                  if (((! fault) : Bool) : Bool)
                  then
                    (do
                      (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA))
                  else (pure false) ) : SailM Bool )
                if (w__9 : Bool)
                then
                  (do
                    let w__10 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) : SailM
                      (BitVec esize) )
                    (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
                else
                  (do
                    let w__12 ← (( do (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO) ) :
                      SailM Bool )
                    if (w__12 : Bool)
                    then
                      (do
                        (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))))
                    else
                      (do
                        let w__14 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read orig e esize))
                          ) : SailM (BitVec esize) )
                        (Elem_set result e esize (Sail.BitVec.castWidth w__14)))))
            else
              (do
                let w__16 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) )
                  : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__16))) ) : SailM (BitVec VL) )
          (pure ((accdesc, data, fault, faulted, result, unknown)))
      (pure loop_vars)) ) : SailM
    (AccessDescriptor × (BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 32 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDFF1SW_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6437)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6438)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let orig ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6439)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVEFF contiguous tagchecked) ) : SailM AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure (base)) ) : SailM (BitVec VL) )
  let base := base
  ArmFull.assert accdesc.first "sail-arm/instrs64_sve.sail:78236.24-78236.25"
  let (accdesc, data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (accdesc, data, fault, faulted, result, unknown)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (accdesc, data, fault, faulted, result, unknown) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let (accdesc, data, fault) ← (( do
            if (w__2 : Bool)
            then
              (do
                let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
                  (BitVec esize) )
                let addr : (BitVec 64) :=
                  (BitVec.addInt (Sail.BitVec.zeroExtend w__3 64) (offset *i mbytes))
                if (accdesc.first : Bool)
                then
                  (do
                    let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc))
                      ) : SailM (BitVec (msize / 8 * 8)) )
                    let data := ((Sail.BitVec.castWidth w__4) : (BitVec msize))
                    let accdesc : AccessDescriptor := { accdesc with first := false }
                    (pure ((accdesc, data, fault))))
                else
                  (do
                    let w__5 ← (( do
                      ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemNF_read addr
                        mbytes accdesc)) ) : SailM
                      ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool) )
                    let (tup__0, tup__1) :=
                      (w__5 : ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool))
                    let data : (BitVec msize) := (Sail.BitVec.castWidth tup__0)
                    let fault : Bool := tup__1
                    (pure ((accdesc, data, fault)))))
            else
              (let (tup__0, tup__1) :=
                (((Sail.BitVec.castWidth (Zeros (n := msize))), false) : ((BitVec msize) × Bool))
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure ((accdesc, data, fault)))) ) : SailM
            (AccessDescriptor × (BitVec msize) × Bool) )
          let faulted : Bool := (faulted || fault)
          if (faulted : Bool)
          then
            (do
              (ElemFFR_set e esize 0#1))
          else (pure (()))
          let w__7 ← (( do
            if ((unknown : Bool) : Bool)
            then (pure true)
            else
              (do
                let w__6 ← (( do (ElemFFR_read e esize) ) : SailM (BitVec 1) )
                (pure (((w__6 == 0#1) : Bool)))) ) : SailM Bool )
          let unknown := (w__7 : Bool)
          let result ← (( do
            if (unknown : Bool)
            then
              (do
                let w__9 ← (( do
                  if (((! fault) : Bool) : Bool)
                  then
                    (do
                      (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA))
                  else (pure false) ) : SailM Bool )
                if (w__9 : Bool)
                then
                  (do
                    let w__10 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) : SailM
                      (BitVec esize) )
                    (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
                else
                  (do
                    let w__12 ← (( do (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO) ) :
                      SailM Bool )
                    if (w__12 : Bool)
                    then
                      (do
                        (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))))
                    else
                      (do
                        let w__14 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read orig e esize))
                          ) : SailM (BitVec esize) )
                        (Elem_set result e esize (Sail.BitVec.castWidth w__14)))))
            else
              (do
                let w__16 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) )
                  : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__16))) ) : SailM (BitVec VL) )
          (pure ((accdesc, data, fault, faulted, result, unknown)))
      (pure loop_vars)) ) : SailM
    (AccessDescriptor × (BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1D_Z_P_AI_D (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6440)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6441)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6442)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure (base)) ) : SailM (BitVec VL) )
  let base := base
  let (data, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
                (BitVec esize) )
              let addr : (BitVec 64) :=
                (BitVec.addInt (Sail.BitVec.zeroExtend w__3 64) (offset *i mbytes))
              let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (msize / 8 * 8)) )
              let data := ((Sail.BitVec.castWidth w__4) : (BitVec msize))
              let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) :
                SailM (BitVec esize) )
              let w__6 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__5)) ) : SailM
                (BitVec VL) )
              let result := (w__6 : (BitVec VL))
              (pure ((data, result))))
          else
            (do
              let w__7 ← (( do
                (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM
                (BitVec VL) )
              let result := (w__7 : (BitVec VL))
              (pure ((data, result))))
      (pure loop_vars)) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
