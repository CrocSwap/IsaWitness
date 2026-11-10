import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0034
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0118
import ArmFull.Fn.M0120
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0227
import ArmFull.Fn.M0238
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
import ArmFull.Fn.M1072

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
  : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LDNF1SB_Z_P_BI_S32 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6227) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6228)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let orig ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6229)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, fault, faulted, result, unknown)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, fault, faulted, result, unknown) := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let (data, fault) ← (( do
            if (w__6 : Bool)
            then
              (do
                let eoff : Int := ((offset *i elements) +i e)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                let w__7 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemNF_read addr mbytes
                    accdesc)) ) : SailM ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool) )
                let (tup__0, tup__1) :=
                  (w__7 : ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool))
                let data : (BitVec msize) := (Sail.BitVec.castWidth tup__0)
                let fault : Bool := tup__1
                (pure ((data, fault))))
            else
              (let (tup__0, tup__1) :=
                (((Sail.BitVec.castWidth (Zeros (n := msize))), false) : ((BitVec msize) × Bool))
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure ((data, fault)))) ) : SailM ((BitVec msize) × Bool) )
          let faulted : Bool := (faulted || fault)
          if (faulted : Bool)
          then
            (do
              (ElemFFR_set e esize 0#1))
          else (pure (()))
          let w__9 ← (( do
            if ((unknown : Bool) : Bool)
            then (pure true)
            else
              (do
                let w__8 ← (( do (ElemFFR_read e esize) ) : SailM (BitVec 1) )
                (pure (((w__8 == 0#1) : Bool)))) ) : SailM Bool )
          let unknown := (w__9 : Bool)
          let result ← (( do
            if (unknown : Bool)
            then
              (do
                let w__11 ← (( do
                  if (((! fault) : Bool) : Bool)
                  then
                    (do
                      (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA))
                  else (pure false) ) : SailM Bool )
                if (w__11 : Bool)
                then
                  (do
                    let w__12 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) : SailM
                      (BitVec esize) )
                    (Elem_set result e esize (Sail.BitVec.castWidth w__12)))
                else
                  (do
                    let w__14 ← (( do (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO) ) :
                      SailM Bool )
                    if (w__14 : Bool)
                    then
                      (do
                        (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))))
                    else
                      (do
                        let w__16 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read orig e esize))
                          ) : SailM (BitVec esize) )
                        (Elem_set result e esize (Sail.BitVec.castWidth w__16)))))
            else
              (do
                let w__18 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) )
                  : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__18))) ) : SailM (BitVec VL) )
          (pure ((data, fault, faulted, result, unknown)))
      (pure loop_vars)) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNF1SB_Z_P_BI_S16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6230) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6231)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let orig ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6232)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, fault, faulted, result, unknown)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, fault, faulted, result, unknown) := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let (data, fault) ← (( do
            if (w__6 : Bool)
            then
              (do
                let eoff : Int := ((offset *i elements) +i e)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                let w__7 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemNF_read addr mbytes
                    accdesc)) ) : SailM ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool) )
                let (tup__0, tup__1) :=
                  (w__7 : ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool))
                let data : (BitVec msize) := (Sail.BitVec.castWidth tup__0)
                let fault : Bool := tup__1
                (pure ((data, fault))))
            else
              (let (tup__0, tup__1) :=
                (((Sail.BitVec.castWidth (Zeros (n := msize))), false) : ((BitVec msize) × Bool))
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure ((data, fault)))) ) : SailM ((BitVec msize) × Bool) )
          let faulted : Bool := (faulted || fault)
          if (faulted : Bool)
          then
            (do
              (ElemFFR_set e esize 0#1))
          else (pure (()))
          let w__9 ← (( do
            if ((unknown : Bool) : Bool)
            then (pure true)
            else
              (do
                let w__8 ← (( do (ElemFFR_read e esize) ) : SailM (BitVec 1) )
                (pure (((w__8 == 0#1) : Bool)))) ) : SailM Bool )
          let unknown := (w__9 : Bool)
          let result ← (( do
            if (unknown : Bool)
            then
              (do
                let w__11 ← (( do
                  if (((! fault) : Bool) : Bool)
                  then
                    (do
                      (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA))
                  else (pure false) ) : SailM Bool )
                if (w__11 : Bool)
                then
                  (do
                    let w__12 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) : SailM
                      (BitVec esize) )
                    (Elem_set result e esize (Sail.BitVec.castWidth w__12)))
                else
                  (do
                    let w__14 ← (( do (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO) ) :
                      SailM Bool )
                    if (w__14 : Bool)
                    then
                      (do
                        (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))))
                    else
                      (do
                        let w__16 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read orig e esize))
                          ) : SailM (BitVec esize) )
                        (Elem_set result e esize (Sail.BitVec.castWidth w__16)))))
            else
              (do
                let w__18 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) )
                  : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__18))) ) : SailM (BitVec VL) )
          (pure ((data, fault, faulted, result, unknown)))
      (pure loop_vars)) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 64 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LDNF1D_Z_P_BI_U64 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6233) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6234)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let orig ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6235)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
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
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, fault, faulted, result, unknown)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, fault, faulted, result, unknown) := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let (data, fault) ← (( do
            if (w__6 : Bool)
            then
              (do
                let eoff : Int := ((offset *i elements) +i e)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                let w__7 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemNF_read addr mbytes
                    accdesc)) ) : SailM ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool) )
                let (tup__0, tup__1) :=
                  (w__7 : ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool))
                let data : (BitVec msize) := (Sail.BitVec.castWidth tup__0)
                let fault : Bool := tup__1
                (pure ((data, fault))))
            else
              (let (tup__0, tup__1) :=
                (((Sail.BitVec.castWidth (Zeros (n := msize))), false) : ((BitVec msize) × Bool))
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure ((data, fault)))) ) : SailM ((BitVec msize) × Bool) )
          let faulted : Bool := (faulted || fault)
          if (faulted : Bool)
          then
            (do
              (ElemFFR_set e esize 0#1))
          else (pure (()))
          let w__9 ← (( do
            if ((unknown : Bool) : Bool)
            then (pure true)
            else
              (do
                let w__8 ← (( do (ElemFFR_read e esize) ) : SailM (BitVec 1) )
                (pure (((w__8 == 0#1) : Bool)))) ) : SailM Bool )
          let unknown := (w__9 : Bool)
          let result ← (( do
            if (unknown : Bool)
            then
              (do
                let w__11 ← (( do
                  if (((! fault) : Bool) : Bool)
                  then
                    (do
                      (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA))
                  else (pure false) ) : SailM Bool )
                if (w__11 : Bool)
                then
                  (do
                    let w__12 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) : SailM
                      (BitVec esize) )
                    (Elem_set result e esize (Sail.BitVec.castWidth w__12)))
                else
                  (do
                    let w__14 ← (( do (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO) ) :
                      SailM Bool )
                    if (w__14 : Bool)
                    then
                      (do
                        (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))))
                    else
                      (do
                        let w__16 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read orig e esize))
                          ) : SailM (BitVec esize) )
                        (Elem_set result e esize (Sail.BitVec.castWidth w__16)))))
            else
              (do
                let w__18 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) )
                  : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__18))) ) : SailM (BitVec VL) )
          (pure ((data, fault, faulted, result, unknown)))
      (pure loop_vars)) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, imm : Int, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_STR_P_BI__ (VL : Nat) (imm : Int) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Int := (Int.ediv PL 8)
  let base ← (( do (undefined_bitvector_at (← occLabel 6568) 64) ) : SailM (BitVec 64) )
  let offset : Int := (imm *i elements)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do ((Sail.BitVec.castWidth ) <$> (P_read t PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base offset) 2)
  let w__3 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AlignmentEnforced ()))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let w__4 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort (BitVec.addInt base offset) w__4))
  else (pure (()))
  let offset ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := offset
      for e in [loop_e_lower:loop_e_upper:1]i do
        let offset := loop_vars
        loop_vars ← do
          let offset : Int := offset
          let w__5 ← (( do (Elem_read src e 8) ) : SailM (BitVec (1 * 8)) )
          (AArch64_MemSingle_set (BitVec.addInt base offset) 1 accdesc aligned w__5)
          let offset : Int := (offset +i 1)
          (pure (offset))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, imm : Int, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_STR_Z_BI__ (VL : Nat) (imm : Int) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6569) 64) ) : SailM (BitVec 64) )
  let offset : Int := (imm *i elements)
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let src ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base offset) 16)
  let w__3 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AlignmentEnforced ()))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let w__4 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort (BitVec.addInt base offset) w__4))
  else (pure (()))
  let offset ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := offset
      for e in [loop_e_lower:loop_e_upper:1]i do
        let offset := loop_vars
        loop_vars ← do
          let offset : Int := offset
          let w__5 ← (( do (Elem_read src e 8) ) : SailM (BitVec (1 * 8)) )
          (AArch64_MemSingle_set (BitVec.addInt base offset) 1 accdesc aligned w__5)
          let offset : Int := (offset +i 1)
          (pure (offset))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6983)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize))
                  ) : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 col esize))
                  ) : SailM (BitVec esize) )
                let element3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then
                        (do
                          (FPNeg element1))
                      else (pure (element1)) ) : SailM (BitVec esize) )
                    let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (FPMulAdd_ZA element3 element1 element2 w__4) ) : SailM
                      (BitVec esize) )
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth w__5)))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


end ArmFull.Functions
