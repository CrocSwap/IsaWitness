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
import ArmFull.Fn.M0202
import ArmFull.Fn.M0218
import ArmFull.Fn.M0238
import ArmFull.Fn.M0257
import ArmFull.Fn.M0582
import ArmFull.Fn.M1142
import ArmFull.Fn.M1164

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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg :
  Nat, tstride : Nat, tstride = 8 ∧
  0 ≤ t__arg ∧
  t__arg ≤ 31 ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7203) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7204)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
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
  let (src, t) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (src, t)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (src, t) := loop_vars
        loop_vars ← do
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
          let src := (w__6 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__7 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__7 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
                else (pure (()))
            (pure loop_vars_1))
          let t : Int := (t +i tstride)
          (pure ((src, t)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg :
  Nat, tstride : Nat, tstride = 8 ∧
  0 ≤ t__arg ∧
  t__arg ≤ 31 ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZx_P_BI_2x8 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7205) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7206)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
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
  let (src, t) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (src, t)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (src, t) := loop_vars
        loop_vars ← do
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
          let src := (w__6 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__7 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__7 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
                else (pure (()))
            (pure loop_vars_1))
          let t : Int := (t +i tstride)
          (pure ((src, t)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg :
  Nat, tstride : Nat, tstride = 4 ∧
  0 ≤ t__arg ∧
  t__arg ≤ 31 ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_STNT1B_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7207) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7208)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
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
  let (src, t) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (src, t)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (src, t) := loop_vars
        loop_vars ← do
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
          let src := (w__6 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__7 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__7 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
                else (pure (()))
            (pure loop_vars_1))
          let t : Int := (t +i tstride)
          (pure ((src, t)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg :
  Nat, tstride : Nat, tstride = 4 ∧
  0 ≤ t__arg ∧
  t__arg ≤ 31 ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 16 ∧ (is_VL VL) -/
def execute_STNT1H_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7209) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7210)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
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
  let (src, t) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (src, t)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (src, t) := loop_vars
        loop_vars ← do
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
          let src := (w__6 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__7 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__7 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
                else (pure (()))
            (pure loop_vars_1))
          let t : Int := (t +i tstride)
          (pure ((src, t)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg :
  Nat, tstride : Nat, tstride = 4 ∧
  0 ≤ t__arg ∧
  t__arg ≤ 31 ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 32 ∧ (is_VL VL) -/
def execute_STNT1W_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7211) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7212)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
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
  let (src, t) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (src, t)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (src, t) := loop_vars
        loop_vars ← do
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
          let src := (w__6 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__7 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__7 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
                else (pure (()))
            (pure loop_vars_1))
          let t : Int := (t +i tstride)
          (pure ((src, t)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, nreg : Nat, offset : Int, t__arg :
  Nat, tstride : Nat, tstride = 4 ∧
  0 ≤ t__arg ∧
  t__arg ≤ 31 ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 64 ∧ (is_VL VL) -/
def execute_STNT1D_MZx_P_BI_4x4 (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) (nreg : Nat) (offset : Int) (t__arg : Nat) (tstride : Nat) : SailM Unit := do
  let t : Int := t__arg
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7213) 64) ) : SailM (BitVec 64) )
  let src ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7214)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i nreg))))) ) : SailM
    (BitVec ((Sail.Int.toNatChecked PL) * nreg)) )
  let contiguous : Bool := true
  let nontemporal : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
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
  let (src, t) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (src, t)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (src, t) := loop_vars
        loop_vars ← do
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
          let src := (w__6 : (BitVec VL))
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := ()
            for e in [loop_e_lower:loop_e_upper:1]i do
              let () := loop_vars_1
              loop_vars_1 ← do
                let w__7 ← (( do (ActivePredicateElement mask ((r *i elements) +i e) esize) ) :
                  SailM Bool )
                if (w__7 : Bool)
                then
                  (do
                    let addr : (BitVec 64) :=
                      (BitVec.addInt base
                        (((((offset *i nreg) *i elements) +i (r *i elements)) +i e) *i mbytes))
                    let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read src e esize)) ) :
                      SailM (BitVec ((Sail.Int.toNatChecked mbytes) * 8)) )
                    (Mem_set addr mbytes accdesc (Sail.BitVec.castWidth w__8)))
                else (pure (()))
            (pure loop_vars_1))
          let t : Int := (t +i tstride)
          (pure ((src, t)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


def decode_BFMLAL_ZA_ZZV_1 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 5)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat (0#1 +++ Zm))
  let offset : Int := (BitVec.toNat (off3 +++ 0#1))
  let sub_op : Bool := false
  let nreg : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_BFMLAL_ZA_ZZV_1 128 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFMLAL_ZA_ZZV_1 256 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFMLAL_ZA_ZZV_1 512 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFMLAL_ZA_ZZV_1 1024 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFMLAL_ZA_ZZV_1 2048 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFMLAL_ZA_ZZW_2x2 (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let sub_op : Bool := false
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFMLAL_ZA_ZZW_2x2 128 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFMLAL_ZA_ZZW_2x2 256 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFMLAL_ZA_ZZW_2x2 512 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFMLAL_ZA_ZZW_2x2 1024 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFMLAL_ZA_ZZW_2x2 2048 (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) sub_op (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


end ArmFull.Functions
