import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FTSSEL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5096)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7495.49-7495.50"
          let w__0 ← (( do (FPTrigSSel element1 element2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_sub_i : Bool, k_sub_r :
  Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FCADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (sub_i : Bool) (sub_r : Bool) : SailM Unit := do
  let acc_i ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5099)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let acc_r ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5100)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let elt2_i ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5101)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let elt2_r ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5102)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5103)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (acc_i, acc_r, elt2_i, elt2_r, result) ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := (acc_i, acc_r, elt2_i, elt2_r, result)
      for p in [loop_p_lower:loop_p_upper:1]i do
        let (acc_i, acc_r, elt2_i, elt2_r, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let acc_r := (w__2 : (BitVec esize))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let acc_i := (w__3 : (BitVec esize))
          let w__4 ← (( do (ActivePredicateElement mask ((2 *i p) +i 0) esize) ) : SailM Bool )
          let (acc_r, elt2_i) ← (( do
            if (w__4 : Bool)
            then
              (do
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i 1) esize)) ) :
                  SailM (BitVec esize) )
                let elt2_i := (w__5 : (BitVec esize))
                let elt2_i ← (( do
                  if (sub_i : Bool)
                  then
                    (do
                      ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7694.57-7694.58"
                      (FPNeg elt2_i))
                  else (pure (elt2_i)) ) : SailM (BitVec esize) )
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7697.53-7697.54"
                let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__8 ← (( do (FPAdd acc_r elt2_i w__7) ) : SailM (BitVec esize) )
                let acc_r := (w__8 : (BitVec esize))
                (pure ((acc_r, elt2_i))))
            else (pure ((acc_r, elt2_i))) ) : SailM ((BitVec esize) × (BitVec esize)) )
          let w__9 ← (( do (ActivePredicateElement mask ((2 *i p) +i 1) esize) ) : SailM Bool )
          let (acc_i, elt2_r) ← (( do
            if (w__9 : Bool)
            then
              (do
                let w__10 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i 0) esize)) ) :
                  SailM (BitVec esize) )
                let elt2_r := (w__10 : (BitVec esize))
                let elt2_r ← (( do
                  if (sub_r : Bool)
                  then
                    (do
                      ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7703.57-7703.58"
                      (FPNeg elt2_r))
                  else (pure (elt2_r)) ) : SailM (BitVec esize) )
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7706.53-7706.54"
                let w__12 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__13 ← (( do (FPAdd acc_i elt2_r w__12) ) : SailM (BitVec esize) )
                let acc_i := (w__13 : (BitVec esize))
                (pure ((acc_i, elt2_r))))
            else (pure ((acc_i, elt2_r))) ) : SailM ((BitVec esize) × (BitVec esize)) )
          let w__14 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth acc_r))
            ) : SailM (BitVec VL) )
          let result := (w__14 : (BitVec VL))
          let w__15 ← (( do (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth acc_i))
            ) : SailM (BitVec VL) )
          let result := (w__15 : (BitVec VL))
          (pure ((acc_i, acc_r, elt2_i, elt2_r, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_neg_i : Bool, k_neg_r
  : Bool, sel_a : Nat, sel_b : Nat, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FCMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (neg_i : Bool) (neg_r : Bool) (sel_a : Nat) (sel_b : Nat) : SailM Unit := do
  let addend_i ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5104)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let addend_r ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5105)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5106)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (addend_i, addend_r, result) ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := (addend_i, addend_r, result)
      for p in [loop_p_lower:loop_p_upper:1]i do
        let (addend_i, addend_r, result) := loop_vars
        loop_vars ← do
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let addend_r := (w__4 : (BitVec esize))
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let addend_i := (w__5 : (BitVec esize))
          let w__6 ← (( do (ActivePredicateElement mask ((2 *i p) +i 0) esize) ) : SailM Bool )
          let addend_r ← (( do
            if (w__6 : Bool)
            then
              (do
                let elt1_a ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i sel_a) esize)) ) :
                  SailM (BitVec esize) )
                let elt2_a ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i sel_a) esize)) ) :
                  SailM (BitVec esize) )
                let elt2_a ← (( do
                  if (neg_r : Bool)
                  then
                    (do
                      ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7790.57-7790.58"
                      (FPNeg elt2_a))
                  else (pure (elt2_a)) ) : SailM (BitVec esize) )
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7793.53-7793.54"
                let w__8 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPMulAdd addend_r elt1_a elt2_a w__8))
            else (pure (addend_r)) ) : SailM (BitVec esize) )
          let w__10 ← (( do (ActivePredicateElement mask ((2 *i p) +i 1) esize) ) : SailM Bool )
          let addend_i ← (( do
            if (w__10 : Bool)
            then
              (do
                let elt1_a ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i sel_a) esize)) ) :
                  SailM (BitVec esize) )
                let elt2_b ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i sel_b) esize)) ) :
                  SailM (BitVec esize) )
                let elt2_b ← (( do
                  if (neg_i : Bool)
                  then
                    (do
                      ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7800.57-7800.58"
                      (FPNeg elt2_b))
                  else (pure (elt2_b)) ) : SailM (BitVec esize) )
                ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7803.53-7803.54"
                let w__12 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                (FPMulAdd addend_i elt1_a elt2_b w__12))
            else (pure (addend_i)) ) : SailM (BitVec esize) )
          let w__14 ← (( do
            (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth addend_r)) ) : SailM
            (BitVec VL) )
          let result := (w__14 : (BitVec VL))
          let w__15 ← (( do
            (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth addend_i)) ) : SailM
            (BitVec VL) )
          let result := (w__15 : (BitVec VL))
          (pure ((addend_i, addend_r, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec esize) × (BitVec VL)) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_neg_i : Bool, k_neg_r
  : Bool, sel_a : Nat, sel_b : Nat, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FCMLA_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (neg_i : Bool) (neg_r : Bool) (sel_a : Nat) (sel_b : Nat) : SailM Unit := do
  let addend_i ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5107)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let addend_r ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5108)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let elt1_a ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5109)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let elt2_a ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5110)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let elt2_b ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5111)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let s ← (( do (undefined_int_at (← occLabel 5112) ()) ) : SailM Int )
  let segmentbase ← (( do (undefined_int_at (← occLabel 5113) ()) ) : SailM Int )
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let pairspersegment : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv 128 (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5114)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase) ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase)
      for p in [loop_p_lower:loop_p_upper:1]i do
        let (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase) := loop_vars
        loop_vars ← do
          let segmentbase : Int := (p -i (Nat.mod (Sail.Int.toNatChecked (p)) pairspersegment))
          let s : Int := (segmentbase +i index)
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let addend_r := (w__0 : (BitVec esize))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let addend_i := (w__1 : (BitVec esize))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt1_a := (w__2 : (BitVec esize))
          let s : Int := s
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i s) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt2_a := (w__3 : (BitVec esize))
          let s : Int := s
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i s) +i sel_b) esize)) ) : SailM
            (BitVec esize) )
          let elt2_b := (w__4 : (BitVec esize))
          let elt2_a ← (( do
            if (neg_r : Bool)
            then
              (do
                (FPNeg elt2_a))
            else (pure (elt2_a)) ) : SailM (BitVec esize) )
          let elt2_b ← (( do
            if (neg_i : Bool)
            then
              (do
                (FPNeg elt2_b))
            else (pure (elt2_b)) ) : SailM (BitVec esize) )
          let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__8 ← (( do (FPMulAdd addend_r elt1_a elt2_a w__7) ) : SailM (BitVec esize) )
          let addend_r := (w__8 : (BitVec esize))
          let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__10 ← (( do (FPMulAdd addend_i elt1_a elt2_b w__9) ) : SailM (BitVec esize) )
          let addend_i := (w__10 : (BitVec esize))
          let w__11 ← (( do
            (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth addend_r)) ) : SailM
            (BitVec VL) )
          let result := (w__11 : (BitVec VL))
          let w__12 ← (( do
            (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth addend_i)) ) : SailM
            (BitVec VL) )
          let result := (w__12 : (BitVec VL))
          (pure ((addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase)))
      (pure loop_vars)) ) : SailM
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec VL) × Int × Int)
    )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_neg_i : Bool, k_neg_r
  : Bool, sel_a : Nat, sel_b : Nat, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FCMLA_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (neg_i : Bool) (neg_r : Bool) (sel_a : Nat) (sel_b : Nat) : SailM Unit := do
  let addend_i ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5115)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let addend_r ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5116)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let elt1_a ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5117)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let elt2_a ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5118)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let elt2_b ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5119)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let s ← (( do (undefined_int_at (← occLabel 5120) ()) ) : SailM Int )
  let segmentbase ← (( do (undefined_int_at (← occLabel 5121) ()) ) : SailM Int )
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let pairspersegment : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv 128 (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5122)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase) ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase)
      for p in [loop_p_lower:loop_p_upper:1]i do
        let (addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase) := loop_vars
        loop_vars ← do
          let segmentbase : Int := (p -i (Nat.mod (Sail.Int.toNatChecked (p)) pairspersegment))
          let s : Int := (segmentbase +i index)
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let addend_r := (w__0 : (BitVec esize))
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let addend_i := (w__1 : (BitVec esize))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt1_a := (w__2 : (BitVec esize))
          let s : Int := s
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i s) +i sel_a) esize)) ) : SailM
            (BitVec esize) )
          let elt2_a := (w__3 : (BitVec esize))
          let s : Int := s
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i s) +i sel_b) esize)) ) : SailM
            (BitVec esize) )
          let elt2_b := (w__4 : (BitVec esize))
          let elt2_a ← (( do
            if (neg_r : Bool)
            then
              (do
                (FPNeg elt2_a))
            else (pure (elt2_a)) ) : SailM (BitVec esize) )
          let elt2_b ← (( do
            if (neg_i : Bool)
            then
              (do
                (FPNeg elt2_b))
            else (pure (elt2_b)) ) : SailM (BitVec esize) )
          let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__8 ← (( do (FPMulAdd addend_r elt1_a elt2_a w__7) ) : SailM (BitVec esize) )
          let addend_r := (w__8 : (BitVec esize))
          let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__10 ← (( do (FPMulAdd addend_i elt1_a elt2_b w__9) ) : SailM (BitVec esize) )
          let addend_i := (w__10 : (BitVec esize))
          let w__11 ← (( do
            (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth addend_r)) ) : SailM
            (BitVec VL) )
          let result := (w__11 : (BitVec VL))
          let w__12 ← (( do
            (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth addend_i)) ) : SailM
            (BitVec VL) )
          let result := (w__12 : (BitVec VL))
          (pure ((addend_i, addend_r, elt1_a, elt2_a, elt2_b, result, s, segmentbase)))
      (pure loop_vars)) ) : SailM
    ((BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec esize) × (BitVec VL) × Int × Int)
    )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_ZZi_H (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5123)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPMul element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, k_op3_neg : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLA_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec esize) )
          let element3 ← (( do
            if (op3_neg : Bool)
            then
              (do
                (FPNeg element3))
            else (pure (element3)) ) : SailM (BitVec esize) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMulAdd element3 element1 element2 w__2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg :
  Bool, k_op3_neg : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLS_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (FPNeg element1))
            else (pure (element1)) ) : SailM (BitVec esize) )
          let element3 ← (( do
            if (op3_neg : Bool)
            then
              (do
                (FPNeg element3))
            else (pure (element3)) ) : SailM (BitVec esize) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMulAdd element3 element1 element2 w__2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMUL_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5124)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) :
            SailM (BitVec esize) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPMul element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
