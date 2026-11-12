import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0115
import ArmFull.Fn.M0150
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2
  = 0 ∧
  sel1 = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_EORTB_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1) esize)) ) : SailM
            (BitVec esize) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result ((2 *i e) +i sel1) esize (Sail.BitVec.castWidth (element1 ^^^ element2)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b : Nat, k_sub_i
  : Bool, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CDOT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5643)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 0)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let elt1_r : Int := (BitVec.toInt w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 1)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let elt1_i : Int := (BitVec.toInt w__1)
                  let w__2 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                      (((4 *i e) +i (2 *i i)) +i sel_a) (Sail.Int.toNatChecked ((Int.ediv esize 4)))))
                    ) : SailM (BitVec (esize / 4)) )
                  let elt2_a : Int := (BitVec.toInt w__2)
                  let w__3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                      (((4 *i e) +i (2 *i i)) +i sel_b) (Sail.Int.toNatChecked ((Int.ediv esize 4)))))
                    ) : SailM (BitVec (esize / 4)) )
                  let elt2_b : Int := (BitVec.toInt w__3)
                  let res : (BitVec esize) :=
                    if (sub_i : Bool)
                    then (BitVec.subInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b))
                    else (BitVec.addInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b
  : Nat, k_sub_i : Bool, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CDOT_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5644)
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
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 0)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let elt1_r : Int := (BitVec.toInt w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 1)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let elt1_i : Int := (BitVec.toInt w__1)
                  let w__2 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                      (((4 *i s) +i (2 *i i)) +i sel_a) (Sail.Int.toNatChecked ((Int.ediv esize 4)))))
                    ) : SailM (BitVec (esize / 4)) )
                  let elt2_a : Int := (BitVec.toInt w__2)
                  let w__3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                      (((4 *i s) +i (2 *i i)) +i sel_b) (Sail.Int.toNatChecked ((Int.ediv esize 4)))))
                    ) : SailM (BitVec (esize / 4)) )
                  let elt2_b : Int := (BitVec.toInt w__3)
                  let res : (BitVec esize) :=
                    if (sub_i : Bool)
                    then (BitVec.subInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b))
                    else (BitVec.addInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, sel_a : Nat, sel_b
  : Nat, k_sub_i : Bool, List.elem sel_b [0, 1] ∧
  List.elem sel_a [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_CDOT_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (sel_a : Nat) (sel_b : Nat) (sub_i : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5645)
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
          let res ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let res ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := res
              for i in [loop_i_lower:loop_i_upper:1]i do
                let res := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 0)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let elt1_r : Int := (BitVec.toInt w__0)
                  let w__1 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (((4 *i e) +i (2 *i i)) +i 1)
                      (Sail.Int.toNatChecked ((Int.ediv esize 4))))) ) : SailM (BitVec (esize / 4))
                    )
                  let elt1_i : Int := (BitVec.toInt w__1)
                  let w__2 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                      (((4 *i s) +i (2 *i i)) +i sel_a) (Sail.Int.toNatChecked ((Int.ediv esize 4)))))
                    ) : SailM (BitVec (esize / 4)) )
                  let elt2_a : Int := (BitVec.toInt w__2)
                  let w__3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                      (((4 *i s) +i (2 *i i)) +i sel_b) (Sail.Int.toNatChecked ((Int.ediv esize 4)))))
                    ) : SailM (BitVec (esize / 4)) )
                  let elt2_b : Int := (BitVec.toInt w__3)
                  let res : (BitVec esize) :=
                    if (sub_i : Bool)
                    then (BitVec.subInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b))
                    else (BitVec.addInt (BitVec.addInt res (elt1_r *i elt2_a)) (elt1_i *i elt2_b))
                  (pure (res))
              (pure loop_vars_1)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth res))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULH_Z_ZZi_H (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5658)
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
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := (BitVec.toInt w__0)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := (BitVec.toInt w__1)
          let res : Int := ((2 *i element1) *i element2)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat (Int.shiftr res esize) esize))
            ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULH_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5659)
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
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := (BitVec.toInt w__0)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := (BitVec.toInt w__1)
          let res : Int := ((2 *i element1) *i element2)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat (Int.shiftr res esize) esize))
            ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMULH_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5660)
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
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := (BitVec.toInt w__0)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := (BitVec.toInt w__1)
          let res : Int := ((2 *i element1) *i element2)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat (Int.shiftr res esize) esize))
            ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SRSRA_Z_ZI__ (VL : Nat) (da : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5661)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element : Int :=
            (_shr_int_general ((BitVec.toInt w__0) +i (_shl_int_general 1 (shift -i 1))) shift)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize
            (Sail.BitVec.castWidth (w__1 + (Sail.BitVec.castWidth (integer_subrange element
                (esize -i 1) 0)))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SSRA_Z_ZI__ (VL : Nat) (da : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5662)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element : Int := (_shr_int_general (BitVec.toInt w__0) shift)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize
            (Sail.BitVec.castWidth (w__1 + (Sail.BitVec.castWidth (integer_subrange element
                (esize -i 1) 0)))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_URSRA_Z_ZI__ (VL : Nat) (da : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5663)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element : Int :=
            (_shr_int_general ((BitVec.toNat w__0) +i (_shl_int_general 1 (shift -i 1))) shift)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize
            (Sail.BitVec.castWidth (w__1 + (Sail.BitVec.castWidth (integer_subrange element
                (esize -i 1) 0)))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_USRA_Z_ZI__ (VL : Nat) (da : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5664)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element : Int := (_shr_int_general (BitVec.toNat w__0) shift)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result e esize
            (Sail.BitVec.castWidth (w__1 + (Sail.BitVec.castWidth (integer_subrange element
                (esize -i 1) 0)))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, m : Nat, rot : Int, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_XAR_Z_ZZI__ (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (rot : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5676)
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
          ArmFull.assert (rot ≥b 0) "sail-arm/instrs64_sve.sail:52632.36-52632.37"
          (Elem_set result e esize
            (Sail.BitVec.castWidth (ROR (element1 ^^^ element2) (Sail.Int.toNatChecked (rot)))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BCAX_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read k VL)) ) : SailM (BitVec VL) )
  (Z_set dn VL
    (Sail.BitVec.castWidth (operand1 ^^^ (operand2 &&& (Complement.complement operand3)))))


/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_EOR3_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read k VL)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth ((operand1 ^^^ operand2) ^^^ operand3)))


/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BSL_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read k VL)) ) : SailM (BitVec VL) )
  (Z_set dn VL
    (Sail.BitVec.castWidth ((operand1 &&& operand3) ||| (operand2 &&& (Complement.complement
          operand3)))))


/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BSL1N_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read k VL)) ) : SailM (BitVec VL) )
  (Z_set dn VL
    (Sail.BitVec.castWidth (((Complement.complement operand1) &&& operand3) ||| (operand2 &&& (Complement.complement
          operand3)))))


/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BSL2N_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read k VL)) ) : SailM (BitVec VL) )
  (Z_set dn VL
    (Sail.BitVec.castWidth ((operand1 &&& operand3) ||| ((Complement.complement operand2) &&& (Complement.complement
          operand3)))))


/-- Type quantifiers: VL : Nat, dn : Nat, k : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ k ∧ k ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_NBSL_Z_ZZZ__ (VL : Nat) (dn : Nat) (k : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read k VL)) ) : SailM (BitVec VL) )
  (Z_set dn VL
    (Sail.BitVec.castWidth (Complement.complement
      ((operand1 &&& operand3) ||| (operand2 &&& (Complement.complement operand3))))))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_ADCLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let carry_out ← (( do (undefined_bitvector_at (← occLabel 5677) 1) ) : SailM (BitVec 1) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 5678) 4) ) : SailM (BitVec 4) )
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5679)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let carries ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let (carry_out, nzcv, res, result) ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := (carry_out, nzcv, res, result)
      for p in [loop_p_lower:loop_p_upper:1]i do
        let (carry_out, nzcv, res, result) := loop_vars
        loop_vars ← do
          let element1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read result ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let element2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i p) +i 0) esize)) ) : SailM
            (BitVec esize) )
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read carries ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let carry_in : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__0 0)]))
          let (tup__0, tup__1) :=
            ((AddWithCarry element1 element2 carry_in) : ((BitVec esize) × (BitVec 4)))
          let res : (BitVec esize) := tup__0
          let nzcv : (BitVec 4) := tup__1
          let carry_out : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access nzcv 1)]))
          let w__1 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth res)) ) :
            SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          let w__2 ← (( do
            (Elem_set result ((2 *i p) +i 1) esize
              (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend carry_out esize))) ) : SailM
            (BitVec VL) )
          let result := (w__2 : (BitVec VL))
          (pure ((carry_out, nzcv, res, result)))
      (pure loop_vars)) ) : SailM ((BitVec 1) × (BitVec 4) × (BitVec esize) × (BitVec VL)) )
  (Z_set da VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
