import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0146
import ArmFull.Fn.M0178
import ArmFull.Fn.M0204
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
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

/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7242)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((n +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let sum ← (( do (FPDotAdd_ZA (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) )
                    : SailM (BitVec 32) )
                  (Elem_set result e 32 sum)
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7243)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let sum ← (( do (BFDotAdd (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) ) :
                    SailM (BitVec 32) )
                  (Elem_set result e 32 sum)
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZi_4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7244)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let sum ← (( do (BFDotAdd (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) ) :
                    SailM (BitVec 32) )
                  (Elem_set result e 32 sum)
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7245)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let sum ← (( do (FPDotAdd_ZA (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) )
                    : SailM (BitVec 32) )
                  (Elem_set result e 32 sum)
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZi_4xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7246)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let elt1_a ← (( do (Elem_read operand1 ((2 *i e) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt1_b ← (( do (Elem_read operand1 ((2 *i e) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let sum ← (( do (FPDotAdd_ZA (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) )
                    : SailM (BitVec 32) )
                  (Elem_set result e 32 sum)
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_BFVDOT_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name 2)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7247)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1a ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL)
            )
          let operand1b ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 1) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let elt1_a ← (( do (Elem_read operand1a ((2 *i e) +i r) 16) ) : SailM
                    (BitVec 16) )
                  let elt1_b ← (( do (Elem_read operand1b ((2 *i e) +i r) 16) ) : SailM
                    (BitVec 16) )
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let sum ← (( do (BFDotAdd (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) ) :
                    SailM (BitVec 32) )
                  (Elem_set result e 32 sum)
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, index : Nat, m : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ (is_VL VL) -/
def execute_FVDOT_ZA_ZZi_2xi (VL : Nat) (index : Nat) (m : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name 2)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 32)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7248)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1a ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL)
            )
          let operand1b ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 1) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let elt1_a ← (( do (Elem_read operand1a ((2 *i e) +i r) 16) ) : SailM
                    (BitVec 16) )
                  let elt1_b ← (( do (Elem_read operand1b ((2 *i e) +i r) 16) ) : SailM
                    (BitVec 16) )
                  let elt2_a ← (( do (Elem_read operand2 ((2 *i s) +i 0) 16) ) : SailM (BitVec 16)
                    )
                  let elt2_b ← (( do (Elem_read operand2 ((2 *i s) +i 1) 16) ) : SailM (BitVec 16)
                    )
                  let sum ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let sum ← (( do (FPDotAdd_ZA (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__0) )
                    : SailM (BitVec 32) )
                  (Elem_set result e 32 sum)
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 15 ∧ nreg = 1 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZV_1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7265)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((n +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (FPNeg element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (FPMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op : Bool, v : Nat, 0
  ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FMLAL_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7266)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let vec : Int := (vec -i (fmod_int vec 2))
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          let result ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Nat := 1
            (do
              let mut loop_vars_1 := result
              for i in [loop_i_lower:loop_i_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let operand3 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (ZAvector_read (vec +i i) VL)) ) : SailM
                    (BitVec VL) )
                  let result ← (( do
                    let loop_e_lower : Nat := 0
                    let loop_e_upper : Int := (elements -i 1)
                    (do
                      let mut loop_vars_2 := result
                      for e in [loop_e_lower:loop_e_upper:1]i do
                        let result := loop_vars_2
                        loop_vars_2 ← do
                          let element1 ← (( do (Elem_read operand1 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element2 ← (( do (Elem_read operand2 ((2 *i e) +i i) 16) ) : SailM
                            (BitVec 16) )
                          let element3 ← (( do (Elem_read operand3 e 32) ) : SailM (BitVec 32) )
                          let element1 ← (( do
                            if (sub_op : Bool)
                            then
                              (do
                                (FPNeg element1))
                            else (pure (element1)) ) : SailM (BitVec 16) )
                          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                          let w__2 ← (( do
                            (FPMulAddH_ZA (k_N := 32) element3 element1 element2 w__1) ) : SailM
                            (BitVec 32) )
                          (Elem_set result e 32 w__2)
                      (pure loop_vars_2)) ) : SailM (BitVec VL) )
                  (ZAvector_set (vec +i i) VL (Sail.BitVec.castWidth result))
                  (pure (result))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


end ArmFull.Functions
