import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
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

/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op
  : Bool, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZi_S4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7232)
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
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize))
                    ) : SailM (BitVec esize) )
                  let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize))
                    ) : SailM (BitVec esize) )
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec esize) )
                  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__2 ← (( do (FPMulAdd_ZA element3 element1 element2 w__1) ) : SailM
                    (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op
  : Bool, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7233)
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
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize))
                    ) : SailM (BitVec esize) )
                  let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize))
                    ) : SailM (BitVec esize) )
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec esize) )
                  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__2 ← (( do (FPMulAdd_ZA element3 element1 element2 w__1) ) : SailM
                    (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op
  : Bool, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZi_D4xi (VL : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7234)
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
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let segmentbase : Int :=
                    (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
                  let s : Int := (segmentbase +i index)
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 s esize))
                    ) : SailM (BitVec esize) )
                  let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize))
                    ) : SailM (BitVec esize) )
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec esize) )
                  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__2 ← (( do (FPMulAdd_ZA element3 element1 element2 w__1) ) : SailM
                    (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7235)
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
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
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


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7236)
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


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZW_2x2 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7237)
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
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
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


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZV_2x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7238)
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


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7239)
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
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
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


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_BFDOT_ZA_ZZV_4x1 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7240)
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


/-- Type quantifiers: VL : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ (is_VL VL) -/
def execute_FDOT_ZA_ZZW_4x4 (VL : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7241)
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
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
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


end ArmFull.Functions
