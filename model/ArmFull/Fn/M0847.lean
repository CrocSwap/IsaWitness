import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0087
import ArmFull.Fn.M0150
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0582

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg
  = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UUNPK_MZ_Z_2 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let sreg : Nat := (Sail.Int.toNatChecked ((Int.ediv nreg 2)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7508)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Int := (sreg -i 1)
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := results
            for i in [loop_i_lower:loop_i_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let loop_e_lower : Nat := 0
                let loop_e_upper : Int := (elements -i 1)
                (do
                  let mut loop_vars_2 := results
                  for e in [loop_e_lower:loop_e_upper:1]i do
                    let results := loop_vars_2
                    loop_vars_2 ← do
                      let element ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((i *i elements) +i e)
                          hsize)) ) : SailM (BitVec (Sail.Int.toNatChecked hsize)) )
                      let w__1 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) : SailM
                        (BitVec esize) )
                      let w__2 ← (( do
                        (Elem_set
                          (GetElem?.getElem! results (Sail.Int.toNatChecked (((2 *i r) +i i)))) e
                          esize (Sail.BitVec.castWidth w__1)) ) : SailM (BitVec VL) )
                      let results :=
                        ((vectorUpdate results (Sail.Int.toNatChecked (((2 *i r) +i i))) w__2) : (Vector (BitVec VL) 4))
                      (pure (results))
                  (pure loop_vars_2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg
  = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPK_MZ_Z_2 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let sreg : Nat := (Sail.Int.toNatChecked ((Int.ediv nreg 2)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7509)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Int := (sreg -i 1)
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := results
            for i in [loop_i_lower:loop_i_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let loop_e_lower : Nat := 0
                let loop_e_upper : Int := (elements -i 1)
                (do
                  let mut loop_vars_2 := results
                  for e in [loop_e_lower:loop_e_upper:1]i do
                    let results := loop_vars_2
                    loop_vars_2 ← do
                      let element ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((i *i elements) +i e)
                          hsize)) ) : SailM (BitVec (Sail.Int.toNatChecked hsize)) )
                      let w__1 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) : SailM
                        (BitVec esize) )
                      let w__2 ← (( do
                        (Elem_set
                          (GetElem?.getElem! results (Sail.Int.toNatChecked (((2 *i r) +i i)))) e
                          esize (Sail.BitVec.castWidth w__1)) ) : SailM (BitVec VL) )
                      let results :=
                        ((vectorUpdate results (Sail.Int.toNatChecked (((2 *i r) +i i))) w__2) : (Vector (BitVec VL) 4))
                      (pure (results))
                  (pure loop_vars_2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg
  = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UUNPK_MZ_Z_4 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let sreg : Nat := (Sail.Int.toNatChecked ((Int.ediv nreg 2)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7510)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Int := (sreg -i 1)
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := results
            for i in [loop_i_lower:loop_i_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let loop_e_lower : Nat := 0
                let loop_e_upper : Int := (elements -i 1)
                (do
                  let mut loop_vars_2 := results
                  for e in [loop_e_lower:loop_e_upper:1]i do
                    let results := loop_vars_2
                    loop_vars_2 ← do
                      let element ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((i *i elements) +i e)
                          hsize)) ) : SailM (BitVec (Sail.Int.toNatChecked hsize)) )
                      let w__1 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) : SailM
                        (BitVec esize) )
                      let w__2 ← (( do
                        (Elem_set
                          (GetElem?.getElem! results (Sail.Int.toNatChecked (((2 *i r) +i i)))) e
                          esize (Sail.BitVec.castWidth w__1)) ) : SailM (BitVec VL) )
                      let results :=
                        ((vectorUpdate results (Sail.Int.toNatChecked (((2 *i r) +i i))) w__2) : (Vector (BitVec VL) 4))
                      (pure (results))
                  (pure loop_vars_2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg
  = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPK_MZ_Z_4 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let sreg : Nat := (Sail.Int.toNatChecked ((Int.ediv nreg 2)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7511)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Int := (sreg -i 1)
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := results
            for i in [loop_i_lower:loop_i_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let loop_e_lower : Nat := 0
                let loop_e_upper : Int := (elements -i 1)
                (do
                  let mut loop_vars_2 := results
                  for e in [loop_e_lower:loop_e_upper:1]i do
                    let results := loop_vars_2
                    loop_vars_2 ← do
                      let element ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((i *i elements) +i e)
                          hsize)) ) : SailM (BitVec (Sail.Int.toNatChecked hsize)) )
                      let w__1 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) : SailM
                        (BitVec esize) )
                      let w__2 ← (( do
                        (Elem_set
                          (GetElem?.getElem! results (Sail.Int.toNatChecked (((2 *i r) +i i)))) e
                          esize (Sail.BitVec.castWidth w__1)) ) : SailM (BitVec VL) )
                      let results :=
                        ((vectorUpdate results (Sail.Int.toNatChecked (((2 *i r) +i i))) w__2) : (Vector (BitVec VL) 4))
                      (pure (results))
                  (pure loop_vars_2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHR_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7512)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHR_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7513)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRU_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7514)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7515)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 3
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((4 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHRN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7516)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 3
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((4 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRUN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7517)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_i_lower : Nat := 0
          let loop_i_upper : Nat := 3
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((4 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHR_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7518)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 3
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHR_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7519)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 3
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRU_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7520)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 3
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
