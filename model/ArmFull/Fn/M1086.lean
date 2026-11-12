import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0018
import ArmFull.Fn.M0117
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0217
import ArmFull.Fn.M0218
import ArmFull.Fn.M0255
import ArmFull.Fn.M0582
import ArmFull.Fn.M1040
import ArmFull.Fn.M1041
import ArmFull.Fn.M1042
import ArmFull.Fn.M1071

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

/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_MZ_Z_2 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7307)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FixedToFP element 0 is_unsigned w__1 rounding 32) ) : SailM
                  (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_MZ_Z_4 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7308)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FixedToFP element 0 is_unsigned w__1 rounding 32) ) : SailM
                  (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_MZ_Z_2 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7309)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FixedToFP element 0 is_unsigned w__1 rounding 32) ) : SailM
                  (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_is_unsigned : Bool, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_MZ_Z_4 (VL : Nat) (d : Nat) (n : Nat) (nreg : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7310)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FixedToFP element 0 is_unsigned w__1 rounding 32) ) : SailM
                  (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTA_MZ_Z_2 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7311)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTM_MZ_Z_2 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7312)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTN_MZ_Z_2 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7313)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTP_MZ_Z_2 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7314)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTA_MZ_Z_4 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7315)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTM_MZ_Z_4 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7316)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTN_MZ_Z_4 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7317)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: VL : Nat, d : Nat, k_exact : Bool, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FRINTP_MZ_Z_4 (VL : Nat) (d : Nat) (exact : Bool) (n : Nat) (nreg : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7318)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element ← (( do (Elem_read operand e 32) ) : SailM (BitVec 32) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec 32) )
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 32 w__2) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
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


/-- Type quantifiers: k_highestAddressfirst : Bool, k_ispair : Bool, size : Nat, List.elem size
  [1, 2, 4, 8, 16] -/
def Mem_read__2 (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) (highestAddressfirst : Bool) : SailM (BitVec (size * 8)) := do
  let c ← (( do (undefined_Constraint (← occLabel 1640) ()) ) : SailM Constraint )
  let halfsize : Nat := (Sail.Int.toNatChecked ((Int.ediv size 2)))
  let value_name ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1641)
      (Sail.Int.toNatChecked ((size *i 8))))) ) : SailM (BitVec (size * 8)) )
  let alignment : Int :=
    if (ispair : Bool)
    then halfsize
    else size
  let aligned : Bool := (IsAligned__1 address alignment)
  let w__1 ← (( do
    if (((! aligned) : Bool) : Bool)
    then
      (do
        (AArch64_UnalignedAccessFaults accdesc address size))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort address w__2))
  else (pure (()))
  let value_name ← (( do
    if ((((BEq.beq accdesc.acctype AccessType_ASIMD) && (size == 16)) && (IsAligned__1 address 8)) : Bool)
    then
      (do
        let lowhalf ← (( do
          ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read__1 address halfsize accdesc aligned
            ispair)) ) : SailM (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
        let highhalf ← (( do
          ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read__1 (BitVec.addInt address halfsize)
            halfsize accdesc aligned ispair)) ) : SailM
          (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
        let value_name : (BitVec (size * 8)) := (Sail.BitVec.castWidth (highhalf +++ lowhalf))
        (pure (value_name)))
    else
      (do
        let w__5 ← (( do
          if ((← do
               (HaveLSE2Ext ())) : Bool)
          then
            (do
              (AllInAlignedQuantity address size 16))
          else (pure false) ) : SailM Bool )
        if (w__5 : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read__1 address size accdesc aligned
              ispair)))
        else
          (do
            if ((ispair && aligned) : Bool)
            then
              (do
                ArmFull.assert ((((halfsize == 1) || (halfsize == 2)) || (halfsize == 4)) || (halfsize == 8)) "sail-arm/v8_base.sail:28194.52-28194.53"
                let highhalf ← (( do
                  ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1644)
                    (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
                  (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                let lowhalf ← (( do
                  ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1645)
                    (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
                  (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                let w__8 ← (( do
                  (pure ((← do
                        (HaveLRCPC3Ext ())) && (highestAddressfirst : Bool))) ) : SailM Bool )
                let (highhalf, lowhalf) ← (( do
                  if (w__8 : Bool)
                  then
                    (do
                      let w__9 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read
                          (BitVec.addInt address halfsize) halfsize accdesc aligned)) ) : SailM
                        (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                      let highhalf := (w__9 : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)))
                      let w__10 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read address halfsize
                          accdesc aligned)) ) : SailM
                        (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                      let lowhalf := (w__10 : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)))
                      (pure ((highhalf, lowhalf))))
                  else
                    (do
                      let w__11 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read address halfsize
                          accdesc aligned)) ) : SailM
                        (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                      let lowhalf := (w__11 : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)))
                      let w__12 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read
                          (BitVec.addInt address halfsize) halfsize accdesc aligned)) ) : SailM
                        (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                      let highhalf := (w__12 : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)))
                      (pure ((highhalf, lowhalf)))) ) : SailM
                  ((BitVec ((Sail.Int.toNatChecked halfsize) * 8)) × (BitVec ((Sail.Int.toNatChecked halfsize) * 8)))
                  )
                let value_name : (BitVec (size * 8)) :=
                  (Sail.BitVec.castWidth (highhalf +++ lowhalf))
                (pure (value_name)))
            else
              (do
                if (aligned : Bool)
                then
                  (do
                    ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read__1 address size accdesc
                      aligned ispair)))
                else
                  (do
                    ArmFull.assert (size >b 1) "sail-arm/v8_base.sail:28208.23-28208.24"
                    ArmFull.assert ((((halfsize == 1) || (halfsize == 2)) || (halfsize == 4)) || (halfsize == 8)) "sail-arm/v8_base.sail:28209.52-28209.53"
                    let highhalf ← (( do
                      ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1642)
                        (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
                      (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                    let lowhalf ← (( do
                      ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1643)
                        (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
                      (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                    let w__16 ← (( do
                      (pure ((← do
                            (pure ((← do
                                  (HaveLRCPC3Ext ())) && (ispair : Bool)))) && (highestAddressfirst : Bool)))
                      ) : SailM Bool )
                    if (w__16 : Bool)
                    then
                      (do
                        let highhalf ← (( do
                          let loop_i_lower : Nat := 0
                          let loop_i_upper : Int := (halfsize -i 1)
                          (do
                            let mut loop_vars := highhalf
                            for i in [loop_i_lower:loop_i_upper:1]i do
                              let highhalf := loop_vars
                              loop_vars ← do
                                let w__17 ← (( do
                                  (AArch64_MemSingle_read
                                    (BitVec.addInt (BitVec.addInt address halfsize) i) 1 accdesc
                                    aligned) ) : SailM (BitVec (1 * 8)) )
                                let highhalf :=
                                  ((Sail.BitVec.updateSubrange highhalf
                                    (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                                    (Sail.Int.toNatChecked ((8 *i i))) (Sail.BitVec.castWidth w__17)) : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)))
                                (pure (highhalf))
                            (pure loop_vars)) ) : SailM
                          (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                        let lowhalf ← (( do
                          let loop_i_lower : Nat := 0
                          let loop_i_upper : Int := (halfsize -i 1)
                          (do
                            let mut loop_vars := lowhalf
                            for i in [loop_i_lower:loop_i_upper:1]i do
                              let lowhalf := loop_vars
                              loop_vars ← do
                                let w__18 ← (( do
                                  (AArch64_MemSingle_read (BitVec.addInt address i) 1 accdesc
                                    aligned) ) : SailM (BitVec (1 * 8)) )
                                let lowhalf :=
                                  ((Sail.BitVec.updateSubrange lowhalf
                                    (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                                    (Sail.Int.toNatChecked ((8 *i i))) (Sail.BitVec.castWidth w__18)) : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)))
                                (pure (lowhalf))
                            (pure loop_vars)) ) : SailM
                          (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                        let value_name : (BitVec (size * 8)) :=
                          (Sail.BitVec.castWidth (highhalf +++ lowhalf))
                        (pure (value_name)))
                    else
                      (do
                        let w__19 ← (( do (AArch64_MemSingle_read address 1 accdesc aligned) ) :
                          SailM (BitVec (1 * 8)) )
                        let value_name :=
                          ((Sail.BitVec.updateSubrange value_name 7 0 w__19) : (BitVec (size * 8)))
                        let c ← (( do (ConstrainUnpredictable Unpredictable_DEVPAGE2) ) : SailM
                          Constraint )
                        ArmFull.assert ((BEq.beq c Constraint_FAULT) || (BEq.beq c Constraint_NONE)) "sail-arm/v8_base.sail:28223.63-28223.64"
                        let aligned : Bool :=
                          if ((BEq.beq c Constraint_NONE) : Bool)
                          then true
                          else aligned
                        let loop_i_lower : Nat := 1
                        let loop_i_upper : Nat := (Sail.Int.toNatChecked ((size -i 1)))
                        (do
                          let mut loop_vars := value_name
                          for i in [loop_i_lower:loop_i_upper:1]i do
                            let value_name := loop_vars
                            loop_vars ← do
                              let w__20 ← (( do
                                (AArch64_MemSingle_read (BitVec.addInt address i) 1 accdesc aligned)
                                ) : SailM (BitVec (1 * 8)) )
                              let value_name :=
                                ((Sail.BitVec.updateSubrange value_name
                                  (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                                  (Sail.Int.toNatChecked ((8 *i i))) (Sail.BitVec.castWidth w__20)) : (BitVec (size * 8)))
                              (pure (value_name))
                          (pure loop_vars))))))) ) : SailM (BitVec (size * 8)) )
  let w__21 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let value_name : (BitVec (size * 8)) :=
    if (w__21 : Bool)
    then (reverse_endianness value_name)
    else value_name
  (pure ((Sail.BitVec.castWidth value_name)))


end ArmFull.Functions
