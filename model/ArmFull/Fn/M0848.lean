import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVT_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7521)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVT_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7522)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toNat w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTU_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7523)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7524)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((4 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVTN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7525)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let element : Int := (BitVec.toNat w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((4 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTUN_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7526)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((4 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVT_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7527)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVT_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7528)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let element : Int := (BitVec.toNat w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTU_Z_MZ4__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((4 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7529)
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
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((4 *i esize))))) ) : SailM (BitVec (4 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((r *i elements) +i e) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP_MZ_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand0 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7530)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let base : Int := (r *i pairs)
          let result ← (( do
            let loop_p_lower : Nat := 0
            let loop_p_upper : Int := (pairs -i 1)
            (do
              let mut loop_vars_1 := result
              for p in [loop_p_lower:loop_p_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand0 (base +i p) esize)) ) : SailM
                    (BitVec esize) )
                  let w__1 ← (( do
                    (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__0)) ) : SailM
                    (BitVec VL) )
                  let result := (w__1 : (BitVec VL))
                  let w__2 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (base +i p) esize)) ) : SailM
                    (BitVec esize) )
                  (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP_MZ_ZZ_2 (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let result0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7531)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7532)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result0, result1) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := (result0, result1)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result0, result1) := loop_vars
        loop_vars ← do
          let base : Int := (r *i pairs)
          let operand ← (( do
            if ((r == 0) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (Z_read m VL))) ) : SailM (BitVec VL) )
          let loop_p_lower : Nat := 0
          let loop_p_upper : Int := (pairs -i 1)
          (do
            let mut loop_vars_1 := (result0, result1)
            for p in [loop_p_lower:loop_p_upper:1]i do
              let (result0, result1) := loop_vars_1
              loop_vars_1 ← do
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i p) +i 0) esize)) ) : SailM
                  (BitVec esize) )
                let w__3 ← (( do (Elem_set result0 (base +i p) esize (Sail.BitVec.castWidth w__2))
                  ) : SailM (BitVec VL) )
                let result0 := (w__3 : (BitVec VL))
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i p) +i 1) esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (Elem_set result1 (base +i p) esize (Sail.BitVec.castWidth w__4))
                  ) : SailM (BitVec VL) )
                let result1 := (w__5 : (BitVec VL))
                (pure ((result0, result1)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL (Sail.BitVec.castWidth result0))
  (Z_set (d +i 1) VL (Sail.BitVec.castWidth result1))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP_MZ_ZZ_2Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand0 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7533)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let base : Int := (r *i pairs)
          let result ← (( do
            let loop_p_lower : Nat := 0
            let loop_p_upper : Int := (pairs -i 1)
            (do
              let mut loop_vars_1 := result
              for p in [loop_p_lower:loop_p_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand0 (base +i p) esize)) ) : SailM
                    (BitVec esize) )
                  let w__1 ← (( do
                    (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__0)) ) : SailM
                    (BitVec VL) )
                  let result := (w__1 : (BitVec VL))
                  let w__2 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (base +i p) esize)) ) : SailM
                    (BitVec esize) )
                  (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP_MZ_ZZ_2Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let result0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7534)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7535)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result0, result1) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 1
    (do
      let mut loop_vars := (result0, result1)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result0, result1) := loop_vars
        loop_vars ← do
          let base : Int := (r *i pairs)
          let operand ← (( do
            if ((r == 0) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (Z_read m VL))) ) : SailM (BitVec VL) )
          let loop_p_lower : Nat := 0
          let loop_p_upper : Int := (pairs -i 1)
          (do
            let mut loop_vars_1 := (result0, result1)
            for p in [loop_p_lower:loop_p_upper:1]i do
              let (result0, result1) := loop_vars_1
              loop_vars_1 ← do
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i p) +i 0) esize)) ) : SailM
                  (BitVec esize) )
                let w__3 ← (( do (Elem_set result0 (base +i p) esize (Sail.BitVec.castWidth w__2))
                  ) : SailM (BitVec VL) )
                let result0 := (w__3 : (BitVec VL))
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i p) +i 1) esize)) ) : SailM
                  (BitVec esize) )
                let w__5 ← (( do (Elem_set result1 (base +i p) esize (Sail.BitVec.castWidth w__4))
                  ) : SailM (BitVec VL) )
                let result1 := (w__5 : (BitVec VL))
                (pure ((result0, result1)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL (Sail.BitVec.castWidth result0))
  (Z_set (d +i 1) VL (Sail.BitVec.castWidth result1))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP_MZ_Z_4 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 4)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let quads : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 4))))))
  let operand0 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 1) VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 2) VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i 3) VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7536)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := 3
    (do
      let mut loop_vars := result
      for r in [loop_r_lower:loop_r_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let base : Int := (r *i quads)
          let result ← (( do
            let loop_q_lower : Nat := 0
            let loop_q_upper : Int := (quads -i 1)
            (do
              let mut loop_vars_1 := result
              for q in [loop_q_lower:loop_q_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand0 (base +i q) esize)) ) : SailM
                    (BitVec esize) )
                  let w__1 ← (( do
                    (Elem_set result ((4 *i q) +i 0) esize (Sail.BitVec.castWidth w__0)) ) : SailM
                    (BitVec VL) )
                  let result := (w__1 : (BitVec VL))
                  let w__2 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (base +i q) esize)) ) : SailM
                    (BitVec esize) )
                  let w__3 ← (( do
                    (Elem_set result ((4 *i q) +i 1) esize (Sail.BitVec.castWidth w__2)) ) : SailM
                    (BitVec VL) )
                  let result := (w__3 : (BitVec VL))
                  let w__4 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (base +i q) esize)) ) : SailM
                    (BitVec esize) )
                  let w__5 ← (( do
                    (Elem_set result ((4 *i q) +i 2) esize (Sail.BitVec.castWidth w__4)) ) : SailM
                    (BitVec VL) )
                  let result := (w__5 : (BitVec VL))
                  let w__6 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 (base +i q) esize)) ) : SailM
                    (BitVec esize) )
                  (Elem_set result ((4 *i q) +i 3) esize (Sail.BitVec.castWidth w__6))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (pure (()))


end ArmFull.Functions
