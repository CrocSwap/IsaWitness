import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0115
import ArmFull.Fn.M0120
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
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

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_ADCLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let carry_out ← (( do (undefined_bitvector_at (← occLabel 5680) 1) ) : SailM (BitVec 1) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 5681) 4) ) : SailM (BitVec 4) )
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5682)
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
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i p) +i 1) esize)) ) : SailM
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


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SBCLB_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let carry_out ← (( do (undefined_bitvector_at (← occLabel 5683) 1) ) : SailM (BitVec 1) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 5684) 4) ) : SailM (BitVec 4) )
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5685)
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
            ((AddWithCarry element1 (Complement.complement element2) carry_in) : ((BitVec esize) × (BitVec 4)))
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


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SBCLT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  let carry_out ← (( do (undefined_bitvector_at (← occLabel 5686) 1) ) : SailM (BitVec 1) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 5687) 4) ) : SailM (BitVec 4) )
  let res ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5688)
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
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read carries ((2 *i p) +i 1) esize)) ) : SailM
            (BitVec esize) )
          let carry_in : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__0 0)]))
          let (tup__0, tup__1) :=
            ((AddWithCarry element1 (Complement.complement element2) carry_in) : ((BitVec esize) × (BitVec 4)))
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


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SMULH_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5689)
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
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let product : Int := (Int.shiftr (element1 *i element2) esize)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange product (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n : Nat, 0 ≤
  n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UMULH_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5690)
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
          let element1 ← (( do (asl_Int w__0 is_unsigned) ) : SailM Int )
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
          let product : Int := (Int.shiftr (element1 *i element2) esize)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange product (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCLAMP_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5691)
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
          let element1 : Int := (BitVec.toInt w__0)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := (BitVec.toInt w__1)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let res : Int := (Min.min (Max.max element1 element3) element2)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCLAMP_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5692)
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
          let element1 : Int := (BitVec.toNat w__0)
          let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := (BitVec.toNat w__1)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toNat w__2)
          let res : Int := (Min.min (Max.max element1 element3) element2)
          (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, swsize : Nat, swsize = 64
  ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_REVD_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) (swsize : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) :
                SailM (BitVec esize) )
              let w__3 ← (( do (Reverse element swsize) ) : SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__3)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, m : Nat, n : Nat, v : Nat, 0 ≤ v
  ∧
  v ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧
  0 ≤ imm ∧
  imm ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PSEL_P_PPi__ (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (m : Nat) (n : Nat) (v : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let idx ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let element : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat idx) +i imm))) elements)
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5693)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (ActivePredicateElement operand2 element esize) ) : SailM Bool )
  let result : (BitVec (Sail.Int.toNatChecked PL)) :=
    if (w__0 : Bool)
    then operand1
    else (Sail.BitVec.castWidth (Zeros (n := PL)))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, rsize : Nat, rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELO_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec ((Sail.Int.toNatChecked PL) * 2)) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked ((PL *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5695)
      (Sail.Int.toNatChecked ((PL *i 2))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((elements *i 2) -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5696) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 <b w__1) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≤b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
          let result := (w__4 : (BitVec ((Sail.Int.toNatChecked PL) * 2)))
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM
    (Bool × (BitVec rsize) × (BitVec ((Sail.Int.toNatChecked PL) * 2))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((PL -i 1))) 0)))
  (P_set d1 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((PL *i 2) -i 1)))
      PL)))


/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, rsize : Nat, rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELS_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec ((Sail.Int.toNatChecked PL) * 2)) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked ((PL *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5697)
      (Sail.Int.toNatChecked ((PL *i 2))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((elements *i 2) -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5698) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 <b w__1) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≤b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
          let result := (w__4 : (BitVec ((Sail.Int.toNatChecked PL) * 2)))
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM
    (Bool × (BitVec rsize) × (BitVec ((Sail.Int.toNatChecked PL) * 2))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((PL -i 1))) 0)))
  (P_set d1 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((PL *i 2) -i 1)))
      PL)))


/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, rsize : Nat, rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELT_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec ((Sail.Int.toNatChecked PL) * 2)) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked ((PL *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5699)
      (Sail.Int.toNatChecked ((PL *i 2))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((elements *i 2) -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5700) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 <b w__1) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≤b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
          let result := (w__4 : (BitVec ((Sail.Int.toNatChecked PL) * 2)))
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM
    (Bool × (BitVec rsize) × (BitVec ((Sail.Int.toNatChecked PL) * 2))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((PL -i 1))) 0)))
  (P_set d1 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((PL *i 2) -i 1)))
      PL)))


/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, n :
  Nat, rsize : Nat, rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d1 ∧ d1 ≤ 15 ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELE_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Nat) (esize : Nat) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask : (BitVec ((Sail.Int.toNatChecked PL) * 2)) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked ((PL *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5701)
      (Sail.Int.toNatChecked ((PL *i 2))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
  let last : Bool := true
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (last, operand1, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := ((elements *i 2) -i 1)
    (do
      let mut loop_vars := (last, operand1, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (last, operand1, result) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5702) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__0 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__1 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__0 <b w__1) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__2 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__3 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__2 ≤b w__3) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let pbit : (BitVec 1) :=
            if (last : Bool)
            then 1#1
            else 0#1
          let w__4 ← (( do
            (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))) )
            : SailM (BitVec ((Sail.Int.toNatChecked PL) * 2)) )
          let result := (w__4 : (BitVec ((Sail.Int.toNatChecked PL) * 2)))
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((last, operand1, result)))
      (pure loop_vars)) ) : SailM
    (Bool × (BitVec rsize) × (BitVec ((Sail.Int.toNatChecked PL) * 2))) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d0 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((PL -i 1))) 0)))
  (P_set d1 PL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((PL *i 2) -i 1)))
      PL)))


end ArmFull.Functions
