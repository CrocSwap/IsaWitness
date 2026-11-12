import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0118
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP1_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let base : Nat := (Sail.Int.toNatChecked ((part *i pairs)))
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (base +i p) esize)) )
            : SailM (BitVec esize) )
          let w__1 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__0)) )
            : SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (base +i p) esize)) )
            : SailM (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP2_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let base : Int := (part *i pairs)
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (base +i p) esize)) )
            : SailM (BitVec esize) )
          let w__1 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__0)) )
            : SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (base +i p) esize)) )
            : SailM (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, csize : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m :
  Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ dn ∧ dn ≤ 31 ∧ List.elem csize [32, 64] ∧ (is_VL VL) -/
def execute_CLASTA_R_P_Z__ (VL : Nat) (csize : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn esize)) ) : SailM (BitVec esize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5395)
      (Sail.Int.toNatChecked (csize)))) ) : SailM (BitVec csize) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then
      (do
        ArmFull.assert ((esize ≥b 0) && (csize ≥b esize)) "sail-arm/instrs64_sve.sail:27154.59-27154.60"
        let result : (BitVec csize) :=
          (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend operand1 csize))
        (pure (result)))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last : Int := last
        ArmFull.assert ((esize ≥b 0) && (csize ≥b esize)) "sail-arm/instrs64_sve.sail:27165.59-27165.60"
        let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 last esize)) ) : SailM
          (BitVec esize) )
        let result := ((Sail.BitVec.castWidth (Sail.BitVec.zeroExtend w__0 csize)) : (BitVec csize))
        (pure (result))) ) : SailM (BitVec csize) )
  (X_set dn csize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, csize : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m :
  Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧
  0 ≤ dn ∧ dn ≤ 31 ∧ List.elem csize [32, 64] ∧ (is_VL VL) -/
def execute_CLASTB_R_P_Z__ (VL : Nat) (csize : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read dn esize)) ) : SailM (BitVec esize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5396)
      (Sail.Int.toNatChecked (csize)))) ) : SailM (BitVec csize) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then
      (do
        ArmFull.assert ((esize ≥b 0) && (csize ≥b esize)) "sail-arm/instrs64_sve.sail:27229.59-27229.60"
        let result : (BitVec csize) :=
          (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend operand1 csize))
        (pure (result)))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last : Int := last
        ArmFull.assert ((esize ≥b 0) && (csize ≥b esize)) "sail-arm/instrs64_sve.sail:27240.59-27240.60"
        let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 last esize)) ) : SailM
          (BitVec esize) )
        let result := ((Sail.BitVec.castWidth (Sail.BitVec.zeroExtend w__0 csize)) : (BitVec csize))
        (pure (result))) ) : SailM (BitVec csize) )
  (X_set dn csize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m
  ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CLASTA_V_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read dn esize)) ) : SailM (BitVec esize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5397)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then
      (let result : (BitVec esize) :=
        (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend operand1 esize))
      (pure (result)))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last : Int := last
        ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 last esize))) ) : SailM (BitVec esize) )
  (V_set dn esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m
  ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CLASTB_V_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read dn esize)) ) : SailM (BitVec esize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5398)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then
      (let result : (BitVec esize) :=
        (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend operand1 esize))
      (pure (result)))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last : Int := last
        ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 last esize))) ) : SailM (BitVec esize) )
  (V_set dn esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m
  ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CLASTA_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5399)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then (pure (operand1))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last : Int := last
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars
            loop_vars ← do
              let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 last esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__0))
          (pure loop_vars))) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, k_isBefore : Bool, m : Nat, 0 ≤ m
  ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_CLASTB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (isBefore : Bool) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5400)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let last ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let result ← (( do
    if ((last <b 0) : Bool)
    then (pure (operand1))
    else
      (do
        let last : Int :=
          if ((! isBefore) : Bool)
          then
            (let last : Int := (last +i 1)
            if ((last ≥b elements) : Bool)
            then 0
            else last)
          else last
        let last : Int := last
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars
            loop_vars ← do
              let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 last esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__0))
          (pure loop_vars))) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, s1 : Nat, s2 : Nat, v : Nat, List.elem v
  [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ s2 ∧
  s2 ≤ 31 ∧
  0 ≤ s1 ∧
  s1 ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_SPLICE_Z_P_ZZ_Des (VL : Nat) (dst : Nat) (esize : Nat) (s1 : Nat) (s2 : Nat) (v : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read v PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read s1 VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s2 VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5401)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let x : Int := 0
  let active : Bool := false
  let lastnum ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let (result, x) ← (( do
    if ((lastnum ≥b 0) : Bool)
    then
      (do
        let (active, result, x) ← (( do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := lastnum
          (do
            let mut loop_vars := (active, result, x)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (active, result, x) := loop_vars
              loop_vars ← do
                let w__3 ← (( do
                  if ((active : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      (ActivePredicateElement mask e esize)) ) : SailM Bool )
                let active := (w__3 : Bool)
                let (result, x) ← (( do
                  if (active : Bool)
                  then
                    (do
                      let x : Int := x
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                        ) : SailM (BitVec esize) )
                      let w__5 ← (( do (Elem_set result x esize (Sail.BitVec.castWidth w__4)) ) :
                        SailM (BitVec VL) )
                      let result := (w__5 : (BitVec VL))
                      let x : Int := (x +i 1)
                      (pure ((result, x))))
                  else (pure ((result, x))) ) : SailM ((BitVec VL) × Int) )
                (pure ((active, result, x)))
            (pure loop_vars)) ) : SailM (Bool × (BitVec VL) × Int) )
        (pure ((result, x))))
    else (pure ((result, x))) ) : SailM ((BitVec VL) × Int) )
  let nelements : Int := ((elements -i x) -i 1)
  let (result, x) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := nelements
    (do
      let mut loop_vars := (result, x)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (result, x) := loop_vars
        loop_vars ← do
          let x : Int := x
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__7 ← (( do (Elem_set result x esize (Sail.BitVec.castWidth w__6)) ) : SailM
            (BitVec VL) )
          let result := (w__7 : (BitVec VL))
          let x : Int := (x +i 1)
          (pure ((result, x)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (Z_set dst VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, s1 : Nat, s2 : Int, v : Nat, List.elem v
  [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ s1 ∧
  s1 ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_SPLICE_Z_P_ZZ_Con (VL : Nat) (dst : Nat) (esize : Nat) (s1 : Nat) (s2 : Int) (v : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read v PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read s1 VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s2 VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5402)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let x : Int := 0
  let active : Bool := false
  let lastnum ← (( do (LastActiveElement mask esize) ) : SailM Int )
  let (result, x) ← (( do
    if ((lastnum ≥b 0) : Bool)
    then
      (do
        let (active, result, x) ← (( do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := lastnum
          (do
            let mut loop_vars := (active, result, x)
            for e in [loop_e_lower:loop_e_upper:1]i do
              let (active, result, x) := loop_vars
              loop_vars ← do
                let w__3 ← (( do
                  if ((active : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      (ActivePredicateElement mask e esize)) ) : SailM Bool )
                let active := (w__3 : Bool)
                let (result, x) ← (( do
                  if (active : Bool)
                  then
                    (do
                      let x : Int := x
                      let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                        ) : SailM (BitVec esize) )
                      let w__5 ← (( do (Elem_set result x esize (Sail.BitVec.castWidth w__4)) ) :
                        SailM (BitVec VL) )
                      let result := (w__5 : (BitVec VL))
                      let x : Int := (x +i 1)
                      (pure ((result, x))))
                  else (pure ((result, x))) ) : SailM ((BitVec VL) × Int) )
                (pure ((active, result, x)))
            (pure loop_vars)) ) : SailM (Bool × (BitVec VL) × Int) )
        (pure ((result, x))))
    else (pure ((result, x))) ) : SailM ((BitVec VL) × Int) )
  let nelements : Int := ((elements -i x) -i 1)
  let (result, x) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := nelements
    (do
      let mut loop_vars := (result, x)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (result, x) := loop_vars
        loop_vars ← do
          let x : Int := x
          let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let w__7 ← (( do (Elem_set result x esize (Sail.BitVec.castWidth w__6)) ) : SailM
            (BitVec VL) )
          let result := (w__7 : (BitVec VL))
          let x : Int := (x +i 1)
          (pure ((result, x)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (Z_set dst VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, position__arg : Nat, s1 : Nat, s2 : Nat, 0
  ≤ s2 ∧
  s2 ≤ 31 ∧
  0 ≤ s1 ∧
  s1 ≤ 31 ∧
  0 ≤ position__arg ∧
  position__arg ≤ 255 ∧ esize = 8 ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_EXT_Z_ZI_Des (VL : Nat) (dst : Nat) (esize : Nat) (position__arg : Nat) (s1 : Nat) (s2 : Nat) : SailM Unit := do
  let position : Int := position__arg
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s1 VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s2 VL)) ) : SailM (BitVec VL) )
  let position : Int :=
    if ((position ≥b elements) : Bool)
    then 0
    else position
  let position : Int := (Int.shiftl position 3)
  let concat : (BitVec (VL * 2)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  ArmFull.assert ((0 ≤b (Sail.Int.toNatChecked (position))) && ((((Sail.Int.toNatChecked (position)) +i VL) -i 1) <b (VL *i 2))) "sail-arm/instrs64_sve.sail:27842.71-27842.72"
  let result : (BitVec VL) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb concat
      (Sail.Int.toNatChecked ((((Sail.Int.toNatChecked (position)) +i VL) -i 1)))
      (Sail.Int.toNatChecked ((Sail.Int.toNatChecked (position))))))
  (Z_set dst VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dst : Nat, esize : Nat, position__arg : Nat, s1 : Nat, s2 : Int, 0
  ≤ s1 ∧
  s1 ≤ 31 ∧
  0 ≤ position__arg ∧
  position__arg ≤ 255 ∧ esize = 8 ∧ 0 ≤ dst ∧ dst ≤ 31 ∧ (is_VL VL) -/
def execute_EXT_Z_ZI_Con (VL : Nat) (dst : Nat) (esize : Nat) (position__arg : Nat) (s1 : Nat) (s2 : Int) : SailM Unit := do
  let position : Int := position__arg
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s1 VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read s2 VL)) ) : SailM (BitVec VL) )
  let position : Int :=
    if ((position ≥b elements) : Bool)
    then 0
    else position
  let position : Int := (Int.shiftl position 3)
  let concat : (BitVec (VL * 2)) := (Sail.BitVec.castWidth (operand2 +++ operand1))
  ArmFull.assert ((0 ≤b (Sail.Int.toNatChecked (position))) && ((((Sail.Int.toNatChecked (position)) +i VL) -i 1) <b (VL *i 2))) "sail-arm/instrs64_sve.sail:27905.71-27905.72"
  let result : (BitVec VL) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb concat
      (Sail.Int.toNatChecked ((((Sail.Int.toNatChecked (position)) +i VL) -i 1)))
      (Sail.Int.toNatChecked ((Sail.Int.toNatChecked (position))))))
  (Z_set dst VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CPY_Z_P_R__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let result ← (( do
    if (w__0 : Bool)
    then
      (do
        let operand1 ← (( do (undefined_bitvector_at (← occLabel 5403) 64) ) : SailM (BitVec 64)
          )
        let operand1 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let loop_e_lower : Nat := 0
        let loop_e_upper : Int := (elements -i 1)
        (do
          let mut loop_vars := result
          for e in [loop_e_lower:loop_e_upper:1]i do
            let result := loop_vars
            loop_vars ← do
              let w__3 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
              if (w__3 : Bool)
              then
                (do
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb operand1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0))))
              else (pure (result))
          (pure loop_vars)))
    else (pure (result)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CPY_Z_P_V__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (V_read n esize)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := esize))))) ) : SailM (BitVec esize) )
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
              (Elem_set result e esize (Sail.BitVec.castWidth operand1)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
