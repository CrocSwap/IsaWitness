module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0866 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2
  = 1 ∧
  sel1 = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLALBT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
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
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 : Int := (BitVec.toInt w__0)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 : Int := (BitVec.toInt w__1)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat ((2 *i element1) *i element2) esize)) ) : SailM
            (BitVec esize) )
          let product : Int := (BitVec.toInt w__3)
          let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat (element3 +i product) esize))
            ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__4))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, m : Nat, n : Nat, sel1 : Nat, sel2 : Nat, sel2
  = 1 ∧
  sel1 = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQDMLSLBT_Z_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sel1 : Nat) (sel2 : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
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
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i e) +i sel1)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element1 : Int := (BitVec.toInt w__0)
          let w__1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i e) +i sel2)
              (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
          let element2 : Int := (BitVec.toInt w__1)
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat ((2 *i element1) *i element2) esize)) ) : SailM
            (BitVec esize) )
          let product : Int := (BitVec.toInt w__3)
          let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat (element3 -i product) esize))
            ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__4))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMULH_Z_ZZi_H (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5609)
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
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMULH_Z_ZZi_S (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5610)
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
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMULH_Z_ZZi_D (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5611)
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
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLAH_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5612)
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
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let res : Int := ((Int.shiftl element3 esize) +i ((2 *i element1) *i element2))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLAH_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5613)
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
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let res : Int := ((Int.shiftl element3 esize) +i ((2 *i element1) *i element2))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLAH_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5614)
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
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let res : Int := ((Int.shiftl element3 esize) +i ((2 *i element1) *i element2))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLSH_Z_ZZZi_H (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5615)
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
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let res : Int := ((Int.shiftl element3 esize) -i ((2 *i element1) *i element2))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLSH_Z_ZZZi_S (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5616)
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
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let res : Int := ((Int.shiftl element3 esize) -i ((2 *i element1) *i element2))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ List.elem index [0, 1] ∧ esize = 64 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_SQRDMLSH_Z_ZZZi_D (VL : Nat) (da : Nat) (esize : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5617)
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
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) : SailM
            (BitVec esize) )
          let element3 : Int := (BitVec.toInt w__2)
          let res : Int := ((Int.shiftl element3 esize) -i ((2 *i element1) *i element2))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (SignedSat
              (Int.shiftr (res +i (Int.shiftl 1 (Sail.Int.toNatChecked ((esize -i 1))))) esize)
              esize)) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SHADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5618)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := (BitVec.toInt w__2)
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := (BitVec.toInt w__3)
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let res : Int := (Int.shiftr (element1 +i element2) 1)
              (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))))
          else
            (do
              let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__6)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SHSUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5619)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := (BitVec.toInt w__2)
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := (BitVec.toInt w__3)
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let res : Int := (Int.shiftr (element1 -i element2) 1)
              (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))))
          else
            (do
              let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__6)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SHSUBR_Z_P_ZZ__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
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
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5620)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) : SailM
            (BitVec esize) )
          let element1 : Int := (BitVec.toInt w__2)
          let w__3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) : SailM
            (BitVec esize) )
          let element2 : Int := (BitVec.toInt w__3)
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let res : Int := (Int.shiftr (element2 -i element1) 1)
              (Elem_set result e esize (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))))
          else
            (do
              let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__6)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
