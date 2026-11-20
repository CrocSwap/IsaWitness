module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5711)
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
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQRSHRUN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5712)
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
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toInt element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, shift : Int, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQRSHRN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (shift : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5713)
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
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let element ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let res : Int :=
                  (_shr_int_general ((BitVec.toNat element) +i (_shl_int_general 1 (shift -i 1)))
                    shift)
                let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat res esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__0))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5714)
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
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (SignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SQCVTUN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5715)
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
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toInt w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UQCVTN_Z_MZ2__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((2 *i esize))))))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5716)
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
          let loop_i_upper : Nat := 1
          (do
            let mut loop_vars_1 := result
            for i in [loop_i_lower:loop_i_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i i) VL)) ) : SailM
                  (BitVec VL) )
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
                    (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
                let element : Int := (BitVec.toNat w__0)
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (UnsignedSat element esize)) ) :
                  SailM (BitVec esize) )
                (Elem_set result ((2 *i e) +i i) esize (Sail.BitVec.castWidth w__1))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, index : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ index ∧
  index ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_DUPQ_Z_Zi__ (VL : Nat) (d : Nat) (esize : Nat) (index : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5717)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5718)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (element, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand ((s *i elements) +i index) esize)) ) :
            SailM (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let w__1 ← (( do
            (Elem_set result s 128
              (Sail.BitVec.castWidth (BitVec.replicateBits element
                (Sail.Int.toNatChecked ((Int.ediv 128 esize)))))) ) : SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec VL)) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, m : Nat, position : Int, 0 ≤ m ∧
  m ≤ 31 ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_EXTQ_Z_ZI_Des (VL : Nat) (dn : Nat) (m : Nat) (position : Int) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5720)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
          let w__1 ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
          let concat : (BitVec 256) := (w__0 +++ w__1)
          ArmFull.assert ((0 ≤b position) && ((position +i 127) <b 256)) "sail-inputs/16-instrs64_sve.sail:54880.67-54880.68"
          (Elem_set result s 128
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb concat
              (Sail.Int.toNatChecked ((position +i 127))) (Sail.Int.toNatChecked (position)))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TBLQ_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5721)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((s *i elements) +i e) esize)) )
                  : SailM (BitVec esize) )
                let idx : Int := (BitVec.toNat w__0)
                if ((idx <b elements) : Bool)
                then
                  (do
                    let w__1 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((s *i elements) +i idx)
                        esize)) ) : SailM (BitVec esize) )
                    (Elem_set result ((s *i elements) +i e) esize (Sail.BitVec.castWidth w__1)))
                else
                  (do
                    (Elem_set result ((s *i elements) +i e) esize
                      (Sail.BitVec.castWidth (Zeros (n := esize)))))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TBXQ_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := result
            for e in [loop_e_lower:loop_e_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((s *i elements) +i e) esize)) )
                  : SailM (BitVec esize) )
                let idx : Int := (BitVec.toNat w__0)
                if ((idx <b elements) : Bool)
                then
                  (do
                    let w__1 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((s *i elements) +i idx)
                        esize)) ) : SailM (BitVec esize) )
                    (Elem_set result ((s *i elements) +i e) esize (Sail.BitVec.castWidth w__1)))
                else (pure (result))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZPQ1_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let pairs : Int := (Int.ediv elements 2)
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5722)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let result ← (( do
            let loop_p_lower : Nat := 0
            let loop_p_upper : Int := (pairs -i 1)
            (do
              let mut loop_vars_1 := result
              for p in [loop_p_lower:loop_p_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1
                      (((s *i elements) +i (2 *i p)) +i part) esize)) ) : SailM (BitVec esize) )
                  (Elem_set result ((s *i elements) +i p) esize (Sail.BitVec.castWidth w__0))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let loop_p_lower : Nat := 0
          let loop_p_upper : Int := (pairs -i 1)
          (do
            let mut loop_vars_1 := result
            for p in [loop_p_lower:loop_p_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                    (((s *i elements) +i (2 *i p)) +i part) esize)) ) : SailM (BitVec esize) )
                (Elem_set result (((s *i elements) +i pairs) +i p) esize
                  (Sail.BitVec.castWidth w__2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZPQ2_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let pairs : Int := (Int.ediv elements 2)
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5723)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let result ← (( do
            let loop_p_lower : Nat := 0
            let loop_p_upper : Int := (pairs -i 1)
            (do
              let mut loop_vars_1 := result
              for p in [loop_p_lower:loop_p_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read operand1
                      (((s *i elements) +i (2 *i p)) +i part) esize)) ) : SailM (BitVec esize) )
                  (Elem_set result ((s *i elements) +i p) esize (Sail.BitVec.castWidth w__0))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let loop_p_lower : Nat := 0
          let loop_p_upper : Int := (pairs -i 1)
          (do
            let mut loop_vars_1 := result
            for p in [loop_p_lower:loop_p_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2
                    (((s *i elements) +i (2 *i p)) +i part) esize)) ) : SailM (BitVec esize) )
                (Elem_set result (((s *i elements) +i pairs) +i p) esize
                  (Sail.BitVec.castWidth w__2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIPQ1_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let pairs : Int := (Int.ediv elements 2)
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5724)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let base : Int := ((s *i elements) +i (part *i pairs))
          let loop_p_lower : Nat := 0
          let loop_p_upper : Int := (pairs -i 1)
          (do
            let mut loop_vars_1 := result
            for p in [loop_p_lower:loop_p_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (base +i p) esize)) ) : SailM
                  (BitVec esize) )
                let w__1 ← (( do
                  (Elem_set result (((s *i elements) +i (2 *i p)) +i 0) esize
                    (Sail.BitVec.castWidth w__0)) ) : SailM (BitVec VL) )
                let result := (w__1 : (BitVec VL))
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (base +i p) esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result (((s *i elements) +i (2 *i p)) +i 1) esize
                  (Sail.BitVec.castWidth w__2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIPQ2_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let pairs : Int := (Int.ediv elements 2)
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5725)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := result
      for s in [loop_s_lower:loop_s_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let base : Int := ((s *i elements) +i (part *i pairs))
          let loop_p_lower : Nat := 0
          let loop_p_upper : Int := (pairs -i 1)
          (do
            let mut loop_vars_1 := result
            for p in [loop_p_lower:loop_p_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (base +i p) esize)) ) : SailM
                  (BitVec esize) )
                let w__1 ← (( do
                  (Elem_set result (((s *i elements) +i (2 *i p)) +i 0) esize
                    (Sail.BitVec.castWidth w__0)) ) : SailM (BitVec VL) )
                let result := (w__1 : (BitVec VL))
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (base +i p) esize)) ) : SailM
                  (BitVec esize) )
                (Elem_set result (((s *i elements) +i (2 *i p)) +i 1) esize
                  (Sail.BitVec.castWidth w__2))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
