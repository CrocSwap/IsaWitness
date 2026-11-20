module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0605
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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧
  List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_PMOV_Z_PI_D (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5737)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    if ((imm == 0) : Bool)
    then
      (let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
      (pure (result)))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read d VL))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__1 ← (( do (PredicateElement operand e esize) ) : SailM (BitVec 1) )
          let result :=
            ((BitVec.update result (Sail.Int.toNatChecked (((elements *i imm) +i e))) (Bit w__1)) : (BitVec VL))
          (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ imm = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PMOV_P_ZI_B (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5738)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          (Elem_set result e psize
            (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand
                  (Sail.Int.toNatChecked (((elements *i imm) +i e))))])) psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem imm [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PMOV_P_ZI_H (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5739)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          (Elem_set result e psize
            (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand
                  (Sail.Int.toNatChecked (((elements *i imm) +i e))))])) psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem imm [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PMOV_P_ZI_S (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5740)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          (Elem_set result e psize
            (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand
                  (Sail.Int.toNatChecked (((elements *i imm) +i e))))])) psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, imm : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PMOV_P_ZI_D (VL : Nat) (d : Nat) (esize : Nat) (imm : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5741)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          (Elem_set result e psize
            (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand
                  (Sail.Int.toNatChecked (((elements *i imm) +i e))))])) psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, part : Nat, List.elem part
  [0, 1, 2, 3] ∧
  0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PEXT_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i 4))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 4)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5742)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let pbit ← (( do (PredicateElement mask ((part *i elements) +i e) esize) ) : SailM
            (BitVec 1) )
          (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d0 : Nat, d1 : Int, esize : Nat, n : Nat, part : Nat, List.elem part
  [0, 1] ∧
  0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d0 ∧ d0 ≤ 15 ∧ (is_VL VL) -/
def execute_PEXT_PP_RR__ (VL : Nat) (d0 : Nat) (d1 : Int) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i 4))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 4)) )
  let result0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5743)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5744)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result0 ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result0
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result0 := loop_vars
        loop_vars ← do
          let pbit ← (( do (PredicateElement mask (((part *i 2) *i elements) +i e) esize) ) :
            SailM (BitVec 1) )
          (Elem_set result0 e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let result1 ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result1
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result1 := loop_vars
        loop_vars ← do
          let pbit ← (( do
            (PredicateElement mask ((((part *i 2) *i elements) +i elements) +i e) esize) ) : SailM
            (BitVec 1) )
          (Elem_set result1 e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d0 PL (Sail.BitVec.castWidth result0))
  (P_set d1 PL (Sail.BitVec.castWidth result1))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, List.elem esize [8, 16, 32, 64] ∧
  0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PTRUE_PN_I__ (VL : Nat) (d : Nat) (esize : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements elements false PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, width : Nat, List.elem width [2, 4]
  ∧
  0 ≤ n ∧ n ≤ 15 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_CNTP_R_PN__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let pred ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask ← (( do
    ((Sail.BitVec.castWidth ) <$> (CounterToPredicate (Sail.BitVec.extractLsb pred 15 0)
      (Sail.Int.toNatChecked ((PL *i 4))))) ) : SailM (BitVec ((Sail.Int.toNatChecked PL) * 4)) )
  let sum : (BitVec 64) := (Zeros (n := 64))
  let limit : Int := (elements *i width)
  let sum ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (limit -i 1)
    (do
      let mut loop_vars := sum
      for e in [loop_e_lower:loop_e_upper:1]i do
        let sum := loop_vars
        loop_vars ← do
          let w__1 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let sum : (BitVec 64) :=
            if (w__1 : Bool)
            then (BitVec.addInt sum 1)
            else sum
          (pure (sum))
      (pure loop_vars)) ) : SailM (BitVec 64) )
  (X_set d 64 sum)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELO_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5745) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 <b w__2) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≤b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELS_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5746) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 <b w__2) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≤b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELT_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5747) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 <b w__2) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≤b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILELE_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5748) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_LT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 <b w__2) : Bool)
                (pure (cond)))
            | .Cmp_LE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≤b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.addInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_invert : Bool, k_is_unsigned : Bool, m : Nat, n
  : Nat, rsize : Nat, width : Nat, List.elem width [2, 4] ∧
  rsize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_WHILEHI_PN_RR__ (VL : Nat) (d : Nat) (esize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : SVECmp) (rsize : Nat) (is_unsigned : Bool) (width : Nat) : SailM Unit := do
  let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (CheckSVEEnabled ()))
  else
    (do
      (CheckStreamingSVEEnabled ()))
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((width *i (Int.ediv VL esize))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n rsize)) ) : SailM (BitVec rsize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m rsize)) ) : SailM (BitVec rsize) )
  let last : Bool := true
  let count : Int := 0
  let (count, last, operand1) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (count, last, operand1)
      for e in [loop_e_upper:loop_e_lower:-1]i do
        let (count, last, operand1) := loop_vars
        loop_vars ← do
          let cond ← (( do (undefined_bool_at (← occLabel 5749) ()) ) : SailM Bool )
          let cond ← (( do
            match op with
            | .Cmp_GT =>
              (do
                let w__1 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__1 >b w__2) : Bool)
                (pure (cond)))
            | .Cmp_GE =>
              (do
                let w__3 ← (( do (asl_Int operand1 is_unsigned) ) : SailM Int )
                let w__4 ← (( do (asl_Int operand2 is_unsigned) ) : SailM Int )
                let cond := ((w__3 ≥b w__4) : Bool)
                (pure (cond)))
            | _ => (pure (cond)) ) : SailM Bool )
          let last : Bool := (last && cond)
          let count : Int :=
            if (last : Bool)
            then (count +i 1)
            else count
          let operand1 : (BitVec rsize) := (BitVec.subInt operand1 1)
          (pure ((count, last, operand1)))
      (pure loop_vars)) ) : SailM (Int × Bool × (BitVec rsize)) )
  let count : Int := count
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (EncodePredCount esize elements count invert PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredCountTest elements count invert) ) : SailM (BitVec 4) )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


end ArmFull.Functions
