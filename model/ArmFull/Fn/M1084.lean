import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
import ArmFull.Fn.M1040
import ArmFull.Fn.M1044

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

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_W2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let fpval ← (( do
                ((Sail.BitVec.castWidth ) <$> (FixedToFP
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend fpval esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UCVTF_Z_P_Z_W2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let fpval ← (( do
                ((Sail.BitVec.castWidth ) <$> (FixedToFP
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend fpval esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_X2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let fpval ← (( do
                ((Sail.BitVec.castWidth ) <$> (FixedToFP
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend fpval esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_X2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let fpval ← (( do
                ((Sail.BitVec.castWidth ) <$> (FixedToFP
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend fpval esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_W2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let fpval ← (( do
                ((Sail.BitVec.castWidth ) <$> (FixedToFP
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend fpval esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, n
  : Nat, s_esize : Nat, s_esize = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SCVTF_Z_P_Z_W2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (rounding : FPRounding) (s_esize : Nat) (is_unsigned : Bool) : SailM Unit := do
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
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let fpval ← (( do
                ((Sail.BitVec.castWidth ) <$> (FixedToFP
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) 0
                  is_unsigned w__3 rounding d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend fpval esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FACGE_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5068)
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
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5069) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5665.59-5665.60"
                    let w__5 ← (( do (FPAbs element1) ) : SailM (BitVec esize) )
                    let w__6 ← (( do (FPAbs element2) ) : SailM (BitVec esize) )
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE w__5 w__6 w__7))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5669.59-5669.60"
                    let w__9 ← (( do (FPAbs element1) ) : SailM (BitVec esize) )
                    let w__10 ← (( do (FPAbs element2) ) : SailM (BitVec esize) )
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT w__9 w__10 w__11))
                | _ => (pure (res)) ) : SailM Bool )
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FACGT_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5070)
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
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5071) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5756.59-5756.60"
                    let w__5 ← (( do (FPAbs element1) ) : SailM (BitVec esize) )
                    let w__6 ← (( do (FPAbs element2) ) : SailM (BitVec esize) )
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE w__5 w__6 w__7))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5760.59-5760.60"
                    let w__9 ← (( do (FPAbs element1) ) : SailM (BitVec esize) )
                    let w__10 ← (( do (FPAbs element2) ) : SailM (BitVec esize) )
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT w__9 w__10 w__11))
                | _ => (pure (res)) ) : SailM Bool )
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMUO_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5072)
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
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5073) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5847.59-5847.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element1 element2 w__5))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5851.59-5851.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element1 element2 w__7))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5855.59-5855.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element1 element2 w__9))
                | .Cmp_UN =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5859.59-5859.60"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareUN element1 element2 w__11))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5863.59-5863.60"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element1 element2 w__13))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5867.59-5867.60"
                    let w__15 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element2 element1 w__15))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5871.59-5871.60"
                    let w__17 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element2 element1 w__17)) ) : SailM Bool )
              let res := res
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_FCMGE_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op : SVECmp) : SailM Unit := do
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
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5074)
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
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              let res ← (( do (undefined_bool_at (← occLabel 5075) ()) ) : SailM Bool )
              let res ← (( do
                match op with
                | .Cmp_EQ =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5958.59-5958.60"
                    let w__5 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareEQ element1 element2 w__5))
                | .Cmp_GE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5962.59-5962.60"
                    let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element1 element2 w__7))
                | .Cmp_GT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5966.59-5966.60"
                    let w__9 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element1 element2 w__9))
                | .Cmp_UN =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5970.59-5970.60"
                    let w__11 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareUN element1 element2 w__11))
                | .Cmp_NE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5974.59-5974.60"
                    let w__13 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareNE element1 element2 w__13))
                | .Cmp_LT =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5978.59-5978.60"
                    let w__15 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGT element2 element1 w__15))
                | .Cmp_LE =>
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:5982.59-5982.60"
                    let w__17 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    (FPCompareGE element2 element1 w__17)) ) : SailM Bool )
              let res := res
              let pbit : (BitVec 1) :=
                if (res : Bool)
                then 1#1
                else 0#1
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth result))


end ArmFull.Functions
