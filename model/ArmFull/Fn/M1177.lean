module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M1050
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1123 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize
  = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTX_Z_P_Z_D2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
              let res ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPConvertSVE
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) w__3
                  FPRounding_ODD d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend res esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTXNT_Z_P_Z_D2S (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
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
              let w__4 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPConvertSVE element w__3 FPRounding_ODD
                  (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM (BitVec (esize / 2)) )
              (Elem_set result ((2 *i e) +i 1) (Sail.Int.toNatChecked ((Int.ediv esize 2)))
                (Sail.BitVec.castWidth w__4)))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCLAMP_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5169)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:11265.49-11265.50"
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPMaxNum element1 element3 w__0) ) : SailM (BitVec esize) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (FPMinNum w__1 element2 w__2) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__3))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFADD_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5175)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFAdd (k_N := 16) element1 element2 w__0) ) : SailM (BitVec 16) )
          (Elem_set result e 16 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFMUL_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5176)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFMul (k_N := 16) element1 element2 w__0) ) : SailM (BitVec 16) )
          (Elem_set result e 16 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFSUB_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5177)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFSub (k_N := 16) element1 element2 w__0) ) : SailM (BitVec 16) )
          (Elem_set result e 16 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFADD_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5178)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do (BFAdd (k_N := 16) element1 element2 w__3) ) : SailM (BitVec 16) )
              (Elem_set result e 16 w__4))
          else
            (do
              (Elem_set result e 16 element1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMUL_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5179)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do (BFMul (k_N := 16) element1 element2 w__3) ) : SailM (BitVec 16) )
              (Elem_set result e 16 w__4))
          else
            (do
              (Elem_set result e 16 element1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFSUB_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5180)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do (BFSub (k_N := 16) element1 element2 w__3) ) : SailM (BitVec 16) )
              (Elem_set result e 16 w__4))
          else
            (do
              (Elem_set result e 16 element1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg :
  Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5181)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    (BFNeg (k_N := 16) element1))
                else (pure (element1)) ) : SailM (BitVec 16) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    (BFNeg (k_N := 16) element3))
                else (pure (element3)) ) : SailM (BitVec 16) )
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (BFMulAdd (k_N := 16) element3 element1 element2 w__7) ) : SailM
                (BitVec 16) )
              (Elem_set result e 16 w__8))
          else
            (do
              let w__10 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              (Elem_set result e 16 w__10))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg :
  Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLS_Z_P_ZZZ__ (VL : Nat) (da : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5182)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    (BFNeg (k_N := 16) element1))
                else (pure (element1)) ) : SailM (BitVec 16) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    (BFNeg (k_N := 16) element3))
                else (pure (element3)) ) : SailM (BitVec 16) )
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (BFMulAdd (k_N := 16) element3 element1 element2 w__7) ) : SailM
                (BitVec 16) )
              (Elem_set result e 16 w__8))
          else
            (do
              let w__10 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
              (Elem_set result e 16 w__10))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLA_Z_ZZZi_H (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 16)))
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
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
          let element3 ← (( do (Elem_read result e 16) ) : SailM (BitVec 16) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (BFNeg (k_N := 16) element1))
            else (pure (element1)) ) : SailM (BitVec 16) )
          let element3 ← (( do
            if (op3_neg : Bool)
            then
              (do
                (BFNeg (k_N := 16) element3))
            else (pure (element3)) ) : SailM (BitVec 16) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (BFMulAdd (k_N := 16) element3 element1 element2 w__2) ) : SailM
            (BitVec 16) )
          (Elem_set result e 16 w__3)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, index : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMLS_Z_ZZZi_H (VL : Nat) (da : Nat) (index : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 16)))
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
          let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
          let s : Int := (segmentbase +i index)
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
          let element3 ← (( do (Elem_read result e 16) ) : SailM (BitVec 16) )
          let element1 ← (( do
            if (op1_neg : Bool)
            then
              (do
                (BFNeg (k_N := 16) element1))
            else (pure (element1)) ) : SailM (BitVec 16) )
          let element3 ← (( do
            if (op3_neg : Bool)
            then
              (do
                (BFNeg (k_N := 16) element3))
            else (pure (element3)) ) : SailM (BitVec 16) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (BFMulAdd (k_N := 16) element3 element1 element2 w__2) ) : SailM
            (BitVec 16) )
          (Elem_set result e 16 w__3)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, index : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem index [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFMUL_Z_ZZi_H (VL : Nat) (d : Nat) (index : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 16)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5183)
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
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 s 16) ) : SailM (BitVec 16) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFMul (k_N := 16) element1 element2 w__0) ) : SailM (BitVec 16) )
          (Elem_set result e 16 w__1)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAXNM_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5184)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do (BFMaxNum (k_N := 16) element1 element2 w__3) ) : SailM (BitVec 16)
                )
              (Elem_set result e 16 w__4))
          else
            (do
              (Elem_set result e 16 element1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
