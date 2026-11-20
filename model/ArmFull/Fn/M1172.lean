module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M1092
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1136 set_option backward.proofsInPublic true @[expose] public section

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

def decode_FCMNE_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (cmph : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (cmpl : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let d : Int := (BitVec.toNat Pd)
          let op : SVECmp := Cmp_NE
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_ZZ__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_ZZ__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_ZZ__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op))
          | _ => (pure (()))))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5082)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6409.57-6409.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6413.57-6413.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6416.53-6416.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FMLS_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5083)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6497.57-6497.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6501.57-6501.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6504.53-6504.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FNMLA_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5084)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6585.57-6585.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6589.57-6589.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6592.53-6592.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, da : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_FNMLS_Z_P_ZZZ__ (VL : Nat) (da : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5085)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6676.57-6676.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6680.57-6680.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6683.53-6683.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set da VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FMAD_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand3 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read a VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5086)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6767.57-6767.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6771.57-6771.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6774.53-6774.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FMSB_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand3 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read a VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5087)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6858.57-6858.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6862.57-6862.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6865.53-6865.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FNMAD_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand3 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read a VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5088)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6949.57-6949.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6953.57-6953.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:6956.53-6956.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, k_op1_neg : Bool, k_op3_neg
  : Bool, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ 0 ≤ a ∧ a ≤ 31 ∧ (is_VL VL) -/
def execute_FNMSB_Z_P_ZZZ__ (VL : Nat) (a : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) (op1_neg : Bool) (op3_neg : Bool) : SailM Unit := do
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
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand3 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read a VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5089)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
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
              let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize)) ) :
                SailM (BitVec esize) )
              let element1 ← (( do
                if (op1_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:7040.57-7040.58"
                    (FPNeg element1))
                else (pure (element1)) ) : SailM (BitVec esize) )
              let element3 ← (( do
                if (op3_neg : Bool)
                then
                  (do
                    ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:7044.57-7044.58"
                    (FPNeg element3))
                else (pure (element3)) ) : SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:7047.53-7047.54"
              let w__7 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__8 ← (( do (FPMulAdd element3 element1 element2 w__7) ) : SailM (BitVec esize)
                )
              (Elem_set result e esize (Sail.BitVec.castWidth w__8)))
          else
            (do
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth w__10)))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
