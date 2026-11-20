module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1132
public import ArmFull.Fn.M1133 set_option backward.proofsInPublic true @[expose] public section

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

def decode_FCMLE_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Pd)
          let op : SVECmp := Cmp_LE
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMLE_P_P_Z0__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMLE_P_P_Z0__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMLE_P_P_Z0__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMLE_P_P_Z0__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMLE_P_P_Z0__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | _ => (pure (()))))


def decode_FCMEQ_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Pd)
          let op : SVECmp := Cmp_EQ
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMEQ_P_P_Z0__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMEQ_P_P_Z0__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMEQ_P_P_Z0__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMEQ_P_P_Z0__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMEQ_P_P_Z0__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | _ => (pure (()))))


def decode_FCMNE_P_P_Z0__ (size : (BitVec 2)) (eq : (BitVec 1)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Pd)
          let op : SVECmp := Cmp_NE
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_Z0__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_Z0__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_Z0__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_Z0__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FCMNE_P_P_Z0__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) op))
          | _ => (pure (()))))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FADDA_V_P_Z__ (VL : Nat) (dn : Nat) (esize : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read dn esize)) ) : SailM (BitVec esize) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec esize) := operand1
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
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                SailM (BitVec esize) )
              ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:1250.53-1250.54"
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              (FPAdd result element w__3))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec esize) )
  (V_set dn esize (Sail.BitVec.castWidth result))


def decode_FCVTZU_Z_P_Z_D2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let s_esize : Nat := 64
      let d_esize : Nat := 64
      let is_unsigned : Bool := true
      let rounding : FPRounding := FPRounding_ZERO
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2X 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2X 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2X 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_FCVTZU_Z_P_Z_D2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let s_esize : Nat := 64
      let d_esize : Nat := 32
      let is_unsigned : Bool := true
      let rounding : FPRounding := FPRounding_ZERO
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2W 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2W 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2W 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_D2W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_FCVTZU_Z_P_Z_S2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let s_esize : Nat := 32
      let d_esize : Nat := 32
      let is_unsigned : Bool := true
      let rounding : FPRounding := FPRounding_ZERO
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2W 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2W 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2W 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_FCVTZU_Z_P_Z_S2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let s_esize : Nat := 32
      let d_esize : Nat := 64
      let is_unsigned : Bool := true
      let rounding : FPRounding := FPRounding_ZERO
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2X 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2X 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2X 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZU_Z_P_Z_S2X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_FCVTZS_Z_P_Z_D2X (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let s_esize : Nat := 64
      let d_esize : Nat := 64
      let is_unsigned : Bool := false
      let rounding : FPRounding := FPRounding_ZERO
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2X 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2X 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2X 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2X 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2X 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_FCVTZS_Z_P_Z_D2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let s_esize : Nat := 64
      let d_esize : Nat := 32
      let is_unsigned : Bool := false
      let rounding : FPRounding := FPRounding_ZERO
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2W 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2W 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2W 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_D2W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_FCVTZS_Z_P_Z_S2W (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let s_esize : Nat := 32
      let d_esize : Nat := 32
      let is_unsigned : Bool := false
      let rounding : FPRounding := FPRounding_ZERO
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_S2W 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_S2W 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_S2W 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_S2W 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTZS_Z_P_Z_S2W 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


end ArmFull.Functions
