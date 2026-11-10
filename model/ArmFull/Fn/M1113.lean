import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0147
import ArmFull.Fn.M0178
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0840
import ArmFull.Fn.M1072
import ArmFull.Fn.M1082
import ArmFull.Fn.M1083

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

def decode_SCVTF_Z_P_Z_H2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 16
  let d_esize : Nat := 16
  let is_unsigned : Bool := false
  let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_SCVTF_Z_P_Z_H2FP16 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_SCVTF_Z_P_Z_H2FP16 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_SCVTF_Z_P_Z_H2FP16 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_SCVTF_Z_P_Z_H2FP16 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_SCVTF_Z_P_Z_H2FP16 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_SCVTF_Z_P_Z_W2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 32
  let d_esize : Nat := 16
  let is_unsigned : Bool := false
  let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_SCVTF_Z_P_Z_W2FP16 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_SCVTF_Z_P_Z_W2FP16 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_SCVTF_Z_P_Z_W2FP16 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_SCVTF_Z_P_Z_W2FP16 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_SCVTF_Z_P_Z_W2FP16 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_SCVTF_Z_P_Z_X2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 64
  let d_esize : Nat := 16
  let is_unsigned : Bool := false
  let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_SCVTF_Z_P_Z_X2FP16 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_SCVTF_Z_P_Z_X2FP16 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_SCVTF_Z_P_Z_X2FP16 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_SCVTF_Z_P_Z_X2FP16 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_SCVTF_Z_P_Z_X2FP16 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_UCVTF_Z_P_Z_H2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 16
  let d_esize : Nat := 16
  let is_unsigned : Bool := true
  let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_UCVTF_Z_P_Z_H2FP16 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_UCVTF_Z_P_Z_H2FP16 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_UCVTF_Z_P_Z_H2FP16 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_UCVTF_Z_P_Z_H2FP16 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_UCVTF_Z_P_Z_H2FP16 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_UCVTF_Z_P_Z_W2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 32
  let d_esize : Nat := 16
  let is_unsigned : Bool := true
  let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_UCVTF_Z_P_Z_W2FP16 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_UCVTF_Z_P_Z_W2FP16 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_UCVTF_Z_P_Z_W2FP16 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_UCVTF_Z_P_Z_W2FP16 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_UCVTF_Z_P_Z_W2FP16 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


def decode_UCVTF_Z_P_Z_X2FP16 (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let s_esize : Nat := 64
  let d_esize : Nat := 16
  let is_unsigned : Bool := true
  let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_UCVTF_Z_P_Z_X2FP16 128 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 256 =>
    (do
      (execute_UCVTF_Z_P_Z_X2FP16 256 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 512 =>
    (do
      (execute_UCVTF_Z_P_Z_X2FP16 512 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 1024 =>
    (do
      (execute_UCVTF_Z_P_Z_X2FP16 1024 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | 2048 =>
    (do
      (execute_UCVTF_Z_P_Z_X2FP16 2048 (Sail.Int.toNatChecked (d)) d_esize esize
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize
  = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_D2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
                ((Sail.BitVec.castWidth ) <$> (FPConvertSVE__1
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) w__3
                  d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend res esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize
  = 64 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_D2H (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
                ((Sail.BitVec.castWidth ) <$> (FPConvertSVE__1
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) w__3
                  d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend res esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize
  = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_S2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
                ((Sail.BitVec.castWidth ) <$> (FPConvertSVE__1
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) w__3
                  d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend res esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize
  = 16 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 64 ∧ d_esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_H2D (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
                ((Sail.BitVec.castWidth ) <$> (FPConvertSVE__1
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) w__3
                  d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend res esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize
  = 16 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 32 ∧ d_esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_H2S (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
                ((Sail.BitVec.castWidth ) <$> (FPConvertSVE__1
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) w__3
                  d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend res esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, d_esize : Nat, esize : Nat, g : Nat, n : Nat, s_esize : Nat, s_esize
  = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  esize = 32 ∧ d_esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_Z_P_Z_S2H (VL : Nat) (d : Nat) (d_esize : Nat) (esize : Nat) (g : Nat) (n : Nat) (s_esize : Nat) : SailM Unit := do
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
                ((Sail.BitVec.castWidth ) <$> (FPConvertSVE__1
                  (Sail.BitVec.extractLsb element (Sail.Int.toNatChecked ((s_esize -i 1))) 0) w__3
                  d_esize)) ) : SailM (BitVec d_esize) )
              (Elem_set result e esize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend res esize))))
          else (pure (result))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_FRECPE_Z_Z__ (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FRECPE_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FRECPE_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FRECPE_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FRECPE_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FRECPE_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FRSQRTE_Z_Z__ (size : (BitVec 2)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FRSQRTE_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FRSQRTE_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FRSQRTE_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FRSQRTE_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FRSQRTE_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


end ArmFull.Functions
