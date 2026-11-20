module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1134
public import ArmFull.Fn.M1135 set_option backward.proofsInPublic true @[expose] public section

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

def decode_FRINTI_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Zd)
          let exact : Bool := false
          let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTI_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTI_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTI_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTI_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTI_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | _ => (pure (()))))


def decode_FRINTM_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Zd)
          let exact : Bool := false
          let rounding : FPRounding := FPRounding_NEGINF
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTM_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTM_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTM_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTM_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTM_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | _ => (pure (()))))


def decode_FRINTN_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Zd)
          let exact : Bool := false
          let rounding : FPRounding := FPRounding_TIEEVEN
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTN_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTN_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTN_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTN_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTN_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | _ => (pure (()))))


def decode_FRINTP_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Zd)
          let exact : Bool := false
          let rounding : FPRounding := FPRounding_POSINF
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTP_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTP_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTP_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTP_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTP_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | _ => (pure (()))))


def decode_FRINTX_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Zd)
          let exact : Bool := true
          let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTX_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTX_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTX_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTX_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTX_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | _ => (pure (()))))


def decode_FRINTZ_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let d : Int := (BitVec.toNat Zd)
          let exact : Bool := false
          let rounding : FPRounding := FPRounding_ZERO
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTZ_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTZ_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTZ_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTZ_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRINTZ_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) exact (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n)) rounding))
          | _ => (pure (()))))


def decode_UCVTF_Z_P_Z_X2S (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
      let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2S 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2S 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2S 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2S 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2S 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_UCVTF_Z_P_Z_X2D (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
      let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2D 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2D 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2D 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2D 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_X2D 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_UCVTF_Z_P_Z_W2S (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
      let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2S 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2S 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2S 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2S 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2S 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


def decode_UCVTF_Z_P_Z_W2D (int_U : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
      let rounding ← (( do (FPRoundingMode w__3) ) : SailM FPRounding )
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2D 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2D 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2D 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2D 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCVTF_Z_P_Z_W2D 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) rounding s_esize is_unsigned))
      | _ => (pure (())))


end ArmFull.Functions
