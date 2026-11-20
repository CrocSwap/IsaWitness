module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0899
public import ArmFull.Fn.M0900 set_option backward.proofsInPublic true @[expose] public section

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

def decode_LASTB_V_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Vd)
      let isBefore : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LASTB_V_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LASTB_V_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LASTB_V_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LASTB_V_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LASTB_V_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_PUNPKLO_P_P__ (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 16
      let n : Int := (BitVec.toNat Pn)
      let d : Int := (BitVec.toNat Pd)
      let hi : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKLO_P_P__ 128 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKLO_P_P__ 256 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKLO_P_P__ 512 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKLO_P_P__ 1024 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKLO_P_P__ 2048 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_PUNPKHI_P_P__ (H : (BitVec 1)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 16
      let n : Int := (BitVec.toNat Pn)
      let d : Int := (BitVec.toNat Pd)
      let hi : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKHI_P_P__ 128 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKHI_P_P__ 256 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKHI_P_P__ 512 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKHI_P_P__ 1024 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PUNPKHI_P_P__ 2048 (Sail.Int.toNatChecked (d)) esize hi
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_REVW_Z_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      if ((size != 0b11#2) : Bool)
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
          let swsize : Nat := 32
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVW_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVW_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVW_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVW_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVW_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | _ => (pure (()))))


def decode_REVH_Z_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      if ((let b__0 := size
         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
         then true
         else false : Bool)) : Bool)
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
          let swsize : Nat := 16
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVH_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVH_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVH_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVH_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVH_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | _ => (pure (()))))


def decode_REVB_Z_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let swsize : Nat := 8
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVB_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVB_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVB_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVB_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_REVB_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
          | _ => (pure (()))))


def decode_UUNPKLO_Z_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          let is_unsigned : Bool := true
          let hi : Bool := false
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKLO_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKLO_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKLO_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKLO_Z_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKLO_Z_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | _ => (pure (()))))


def decode_UUNPKHI_Z_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          let is_unsigned : Bool := true
          let hi : Bool := true
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKHI_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKHI_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKHI_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKHI_Z_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UUNPKHI_Z_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | _ => (pure (()))))


def decode_SUNPKLO_Z_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          let is_unsigned : Bool := false
          let hi : Bool := false
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKLO_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKLO_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKLO_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKLO_Z_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKLO_Z_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | _ => (pure (()))))


def decode_SUNPKHI_Z_Z__ (size : (BitVec 2)) (U : (BitVec 1)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          let is_unsigned : Bool := false
          let hi : Bool := true
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKHI_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKHI_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKHI_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKHI_Z_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SUNPKHI_Z_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) hi (Sail.Int.toNatChecked (n)) is_unsigned))
          | _ => (pure (()))))


/-- Type quantifiers: VL : Nat, (is_VL VL) -/
def execute_SETFFR_F__ (VL : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  (FFR_set PL (Sail.BitVec.castWidth (Ones (n := PL))))


def decode_PTRUE_P_S__ (size : (BitVec 2)) (S : (BitVec 1)) (pattern : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := false
      let pat : (BitVec 5) := pattern
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUE_P_S__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUE_P_S__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUE_P_S__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUE_P_S__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUE_P_S__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | _ => (pure (())))


end ArmFull.Functions
