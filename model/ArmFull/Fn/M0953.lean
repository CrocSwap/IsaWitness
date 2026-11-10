import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0087
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0852
import ArmFull.Fn.M0869

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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Vd)
  let isBefore : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_LASTB_V_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_LASTB_V_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_LASTB_V_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_LASTB_V_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_LASTB_V_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat Pn)
  let d : Int := (BitVec.toNat Pd)
  let hi : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_PUNPKLO_P_P__ 128 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PUNPKLO_P_P__ 256 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PUNPKLO_P_P__ 512 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PUNPKLO_P_P__ 1024 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PUNPKLO_P_P__ 2048 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat Pn)
  let d : Int := (BitVec.toNat Pd)
  let hi : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_PUNPKHI_P_P__ 128 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_PUNPKHI_P_P__ 256 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_PUNPKHI_P_P__ 512 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_PUNPKHI_P_P__ 1024 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_PUNPKHI_P_P__ 2048 (Sail.Int.toNatChecked (d)) esize hi (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let swsize : Nat := 32
  match VL with
  | 128 =>
    (do
      (execute_REVW_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 256 =>
    (do
      (execute_REVW_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 512 =>
    (do
      (execute_REVW_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 1024 =>
    (do
      (execute_REVW_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 2048 =>
    (do
      (execute_REVW_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((let b__0 := size
     (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
     then true
     else false : Bool)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let swsize : Nat := 16
  match VL with
  | 128 =>
    (do
      (execute_REVH_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 256 =>
    (do
      (execute_REVH_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 512 =>
    (do
      (execute_REVH_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 1024 =>
    (do
      (execute_REVH_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 2048 =>
    (do
      (execute_REVH_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let swsize : Nat := 8
  match VL with
  | 128 =>
    (do
      (execute_REVB_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 256 =>
    (do
      (execute_REVB_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 512 =>
    (do
      (execute_REVB_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 1024 =>
    (do
      (execute_REVB_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | 2048 =>
    (do
      (execute_REVB_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) swsize))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  let hi : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_UUNPKLO_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_UUNPKLO_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_UUNPKLO_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_UUNPKLO_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_UUNPKLO_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let is_unsigned : Bool := true
  let hi : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UUNPKHI_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_UUNPKHI_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_UUNPKHI_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_UUNPKHI_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_UUNPKHI_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  let hi : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SUNPKLO_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_SUNPKLO_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_SUNPKLO_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_SUNPKLO_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_SUNPKLO_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  let is_unsigned : Bool := false
  let hi : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_SUNPKHI_Z_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 256 =>
    (do
      (execute_SUNPKHI_Z_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 512 =>
    (do
      (execute_SUNPKHI_Z_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 1024 =>
    (do
      (execute_SUNPKHI_Z_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | 2048 =>
    (do
      (execute_SUNPKHI_Z_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) hi
        (Sail.Int.toNatChecked (n)) is_unsigned))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let d : Int := (BitVec.toNat Pd)
  let setflags : Bool := false
  let pat : (BitVec 5) := pattern
  match VL with
  | 128 =>
    (do
      (execute_PTRUE_P_S__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | 256 =>
    (do
      (execute_PTRUE_P_S__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | 512 =>
    (do
      (execute_PTRUE_P_S__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | 1024 =>
    (do
      (execute_PTRUE_P_S__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | 2048 =>
    (do
      (execute_PTRUE_P_S__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | _ => (pure (()))


def decode_PTRUES_P_S__ (size : (BitVec 2)) (S : (BitVec 1)) (pattern : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let d : Int := (BitVec.toNat Pd)
  let setflags : Bool := true
  let pat : (BitVec 5) := pattern
  match VL with
  | 128 =>
    (do
      (execute_PTRUES_P_S__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | 256 =>
    (do
      (execute_PTRUES_P_S__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | 512 =>
    (do
      (execute_PTRUES_P_S__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | 1024 =>
    (do
      (execute_PTRUES_P_S__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | 2048 =>
    (do
      (execute_PTRUES_P_S__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
        setflags))
  | _ => (pure (()))


def decode_PFALSE_P__ (S : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
  let d : Int := (BitVec.toNat Pd)
  match VL with
  | 128 =>
    (do
      (execute_PFALSE_P__ 128 (Sail.Int.toNatChecked (d))))
  | 256 =>
    (do
      (execute_PFALSE_P__ 256 (Sail.Int.toNatChecked (d))))
  | 512 =>
    (do
      (execute_PFALSE_P__ 512 (Sail.Int.toNatChecked (d))))
  | 1024 =>
    (do
      (execute_PFALSE_P__ 1024 (Sail.Int.toNatChecked (d))))
  | 2048 =>
    (do
      (execute_PFALSE_P__ 2048 (Sail.Int.toNatChecked (d))))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_RDFFR_P_F__ (VL : Nat) (d : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let ffr ← (( do ((Sail.BitVec.castWidth ) <$> (FFR_read PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth ffr))


/-- Type quantifiers: VL : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ (is_VL VL) -/
def execute_WRFFR_F_P__ (VL : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let hsb : Int := (HighestSetBit operand)
  if (((hsb <b 0) || (is_ones_subrange operand hsb 0)) : Bool)
  then
    (do
      (FFR_set PL (Sail.BitVec.castWidth operand)))
  else
    (do
      let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits PL)) ) : SailM
        (BitVec (Sail.Int.toNatChecked PL)) )
      (FFR_set PL (Sail.BitVec.castWidth w__0)))


/-- Type quantifiers: VL : Nat, d : Nat, g : Nat, k_setflags : Bool, 0 ≤ g ∧
  g ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_RDFFR_P_P_F__ (VL : Nat) (d : Nat) (g : Nat) (setflags : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let ffr ← (( do ((Sail.BitVec.castWidth ) <$> (FFR_read PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result : (BitVec (Sail.Int.toNatChecked PL)) := (ffr &&& mask)
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result 8) ) : SailM (BitVec 4) )
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


end ArmFull.Functions
