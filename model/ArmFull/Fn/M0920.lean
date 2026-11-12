import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0848
import ArmFull.Fn.M0849

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

def decode_SQCVT_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_SQCVT_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_SQCVT_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_SQCVT_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_SQCVT_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_SQCVT_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_UQCVT_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_UQCVT_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_UQCVT_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_UQCVT_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_UQCVT_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_UQCVT_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SQCVTU_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_SQCVTU_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_SQCVTU_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_SQCVTU_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_SQCVTU_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_SQCVTU_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SQCVTN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-arm/instrs64_sme.sail:34431.103-34431.104"
      (execute_SQCVTN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-arm/instrs64_sme.sail:34435.103-34435.104"
      (execute_SQCVTN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-arm/instrs64_sme.sail:34439.103-34439.104"
      (execute_SQCVTN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-arm/instrs64_sme.sail:34443.104-34443.105"
      (execute_SQCVTN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-arm/instrs64_sme.sail:34447.104-34447.105"
      (execute_SQCVTN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_UQCVTN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-arm/instrs64_sme.sail:34495.103-34495.104"
      (execute_UQCVTN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-arm/instrs64_sme.sail:34499.103-34499.104"
      (execute_UQCVTN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-arm/instrs64_sme.sail:34503.103-34503.104"
      (execute_UQCVTN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-arm/instrs64_sme.sail:34507.104-34507.105"
      (execute_UQCVTN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-arm/instrs64_sme.sail:34511.104-34511.105"
      (execute_UQCVTN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SQCVTUN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-arm/instrs64_sme.sail:34559.103-34559.104"
      (execute_SQCVTUN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-arm/instrs64_sme.sail:34563.103-34563.104"
      (execute_SQCVTUN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-arm/instrs64_sme.sail:34567.103-34567.104"
      (execute_SQCVTUN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-arm/instrs64_sme.sail:34571.104-34571.105"
      (execute_SQCVTUN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-arm/instrs64_sme.sail:34575.104-34575.105"
      (execute_SQCVTUN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SQCVT_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-arm/instrs64_sme.sail:34623.103-34623.104"
      (execute_SQCVT_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-arm/instrs64_sme.sail:34627.103-34627.104"
      (execute_SQCVT_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-arm/instrs64_sme.sail:34631.103-34631.104"
      (execute_SQCVT_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-arm/instrs64_sme.sail:34635.104-34635.105"
      (execute_SQCVT_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-arm/instrs64_sme.sail:34639.104-34639.105"
      (execute_SQCVT_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_UQCVT_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-arm/instrs64_sme.sail:34687.103-34687.104"
      (execute_UQCVT_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-arm/instrs64_sme.sail:34691.103-34691.104"
      (execute_UQCVT_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-arm/instrs64_sme.sail:34695.103-34695.104"
      (execute_UQCVT_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-arm/instrs64_sme.sail:34699.104-34699.105"
      (execute_UQCVT_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-arm/instrs64_sme.sail:34703.104-34703.105"
      (execute_UQCVT_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SQCVTU_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-arm/instrs64_sme.sail:34751.103-34751.104"
      (execute_SQCVTU_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-arm/instrs64_sme.sail:34755.103-34755.104"
      (execute_SQCVTU_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-arm/instrs64_sme.sail:34759.103-34759.104"
      (execute_SQCVTU_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-arm/instrs64_sme.sail:34763.104-34763.105"
      (execute_SQCVTU_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-arm/instrs64_sme.sail:34767.104-34767.105"
      (execute_SQCVTU_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ZIP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 =>
    (do
      (execute_ZIP_MZ_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ZIP_MZ_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ZIP_MZ_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ZIP_MZ_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ZIP_MZ_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_UZP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 =>
    (do
      (execute_UZP_MZ_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_UZP_MZ_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_UZP_MZ_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_UZP_MZ_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_UZP_MZ_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ZIP_MZ_ZZ_2Q (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 =>
    (do
      (execute_ZIP_MZ_ZZ_2Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ZIP_MZ_ZZ_2Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ZIP_MZ_ZZ_2Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ZIP_MZ_ZZ_2Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ZIP_MZ_ZZ_2Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_UZP_MZ_ZZ_2Q (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  match VL with
  | 128 =>
    (do
      (execute_UZP_MZ_ZZ_2Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_UZP_MZ_ZZ_2Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_UZP_MZ_ZZ_2Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_UZP_MZ_ZZ_2Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_UZP_MZ_ZZ_2Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ZIP_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  match VL with
  | 128 =>
    (do
      (execute_ZIP_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ZIP_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ZIP_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ZIP_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ZIP_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_UZP_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  match VL with
  | 128 =>
    (do
      (execute_UZP_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_UZP_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_UZP_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_UZP_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_UZP_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ZIP_MZ_Z_4Q (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  match VL with
  | 128 =>
    (do
      (execute_ZIP_MZ_Z_4Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ZIP_MZ_Z_4Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ZIP_MZ_Z_4Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ZIP_MZ_Z_4Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ZIP_MZ_Z_4Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_UZP_MZ_Z_4Q (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 128
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  match VL with
  | 128 =>
    (do
      (execute_UZP_MZ_Z_4Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_UZP_MZ_Z_4Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_UZP_MZ_Z_4Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_UZP_MZ_Z_4Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_UZP_MZ_Z_4Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SEL_MZ_P_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 4)) (PNg : (BitVec 3)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SEL_MZ_P_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_SEL_MZ_P_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_SEL_MZ_P_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_SEL_MZ_P_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_SEL_MZ_P_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_SEL_MZ_P_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 3)) (PNg : (BitVec 3)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let g : Int := (BitVec.toNat (1#1 +++ PNg))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_SEL_MZ_P_ZZ_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_SEL_MZ_P_ZZ_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_SEL_MZ_P_ZZ_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_SEL_MZ_P_ZZ_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_SEL_MZ_P_ZZ_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


end ArmFull.Functions
