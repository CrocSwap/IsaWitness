import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0118
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0218
import ArmFull.Fn.M0852
import ArmFull.Fn.M0893
import ArmFull.Fn.M0894

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

def decode_CNTP_R_PN__ (size : (BitVec 2)) (vl : (BitVec 1)) (PNn : (BitVec 4)) (Rd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat PNn)
  let d : Int := (BitVec.toNat Rd)
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))) "sail-arm/instrs64_sve.sail:56606.130-56606.131"
      (execute_CNTP_R_PN__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))) "sail-arm/instrs64_sve.sail:56610.130-56610.131"
      (execute_CNTP_R_PN__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))) "sail-arm/instrs64_sve.sail:56614.130-56614.131"
      (execute_CNTP_R_PN__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))) "sail-arm/instrs64_sve.sail:56618.131-56618.132"
      (execute_CNTP_R_PN__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 15) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))) "sail-arm/instrs64_sve.sail:56622.131-56622.132"
      (execute_CNTP_R_PN__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


def decode_WHILELO_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat := 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := true
  let invert : Bool := false
  let op : SVECmp := Cmp_LT
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56696.151-56696.152"
      (execute_WHILELO_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56700.151-56700.152"
      (execute_WHILELO_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56704.151-56704.152"
      (execute_WHILELO_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56708.152-56708.153"
      (execute_WHILELO_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56712.152-56712.153"
      (execute_WHILELO_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


def decode_WHILELS_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat := 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := true
  let invert : Bool := false
  let op : SVECmp := Cmp_LE
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56790.151-56790.152"
      (execute_WHILELS_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56794.151-56794.152"
      (execute_WHILELS_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56798.151-56798.152"
      (execute_WHILELS_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56802.152-56802.153"
      (execute_WHILELS_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56806.152-56806.153"
      (execute_WHILELS_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


def decode_WHILELT_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat := 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := false
  let invert : Bool := false
  let op : SVECmp := Cmp_LT
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56884.151-56884.152"
      (execute_WHILELT_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56888.151-56888.152"
      (execute_WHILELT_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56892.151-56892.152"
      (execute_WHILELT_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56896.152-56896.153"
      (execute_WHILELT_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56900.152-56900.153"
      (execute_WHILELT_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


def decode_WHILELE_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat := 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := false
  let invert : Bool := false
  let op : SVECmp := Cmp_LE
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56978.151-56978.152"
      (execute_WHILELE_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56982.151-56982.152"
      (execute_WHILELE_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56986.151-56986.152"
      (execute_WHILELE_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56990.152-56990.153"
      (execute_WHILELE_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "sail-arm/instrs64_sve.sail:56994.152-56994.153"
      (execute_WHILELE_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


def decode_WHILEHI_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat := 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := true
  let invert : Bool := true
  let op : SVECmp := Cmp_GT
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57072.151-57072.152"
      (execute_WHILEHI_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57076.151-57076.152"
      (execute_WHILEHI_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57080.151-57080.152"
      (execute_WHILEHI_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57084.152-57084.153"
      (execute_WHILEHI_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57088.152-57088.153"
      (execute_WHILEHI_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


def decode_WHILEHS_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat := 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := true
  let invert : Bool := true
  let op : SVECmp := Cmp_GE
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57166.151-57166.152"
      (execute_WHILEHS_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57170.151-57170.152"
      (execute_WHILEHS_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57174.151-57174.152"
      (execute_WHILEHS_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57178.152-57178.153"
      (execute_WHILEHS_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57182.152-57182.153"
      (execute_WHILEHS_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


def decode_WHILEGT_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat := 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := false
  let invert : Bool := true
  let op : SVECmp := Cmp_GT
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57260.151-57260.152"
      (execute_WHILEGT_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57264.151-57264.152"
      (execute_WHILEGT_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57268.151-57268.152"
      (execute_WHILEGT_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57272.152-57272.153"
      (execute_WHILEGT_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57276.152-57276.153"
      (execute_WHILEGT_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


def decode_WHILEGE_PN_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (vl : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (PNd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let rsize : Nat := 64
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let d : Int := (BitVec.toNat (1#1 +++ PNd))
  let is_unsigned : Bool := false
  let invert : Bool := true
  let op : SVECmp := Cmp_GE
  let width : Int := (Int.shiftl 2 (BitVec.toNat vl))
  match VL with
  | 128 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57354.151-57354.152"
      (execute_WHILEGE_PN_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 256 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57358.151-57358.152"
      (execute_WHILEGE_PN_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 512 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57362.151-57362.152"
      (execute_WHILEGE_PN_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 1024 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57366.152-57366.153"
      (execute_WHILEGE_PN_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | 2048 =>
    (do
      ArmFull.assert (((width == 2) || (width == 4)) && ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 31) && (((((esize == 8) || (esize == 16)) || (esize == 32)) || (esize == 64)) && ((0 ≤b d) && ((d ≤b 15) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048)))))))))) "sail-arm/instrs64_sve.sail:57370.152-57370.153"
      (execute_WHILEGE_PN_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        invert (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op rsize is_unsigned
        (Sail.Int.toNatChecked (width))))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned
  : Bool, scale : Nat, k_stream : Bool, scale = 0 ∧
  offs_size = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFB_I_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 5793) 64) ) : SailM (BitVec 64) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5794)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__3 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__3 : (BitVec 64))
        let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__4 : (BitVec VL))
        (pure ((base, offset))))
    else (pure ((base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__5 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__5 : Bool)
        then
          (do
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
              (BitVec esize) )
            let off ← (( do
              (asl_Int (Sail.BitVec.extractLsb w__6 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                offs_unsigned) ) : SailM Int )
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
            (pure ((Hint_Prefetch addr pref_hint level stream))))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, level : Nat, m : Nat, n : Nat, offs_size : Nat, k_offs_unsigned
  : Bool, scale : Nat, k_stream : Bool, scale = 1 ∧
  offs_size = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem level [0, 1, 2, 3] ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_PRFH_I_P_BZ_S_x32_scaled (VL : Nat) (esize : Nat) (g : Nat) (level : Nat) (m : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (pref_hint : PrefetchHint) (scale : Nat) (stream : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let base ← (( do (undefined_bitvector_at (← occLabel 5795) 64) ) : SailM (BitVec 64) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5796)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__3 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__3 : (BitVec 64))
        let w__4 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__4 : (BitVec VL))
        (pure ((base, offset))))
    else (pure ((base, offset))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let offset := offset
  let base := base
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__5 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
        if (w__5 : Bool)
        then
          (do
            let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
              (BitVec esize) )
            let off ← (( do
              (asl_Int (Sail.BitVec.extractLsb w__6 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                offs_unsigned) ) : SailM Int )
            let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
            (pure ((Hint_Prefetch addr pref_hint level stream))))
        else (pure (()))
    (pure loop_vars))


end ArmFull.Functions
