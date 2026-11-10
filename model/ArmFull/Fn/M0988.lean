import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0899
import ArmFull.Fn.M0900

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

def decode_MOVA_MZ2_ZA_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 8
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let n : Nat := 0
  let offset : Int := (BitVec.toNat (off3 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ2_ZA_B1 128 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_MZ2_ZA_B1 256 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_MZ2_ZA_B1 512 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_MZ2_ZA_B1 1024 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_MZ2_ZA_B1 2048 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_MZ2_ZA_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (off2 : (BitVec 2)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 16
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ2_ZA_H1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_MZ2_ZA_H1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_MZ2_ZA_H1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_MZ2_ZA_H1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_MZ2_ZA_H1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_MZ2_ZA_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (o1 : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 32
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat (o1 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ2_ZA_W1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_MZ2_ZA_W1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_MZ2_ZA_W1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_MZ2_ZA_W1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_MZ2_ZA_W1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_MZ2_ZA_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 64
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ2_ZA_D1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_MZ2_ZA_D1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_MZ2_ZA_D1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_MZ2_ZA_D1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_MZ2_ZA_D1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_MZ4_ZA_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off2 : (BitVec 2)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 8
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let n : Nat := 0
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ4_ZA_B1 128 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_MZ4_ZA_B1 256 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_MZ4_ZA_B1 512 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_MZ4_ZA_B1 1024 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_MZ4_ZA_B1 2048 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_MZ4_ZA_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (o1 : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 16
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ4_ZA_H1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_MZ4_ZA_H1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_MZ4_ZA_H1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_MZ4_ZA_H1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_MZ4_ZA_H1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_MZ4_ZA_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 32
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ4_ZA_W1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_MZ4_ZA_W1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_MZ4_ZA_W1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_MZ4_ZA_W1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_MZ4_ZA_W1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_MZ4_ZA_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 64
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ4_ZA_D1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_MZ4_ZA_D1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_MZ4_ZA_D1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_MZ4_ZA_D1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_MZ4_ZA_D1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_MZ_ZA2_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat off3)
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ_ZA2_1 128 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_MOVA_MZ_ZA2_1 256 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_MOVA_MZ_ZA2_1 512 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_MOVA_MZ_ZA2_1 1024 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_MOVA_MZ_ZA2_1 2048 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_MOVA_MZ_ZA4_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat off3)
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_MOVA_MZ_ZA4_1 128 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_MOVA_MZ_ZA4_1 256 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_MOVA_MZ_ZA4_1 512 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_MOVA_MZ_ZA4_1 1024 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_MOVA_MZ_ZA4_1 2048 (Sail.Int.toNatChecked (d)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ADD_ZA_ZW_2x2 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ADD_ZA_ZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ADD_ZA_ZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ADD_ZA_ZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ADD_ZA_ZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ADD_ZA_ZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SUB_ZA_ZW_2x2 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SUB_ZA_ZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SUB_ZA_ZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SUB_ZA_ZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SUB_ZA_ZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SUB_ZA_ZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ADD_ZA_ZW_4x4 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_ADD_ZA_ZW_4x4 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ADD_ZA_ZW_4x4 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ADD_ZA_ZW_4x4 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ADD_ZA_ZW_4x4 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ADD_ZA_ZW_4x4 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SUB_ZA_ZW_4x4 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_SUB_ZA_ZW_4x4 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SUB_ZA_ZW_4x4 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SUB_ZA_ZW_4x4 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SUB_ZA_ZW_4x4 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SUB_ZA_ZW_4x4 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ADD_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ADD_ZA_ZZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ADD_ZA_ZZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ADD_ZA_ZZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ADD_ZA_ZZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ADD_ZA_ZZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_SUB_ZA_ZZW_2x2 (sz : (BitVec 1)) (Zm : (BitVec 4)) (Rv : (BitVec 2)) (Zn : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_SUB_ZA_ZZW_2x2 128 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_SUB_ZA_ZZW_2x2 256 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_SUB_ZA_ZZW_2x2 512 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_SUB_ZA_ZZW_2x2 1024 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_SUB_ZA_ZZW_2x2 2048 (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


end ArmFull.Functions
