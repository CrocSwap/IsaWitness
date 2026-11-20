module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0877
public import ArmFull.Fn.M0878 set_option backward.proofsInPublic true @[expose] public section

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

def decode_UQRSHR_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := 8
      let esize ← (( do
        match tsize with
        | 0b00 =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | 0b01 => (pure (8))
        | b__0 => (pure (16)) ) : SailM Int )
      let esize : Int := esize
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat Zd)
      let shift : Int := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHR_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHR_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHR_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHR_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQRSHR_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | _ => (pure (())))


def decode_SQRSHRU_Z_MZ4__ (tsize : (BitVec 2)) (imm5 : (BitVec 5)) (N : (BitVec 1)) (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := 8
      let esize ← (( do
        match tsize with
        | 0b00 =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | 0b01 => (pure (8))
        | b__0 => (pure (16)) ) : SailM Int )
      let esize : Int := esize
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat Zd)
      let shift : Int := ((8 *i esize) -i (BitVec.toNat (tsize +++ imm5)))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRU_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRU_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRU_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRU_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQRSHRU_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n)) shift))
      | _ => (pure (())))


def decode_SQCVT_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UQCVT_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQCVTU_Z_MZ2__ (Zn : (BitVec 4)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 16
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQCVTN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34431.103-34431.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34435.103-34435.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34439.103-34439.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34443.104-34443.105"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34447.104-34447.105"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UQCVTN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34495.103-34495.104"
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34499.103-34499.104"
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34503.103-34503.104"
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34507.104-34507.105"
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34511.104-34511.105"
          (__ArmCertEndOfDecode ())
          (execute_UQCVTN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQCVTUN_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34559.103-34559.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34563.103-34563.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34567.103-34567.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34571.104-34571.105"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34575.104-34575.105"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTUN_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQCVT_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34623.103-34623.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34627.103-34627.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34631.103-34631.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34635.104-34635.105"
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34639.104-34639.105"
          (__ArmCertEndOfDecode ())
          (execute_SQCVT_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UQCVT_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34687.103-34687.104"
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34691.103-34691.104"
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34695.103-34695.104"
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34699.104-34699.105"
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34703.104-34703.105"
          (__ArmCertEndOfDecode ())
          (execute_UQCVT_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SQCVTU_Z_MZ4__ (sz : (BitVec 1)) (Zn : (BitVec 3)) (N : (BitVec 1)) (U : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((128 == 128) || (128 == 256)) || (128 == 512)) || (128 == 1024)) || (128 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34751.103-34751.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ4__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((256 == 128) || (256 == 256)) || (256 == 512)) || (256 == 1024)) || (256 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34755.103-34755.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ4__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((512 == 128) || (512 == 256)) || (512 == 512)) || (512 == 1024)) || (512 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34759.103-34759.104"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ4__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((1024 == 128) || (1024 == 256)) || (1024 == 512)) || (1024 == 1024)) || (1024 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34763.104-34763.105"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ4__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && (((esize == 8) || (esize == 16)) && ((0 ≤b d) && ((d ≤b 31) && (((((2048 == 128) || (2048 == 256)) || (2048 == 512)) || (2048 == 1024)) || (2048 == 2048))))))) "sail-inputs/17-instrs64_sme.sail:34767.104-34767.105"
          (__ArmCertEndOfDecode ())
          (execute_SQCVTU_Z_MZ4__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_ZIP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat (Zd +++ 0#1))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UZP_MZ_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat (Zd +++ 0#1))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_ZIP_MZ_ZZ_2Q (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat (Zd +++ 0#1))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_ZZ_2Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


end ArmFull.Functions
