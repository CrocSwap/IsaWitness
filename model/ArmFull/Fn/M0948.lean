module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0873
public import ArmFull.Fn.M0874
public import ArmFull.Fn.M0875 set_option backward.proofsInPublic true @[expose] public section

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

def decode_SMAX_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
      let m : Int := (BitVec.toNat (0#1 +++ Zm))
      let nreg : Nat := 2
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_UMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
      let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
      let nreg : Nat := 4
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_SMAX_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
      let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
      let nreg : Nat := 4
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_UMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
      let m : Int := (BitVec.toNat (0#1 +++ Zm))
      let nreg : Nat := 4
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMAX_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_SMAX_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
      let m : Int := (BitVec.toNat (0#1 +++ Zm))
      let nreg : Nat := 4
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMAX_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_UMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
      let m : Int := (BitVec.toNat (Zm +++ 0#1))
      let nreg : Nat := 2
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_SMIN_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
      let m : Int := (BitVec.toNat (Zm +++ 0#1))
      let nreg : Nat := 2
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_UMIN_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
      let m : Int := (BitVec.toNat (0#1 +++ Zm))
      let nreg : Nat := 2
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_SMIN_MZ_ZZV_2x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
      let m : Int := (BitVec.toNat (0#1 +++ Zm))
      let nreg : Nat := 2
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_2x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_2x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_2x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_2x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_2x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_UMIN_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
      let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
      let nreg : Nat := 4
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_SMIN_MZ_ZZW_4x4 (size : (BitVec 2)) (Zm : (BitVec 3)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
      let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
      let nreg : Nat := 4
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_4x4 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_4x4 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_4x4 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_4x4 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZW_4x4 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_UMIN_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
      let m : Int := (BitVec.toNat (0#1 +++ Zm))
      let nreg : Nat := 4
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMIN_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_SMIN_MZ_ZZV_4x1 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 3)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0b00#2))
      let m : Int := (BitVec.toNat (0#1 +++ Zm))
      let nreg : Nat := 4
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_4x1 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_4x1 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_4x1 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_4x1 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMIN_MZ_ZZV_4x1 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg is_unsigned))
      | _ => (pure (())))


def decode_URSHL_MZ_ZZW_2x2 (size : (BitVec 2)) (Zm : (BitVec 4)) (Zdn : (BitVec 4)) (U : (BitVec 1)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat (Zdn +++ 0#1))
      let m : Int := (BitVec.toNat (Zm +++ 0#1))
      let nreg : Nat := 2
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_URSHL_MZ_ZZW_2x2 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_URSHL_MZ_ZZW_2x2 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_URSHL_MZ_ZZW_2x2 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) nreg))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_URSHL_MZ_ZZW_2x2 1024 (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_URSHL_MZ_ZZW_2x2 2048 (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) nreg))
      | _ => (pure (())))


end ArmFull.Functions
