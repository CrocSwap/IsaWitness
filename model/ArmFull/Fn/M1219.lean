module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1179
public import ArmFull.Fn.M1180
public import ArmFull.Fn.M1181 set_option backward.proofsInPublic true @[expose] public section

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

def decode_LDNF1B_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 32
      let msize : Nat := 8
      let is_unsigned : Bool := true
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U32 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U32 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U32 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U32 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U32 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1B_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 64
      let msize : Nat := 8
      let is_unsigned : Bool := true
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1B_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1SW_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 64
      let msize : Nat := 32
      let is_unsigned : Bool := false
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SW_Z_P_BI_S64 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SW_Z_P_BI_S64 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SW_Z_P_BI_S64 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SW_Z_P_BI_S64 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SW_Z_P_BI_S64 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1H_Z_P_BI_U16 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 16
      let msize : Nat := 16
      let is_unsigned : Bool := true
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U16 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U16 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U16 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U16 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U16 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1H_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 32
      let msize : Nat := 16
      let is_unsigned : Bool := true
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U32 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U32 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U32 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U32 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U32 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1H_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 64
      let msize : Nat := 16
      let is_unsigned : Bool := true
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1H_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1SH_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 64
      let msize : Nat := 16
      let is_unsigned : Bool := false
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S64 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S64 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S64 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S64 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S64 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1SH_Z_P_BI_S32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 32
      let msize : Nat := 16
      let is_unsigned : Bool := false
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S32 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S32 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S32 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S32 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SH_Z_P_BI_S32 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1W_Z_P_BI_U32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 32
      let msize : Nat := 32
      let is_unsigned : Bool := true
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U32 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U32 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U32 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U32 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U32 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1W_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 64
      let msize : Nat := 32
      let is_unsigned : Bool := true
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1W_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1SB_Z_P_BI_S64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 64
      let msize : Nat := 8
      let is_unsigned : Bool := false
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S64 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S64 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S64 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S64 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S64 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1SB_Z_P_BI_S32 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 32
      let msize : Nat := 8
      let is_unsigned : Bool := false
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S32 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S32 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S32 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S32 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S32 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1SB_Z_P_BI_S16 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 16
      let msize : Nat := 8
      let is_unsigned : Bool := false
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S16 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S16 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S16 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S16 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1SB_Z_P_BI_S16 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


def decode_LDNF1D_Z_P_BI_U64 (dtype : (BitVec 4)) (imm4 : (BitVec 4)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 64
      let msize : Nat := 64
      let is_unsigned : Bool := true
      let offset : Int := (BitVec.toInt imm4)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1D_Z_P_BI_U64 128 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1D_Z_P_BI_U64 256 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1D_Z_P_BI_U64 512 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1D_Z_P_BI_U64 1024 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LDNF1D_Z_P_BI_U64 2048 esize (Sail.Int.toNatChecked (g)) msize
            (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


end ArmFull.Functions
