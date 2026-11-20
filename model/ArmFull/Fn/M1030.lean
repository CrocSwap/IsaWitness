module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0926
public import ArmFull.Fn.M0927 set_option backward.proofsInPublic true @[expose] public section

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

def decode_SMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 32
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := true
      let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_32 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_32 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_32 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_32 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_32 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_SUMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 32
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := true
      let op1_unsigned : Bool := false
      let op2_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_32 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_32 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_32 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_32 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_32 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_USMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 32
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := true
      let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPS_ZA_PP_ZZ_32 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPS_ZA_PP_ZZ_32 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPS_ZA_PP_ZZ_32 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPS_ZA_PP_ZZ_32 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPS_ZA_PP_ZZ_32 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_UMOPS_ZA_PP_ZZ_32 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 32
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := true
      let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPS_ZA_PP_ZZ_32 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPS_ZA_PP_ZZ_32 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPS_ZA_PP_ZZ_32 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPS_ZA_PP_ZZ_32 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPS_ZA_PP_ZZ_32 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_SMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 64
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := false
      let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPA_ZA_PP_ZZ_64 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPA_ZA_PP_ZZ_64 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPA_ZA_PP_ZZ_64 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPA_ZA_PP_ZZ_64 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPA_ZA_PP_ZZ_64 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_SUMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 64
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := false
      let op1_unsigned : Bool := false
      let op2_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPA_ZA_PP_ZZ_64 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPA_ZA_PP_ZZ_64 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPA_ZA_PP_ZZ_64 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPA_ZA_PP_ZZ_64 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPA_ZA_PP_ZZ_64 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_USMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 64
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := false
      let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPA_ZA_PP_ZZ_64 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPA_ZA_PP_ZZ_64 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPA_ZA_PP_ZZ_64 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPA_ZA_PP_ZZ_64 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMOPA_ZA_PP_ZZ_64 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_UMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 64
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := false
      let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPA_ZA_PP_ZZ_64 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPA_ZA_PP_ZZ_64 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPA_ZA_PP_ZZ_64 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPA_ZA_PP_ZZ_64 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMOPA_ZA_PP_ZZ_64 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_SMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 64
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := true
      let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_64 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_64 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_64 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_64 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMOPS_ZA_PP_ZZ_64 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


def decode_SUMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 64
      let a : Int := (BitVec.toNat Pn)
      let b : Int := (BitVec.toNat Pm)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat ZAda)
      let sub_op : Bool := true
      let op1_unsigned : Bool := false
      let op2_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_64 128
            (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_64 256
            (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_64 512
            (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_64 1024
            (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUMOPS_ZA_PP_ZZ_64 2048
            (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
            (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
            esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned
            sub_op))
      | _ => (pure (())))


end ArmFull.Functions
