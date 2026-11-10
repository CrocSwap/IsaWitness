import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0896
import ArmFull.Fn.M0897
import ArmFull.Fn.M0898

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

def decode_USMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
      (execute_USMOPA_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_USMOPA_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_UMOPA_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
      (execute_UMOPA_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_UMOPA_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_SMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
      (execute_SMOPS_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_SMOPS_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_SUMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
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
      (execute_SUMOPS_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_SUMOPS_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_USMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
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
      (execute_USMOPS_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_USMOPS_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_UMOPS_ZA_PP_ZZ_64 (u0 : (BitVec 1)) (u1 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
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
      (execute_UMOPS_ZA_PP_ZZ_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 256 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 512 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 1024 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | 2048 =>
    (do
      (execute_UMOPS_ZA_PP_ZZ_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned sub_op))
  | _ => (pure (()))


def decode_MOVA_ZA_P_RZ_B (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (off4 : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat Zn)
  let d : Nat := 0
  let offset : Int := (BitVec.toNat off4)
  let esize : Nat := 8
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA_P_RZ_B 128 d esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA_P_RZ_B 256 d esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA_P_RZ_B 512 d esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA_P_RZ_B 1024 d esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA_P_RZ_B 2048 d esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA_P_RZ_H (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ZAd : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat ZAd)
  let offset : Int := (BitVec.toNat off3)
  let esize : Nat := 16
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA_P_RZ_H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA_P_RZ_H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA_P_RZ_H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA_P_RZ_H 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA_P_RZ_H 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | _ => (pure (()))


def decode_MOVA_ZA_P_RZ_W (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ZAd : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat ZAd)
  let offset : Int := (BitVec.toNat off2)
  let esize : Nat := 32
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA_P_RZ_W 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA_P_RZ_W 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA_P_RZ_W 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA_P_RZ_W 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA_P_RZ_W 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | _ => (pure (()))


def decode_MOVA_ZA_P_RZ_D (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ZAd : (BitVec 3)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat ZAd)
  let offset : Int := (BitVec.toNat o1)
  let esize : Nat := 64
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA_P_RZ_D 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA_P_RZ_D 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA_P_RZ_D 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA_P_RZ_D 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA_P_RZ_D 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | _ => (pure (()))


def decode_MOVA_ZA_P_RZ_Q (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ZAd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat ZAd)
  let offset : Nat := 0
  let esize : Nat := 128
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA_P_RZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA_P_RZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA_P_RZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA_P_RZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA_P_RZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_Z_P_RZA_B (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (off4 : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Nat := 0
  let offset : Int := (BitVec.toNat off4)
  let esize : Nat := 8
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_Z_P_RZA_B 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g)) n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_Z_P_RZA_B 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g)) n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_Z_P_RZA_B 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g)) n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_Z_P_RZA_B 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g)) n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_Z_P_RZA_B 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g)) n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_Z_P_RZA_H (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (ZAn : (BitVec 1)) (off3 : (BitVec 3)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat off3)
  let esize : Nat := 16
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_Z_P_RZA_H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 256 =>
    (do
      (execute_MOVA_Z_P_RZA_H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 512 =>
    (do
      (execute_MOVA_Z_P_RZA_H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 1024 =>
    (do
      (execute_MOVA_Z_P_RZA_H 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 2048 =>
    (do
      (execute_MOVA_Z_P_RZA_H 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | _ => (pure (()))


def decode_MOVA_Z_P_RZA_W (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (ZAn : (BitVec 2)) (off2 : (BitVec 2)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat off2)
  let esize : Nat := 32
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_Z_P_RZA_W 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 256 =>
    (do
      (execute_MOVA_Z_P_RZA_W 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 512 =>
    (do
      (execute_MOVA_Z_P_RZA_W 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 1024 =>
    (do
      (execute_MOVA_Z_P_RZA_W 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 2048 =>
    (do
      (execute_MOVA_Z_P_RZA_W 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | _ => (pure (()))


end ArmFull.Functions
