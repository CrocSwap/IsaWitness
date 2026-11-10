import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1135
import ArmFull.Fn.M1136
import ArmFull.Fn.M1137

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

def decode_FCLAMP_MZ_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_FCLAMP_MZ_ZZ_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 256 =>
    (do
      (execute_FCLAMP_MZ_ZZ_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 512 =>
    (do
      (execute_FCLAMP_MZ_ZZ_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 1024 =>
    (do
      (execute_FCLAMP_MZ_ZZ_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | 2048 =>
    (do
      (execute_FCLAMP_MZ_ZZ_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
  | _ => (pure (()))


def decode_BFCVT_Z_MZ2__ (Zn : (BitVec 4)) (N : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFCVT_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFCVT_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFCVT_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFCVT_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFCVT_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FCVT_Z_MZ2__ (Zn : (BitVec 4)) (N : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FCVT_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVT_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVT_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVT_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVT_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFCVTN_Z_MZ2__ (Zn : (BitVec 4)) (N : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFCVTN_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFCVTN_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFCVTN_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFCVTN_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFCVTN_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FCVTN_Z_MZ2__ (Zn : (BitVec 4)) (N : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FCVTN_Z_MZ2__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVTN_Z_MZ2__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVTN_Z_MZ2__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVTN_Z_MZ2__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVTN_Z_MZ2__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_LDR_ZT_BR__ (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  (execute_LDR_ZT_BR__ (Sail.Int.toNatChecked (n)))


def decode_STR_ZT_BR__ (Rn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  (execute_STR_ZT_BR__ (Sail.Int.toNatChecked (n)))


def decode_FMOPA_ZA_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_FMOPA_ZA_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_FMOPS_ZA_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_FMOPS_ZA_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_BFMOPA_ZA_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BFMOPA_ZA_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 16) *i (Int.ediv 128 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_BFMOPA_ZA_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 16) *i (Int.ediv 256 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_BFMOPA_ZA_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 16) *i (Int.ediv 512 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_BFMOPA_ZA_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 16) *i (Int.ediv 1024 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_BFMOPA_ZA_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 16) *i (Int.ediv 2048 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_BFMOPS_ZA_PP_ZZ_16 (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_BFMOPS_ZA_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 16) *i (Int.ediv 128 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 256 =>
    (do
      (execute_BFMOPS_ZA_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 16) *i (Int.ediv 256 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 512 =>
    (do
      (execute_BFMOPS_ZA_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 16) *i (Int.ediv 512 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 1024 =>
    (do
      (execute_BFMOPS_ZA_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 16) *i (Int.ediv 1024 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | 2048 =>
    (do
      (execute_BFMOPS_ZA_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 16) *i (Int.ediv 2048 16)) *i 16)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op))
  | _ => (pure (()))


def decode_FADD_ZA_ZW_2x2_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_FADD_ZA_ZW_2x2_16 128 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FADD_ZA_ZW_2x2_16 256 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FADD_ZA_ZW_2x2_16 512 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FADD_ZA_ZW_2x2_16 1024 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FADD_ZA_ZW_2x2_16 2048 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_FSUB_ZA_ZW_2x2_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_FSUB_ZA_ZW_2x2_16 128 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FSUB_ZA_ZW_2x2_16 256 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FSUB_ZA_ZW_2x2_16 512 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FSUB_ZA_ZW_2x2_16 1024 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FSUB_ZA_ZW_2x2_16 2048 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFADD_ZA_ZW_2x2_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFADD_ZA_ZW_2x2_16 128 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFADD_ZA_ZW_2x2_16 256 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFADD_ZA_ZW_2x2_16 512 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFADD_ZA_ZW_2x2_16 1024 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFADD_ZA_ZW_2x2_16 2048 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFSUB_ZA_ZW_2x2_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 4)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let m : Int := (BitVec.toNat (Zm +++ 0#1))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_BFSUB_ZA_ZW_2x2_16 128 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFSUB_ZA_ZW_2x2_16 256 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFSUB_ZA_ZW_2x2_16 512 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFSUB_ZA_ZW_2x2_16 1024 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFSUB_ZA_ZW_2x2_16 2048 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_FADD_ZA_ZW_4x4_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_FADD_ZA_ZW_4x4_16 128 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FADD_ZA_ZW_4x4_16 256 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FADD_ZA_ZW_4x4_16 512 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FADD_ZA_ZW_4x4_16 1024 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FADD_ZA_ZW_4x4_16 2048 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_FSUB_ZA_ZW_4x4_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEF16F16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let esize : Nat := 16
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_FSUB_ZA_ZW_4x4_16 128 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_FSUB_ZA_ZW_4x4_16 256 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_FSUB_ZA_ZW_4x4_16 512 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_FSUB_ZA_ZW_4x4_16 1024 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_FSUB_ZA_ZW_4x4_16 2048 esize (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFADD_ZA_ZW_4x4_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFADD_ZA_ZW_4x4_16 128 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFADD_ZA_ZW_4x4_16 256 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFADD_ZA_ZW_4x4_16 512 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFADD_ZA_ZW_4x4_16 1024 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFADD_ZA_ZW_4x4_16 2048 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_BFSUB_ZA_ZW_4x4_16 (sz : (BitVec 1)) (Rv : (BitVec 2)) (Zm : (BitVec 3)) (S : (BitVec 1)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
  let offset : Int := (BitVec.toNat off3)
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_BFSUB_ZA_ZW_4x4_16 128 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_BFSUB_ZA_ZW_4x4_16 256 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_BFSUB_ZA_ZW_4x4_16 512 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_BFSUB_ZA_ZW_4x4_16 1024 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_BFSUB_ZA_ZW_4x4_16 2048 (Sail.Int.toNatChecked (m)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


end ArmFull.Functions
