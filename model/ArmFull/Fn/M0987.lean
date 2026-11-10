import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0898
import ArmFull.Fn.M0899

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

def decode_MOVA_Z_P_RZA_D (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (ZAn : (BitVec 3)) (o1 : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat o1)
  let esize : Nat := 64
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_Z_P_RZA_D 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 256 =>
    (do
      (execute_MOVA_Z_P_RZA_D 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 512 =>
    (do
      (execute_MOVA_Z_P_RZA_D 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 1024 =>
    (do
      (execute_MOVA_Z_P_RZA_D 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | 2048 =>
    (do
      (execute_MOVA_Z_P_RZA_D 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s))
        vertical))
  | _ => (pure (()))


def decode_MOVA_Z_P_RZA_Q (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Pg : (BitVec 3)) (ZAn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Nat := 0
  let esize : Nat := 128
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_Z_P_RZA_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_Z_P_RZA_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_Z_P_RZA_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_Z_P_RZA_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_Z_P_RZA_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n)) offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_ADDHA_ZA_PP_Z_32 (V : (BitVec 1)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let da : Int := (BitVec.toNat ZAda)
  match VL with
  | 128 =>
    (do
      (execute_ADDHA_ZA_PP_Z_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADDHA_ZA_PP_Z_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADDHA_ZA_PP_Z_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADDHA_ZA_PP_Z_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADDHA_ZA_PP_Z_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ADDHA_ZA_PP_Z_64 (V : (BitVec 1)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let da : Int := (BitVec.toNat ZAda)
  match VL with
  | 128 =>
    (do
      (execute_ADDHA_ZA_PP_Z_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADDHA_ZA_PP_Z_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADDHA_ZA_PP_Z_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADDHA_ZA_PP_Z_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADDHA_ZA_PP_Z_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ADDVA_ZA_PP_Z_32 (V : (BitVec 1)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let da : Int := (BitVec.toNat ZAda)
  match VL with
  | 128 =>
    (do
      (execute_ADDVA_ZA_PP_Z_32 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADDVA_ZA_PP_Z_32 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADDVA_ZA_PP_Z_32 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADDVA_ZA_PP_Z_32 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADDVA_ZA_PP_Z_32 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ADDVA_ZA_PP_Z_64 (V : (BitVec 1)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (ZAda : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSMEI16I64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let da : Int := (BitVec.toNat ZAda)
  match VL with
  | 128 =>
    (do
      (execute_ADDVA_ZA_PP_Z_64 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADDVA_ZA_PP_Z_64 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADDVA_ZA_PP_Z_64 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADDVA_ZA_PP_Z_64 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADDVA_ZA_PP_Z_64 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_MOVA_ZA2_Z_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 8
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Nat := 0
  let offset : Int := (BitVec.toNat (off3 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA2_Z_B1 128 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA2_Z_B1 256 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA2_Z_B1 512 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA2_Z_B1 1024 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA2_Z_B1 2048 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA2_Z_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 4)) (ZAd : (BitVec 1)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat ZAd)
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA2_Z_H1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA2_Z_H1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA2_Z_H1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA2_Z_H1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA2_Z_H1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA2_Z_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 4)) (ZAd : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 32
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat ZAd)
  let offset : Int := (BitVec.toNat (o1 +++ 0#1))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA2_Z_W1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA2_Z_W1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA2_Z_W1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA2_Z_W1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA2_Z_W1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA2_Z_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 4)) (ZAd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 2
  let esize : Nat := 64
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat ZAd)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA2_Z_D1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA2_Z_D1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA2_Z_D1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA2_Z_D1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA2_Z_D1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA4_Z_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 3)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 8
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Nat := 0
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA4_Z_B1 128 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA4_Z_B1 256 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA4_Z_B1 512 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA4_Z_B1 1024 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA4_Z_B1 2048 d esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA4_Z_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 3)) (ZAd : (BitVec 1)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 16
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat ZAd)
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA4_Z_H1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA4_Z_H1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA4_Z_H1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA4_Z_H1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA4_Z_H1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA4_Z_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 3)) (ZAd : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 32
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat ZAd)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA4_Z_W1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA4_Z_W1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA4_Z_W1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA4_Z_W1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA4_Z_W1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA4_Z_D1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (Zn : (BitVec 3)) (ZAd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let nreg : Nat := 4
  let esize : Nat := 64
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat ZAd)
  let offset : Nat := 0
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA4_Z_D1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVA_ZA4_Z_D1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVA_ZA4_Z_D1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVA_ZA4_Z_D1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVA_ZA4_Z_D1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n)) nreg
        offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVA_ZA_MZ2_1 (Rv : (BitVec 2)) (Zn : (BitVec 4)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat off3)
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let nreg : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA_MZ2_1 128 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_MOVA_ZA_MZ2_1 256 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_MOVA_ZA_MZ2_1 512 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_MOVA_ZA_MZ2_1 1024 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_MOVA_ZA_MZ2_1 2048 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_MOVA_ZA_MZ4_1 (Rv : (BitVec 2)) (Zn : (BitVec 3)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat off3)
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let nreg : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_MOVA_ZA_MZ4_1 128 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_MOVA_ZA_MZ4_1 256 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_MOVA_ZA_MZ4_1 512 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_MOVA_ZA_MZ4_1 1024 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_MOVA_ZA_MZ4_1 2048 (Sail.Int.toNatChecked (n)) nreg (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


end ArmFull.Functions
