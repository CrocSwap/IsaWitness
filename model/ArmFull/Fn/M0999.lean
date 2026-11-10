import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0921
import ArmFull.Fn.M0922
import ArmFull.Fn.M0923

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

def decode_SMOPS_ZA32_PP_ZZ_16 (u0 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SMOPS_ZA32_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 256 =>
    (do
      (execute_SMOPS_ZA32_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 512 =>
    (do
      (execute_SMOPS_ZA32_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 1024 =>
    (do
      (execute_SMOPS_ZA32_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 2048 =>
    (do
      (execute_SMOPS_ZA32_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | _ => (pure (()))


def decode_UMOPS_ZA32_PP_ZZ_16 (u0 : (BitVec 1)) (Zm : (BitVec 5)) (Pm : (BitVec 3)) (Pn : (BitVec 3)) (Zn : (BitVec 5)) (S : (BitVec 1)) (ZAda : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let a : Int := (BitVec.toNat Pn)
  let b : Int := (BitVec.toNat Pm)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat ZAda)
  let sub_op : Bool := true
  let is_unsigned : Bool := true
  match VL with
  | 128 =>
    (do
      (execute_UMOPS_ZA32_PP_ZZ_16 128
        (Sail.Int.toNatChecked ((((Int.ediv 128 esize) *i (Int.ediv 128 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 256 =>
    (do
      (execute_UMOPS_ZA32_PP_ZZ_16 256
        (Sail.Int.toNatChecked ((((Int.ediv 256 esize) *i (Int.ediv 256 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 512 =>
    (do
      (execute_UMOPS_ZA32_PP_ZZ_16 512
        (Sail.Int.toNatChecked ((((Int.ediv 512 esize) *i (Int.ediv 512 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 1024 =>
    (do
      (execute_UMOPS_ZA32_PP_ZZ_16 1024
        (Sail.Int.toNatChecked ((((Int.ediv 1024 esize) *i (Int.ediv 1024 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | 2048 =>
    (do
      (execute_UMOPS_ZA32_PP_ZZ_16 2048
        (Sail.Int.toNatChecked ((((Int.ediv 2048 esize) *i (Int.ediv 2048 esize)) *i esize)))
        (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (b)) (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sub_op is_unsigned))
  | _ => (pure (()))


def decode_ZERO_ZA1_RI_2 (Rv : (BitVec 2)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat off3)
  let ngrp : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ZERO_ZA1_RI_2 128 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ZERO_ZA1_RI_2 256 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ZERO_ZA1_RI_2 512 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ZERO_ZA1_RI_2 1024 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ZERO_ZA1_RI_2 2048 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ZERO_ZA1_RI_4 (Rv : (BitVec 2)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat off3)
  let ngrp : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_ZERO_ZA1_RI_4 128 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ZERO_ZA1_RI_4 256 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ZERO_ZA1_RI_4 512 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ZERO_ZA1_RI_4 1024 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ZERO_ZA1_RI_4 2048 ngrp (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ZERO_ZA2_RI_1 (Rv : (BitVec 2)) (off3 : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat (off3 +++ 0#1))
  let ngrp : Nat := 1
  let nvec : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ZERO_ZA2_RI_1 128 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ZERO_ZA2_RI_1 256 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ZERO_ZA2_RI_1 512 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ZERO_ZA2_RI_1 1024 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ZERO_ZA2_RI_1 2048 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ZERO_ZA2_RI_2 (Rv : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let ngrp : Nat := 2
  let nvec : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ZERO_ZA2_RI_2 128 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ZERO_ZA2_RI_2 256 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ZERO_ZA2_RI_2 512 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ZERO_ZA2_RI_2 1024 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ZERO_ZA2_RI_2 2048 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ZERO_ZA2_RI_4 (Rv : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat (off2 +++ 0#1))
  let ngrp : Nat := 4
  let nvec : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_ZERO_ZA2_RI_4 128 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ZERO_ZA2_RI_4 256 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ZERO_ZA2_RI_4 512 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ZERO_ZA2_RI_4 1024 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ZERO_ZA2_RI_4 2048 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ZERO_ZA4_RI_1 (Rv : (BitVec 2)) (off2 : (BitVec 2)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat (off2 +++ 0b00#2))
  let ngrp : Nat := 1
  let nvec : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_ZERO_ZA4_RI_1 128 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ZERO_ZA4_RI_1 256 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ZERO_ZA4_RI_1 512 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ZERO_ZA4_RI_1 1024 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ZERO_ZA4_RI_1 2048 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ZERO_ZA4_RI_2 (Rv : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let ngrp : Nat := 2
  let nvec : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_ZERO_ZA4_RI_2 128 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ZERO_ZA4_RI_2 256 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ZERO_ZA4_RI_2 512 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ZERO_ZA4_RI_2 1024 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ZERO_ZA4_RI_2 2048 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_ZERO_ZA4_RI_4 (Rv : (BitVec 2)) (o1 : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let v : Int := (BitVec.toNat (0b010#3 +++ Rv))
  let offset : Int := (BitVec.toNat (o1 +++ 0b00#2))
  let ngrp : Nat := 4
  let nvec : Nat := 4
  match VL with
  | 128 =>
    (do
      (execute_ZERO_ZA4_RI_4 128 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 256 =>
    (do
      (execute_ZERO_ZA4_RI_4 256 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 512 =>
    (do
      (execute_ZERO_ZA4_RI_4 512 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 1024 =>
    (do
      (execute_ZERO_ZA4_RI_4 1024 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | 2048 =>
    (do
      (execute_ZERO_ZA4_RI_4 2048 ngrp nvec (Sail.Int.toNatChecked (offset))
        (Sail.Int.toNatChecked (v))))
  | _ => (pure (()))


def decode_MOVAZ_Z_RZA_B (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off4 : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Nat := 0
  let offset : Int := (BitVec.toNat off4)
  let esize : Nat := 8
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_Z_RZA_B 128 (Sail.Int.toNatChecked (d)) esize n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_Z_RZA_B 256 (Sail.Int.toNatChecked (d)) esize n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_Z_RZA_B 512 (Sail.Int.toNatChecked (d)) esize n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_Z_RZA_B 1024 (Sail.Int.toNatChecked (d)) esize n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_Z_RZA_B 2048 (Sail.Int.toNatChecked (d)) esize n
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_Z_RZA_H (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (off3 : (BitVec 3)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat off3)
  let esize : Nat := 16
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_Z_RZA_H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_Z_RZA_H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_Z_RZA_H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_Z_RZA_H 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_Z_RZA_H 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_Z_RZA_W (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (off2 : (BitVec 2)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat off2)
  let esize : Nat := 32
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_Z_RZA_W 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_Z_RZA_W 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_Z_RZA_W 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_Z_RZA_W 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_Z_RZA_W 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_Z_RZA_D (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 3)) (o1 : (BitVec 1)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Int := (BitVec.toNat o1)
  let esize : Nat := 64
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_Z_RZA_D 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_Z_RZA_D 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_Z_RZA_D 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_Z_RZA_D 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_Z_RZA_D 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_Z_RZA_Q (size : (BitVec 2)) (Q : (BitVec 1)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 4)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let s : Int := (BitVec.toNat (0b011#3 +++ Rs))
  let n : Int := (BitVec.toNat ZAn)
  let offset : Nat := 0
  let esize : Nat := 128
  let d : Int := (BitVec.toNat Zd)
  let vertical : Bool := (V == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_MOVAZ_Z_RZA_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_Z_RZA_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_Z_RZA_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_Z_RZA_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_Z_RZA_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        offset (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_MZ2_ZA_B1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (off3 : (BitVec 3)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
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
      (execute_MOVAZ_MZ2_ZA_B1 128 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_MZ2_ZA_B1 256 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_MZ2_ZA_B1 512 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ2_ZA_B1 1024 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ2_ZA_B1 2048 (Sail.Int.toNatChecked (d)) esize n nreg
        (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_MZ2_ZA_H1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 1)) (off2 : (BitVec 2)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
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
      (execute_MOVAZ_MZ2_ZA_H1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_MZ2_ZA_H1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_MZ2_ZA_H1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ2_ZA_H1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ2_ZA_H1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


def decode_MOVAZ_MZ2_ZA_W1 (size : (BitVec 2)) (V : (BitVec 1)) (Rs : (BitVec 2)) (ZAn : (BitVec 2)) (o1 : (BitVec 1)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
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
      (execute_MOVAZ_MZ2_ZA_W1 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 256 =>
    (do
      (execute_MOVAZ_MZ2_ZA_W1 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 512 =>
    (do
      (execute_MOVAZ_MZ2_ZA_W1 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 1024 =>
    (do
      (execute_MOVAZ_MZ2_ZA_W1 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | 2048 =>
    (do
      (execute_MOVAZ_MZ2_ZA_W1 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))
        nreg (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (s)) vertical))
  | _ => (pure (()))


end ArmFull.Functions
