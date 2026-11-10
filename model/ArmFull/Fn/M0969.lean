import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0882
import ArmFull.Fn.M0883

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

def decode_SSUBLTB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (S : (BitVec 1)) (tb : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  let sel1 : Nat := 1
  let sel2 : Nat := 0
  let is_unsigned : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_SSUBLTB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2 is_unsigned))
  | 256 =>
    (do
      (execute_SSUBLTB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2 is_unsigned))
  | 512 =>
    (do
      (execute_SSUBLTB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2 is_unsigned))
  | 1024 =>
    (do
      (execute_SSUBLTB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2 is_unsigned))
  | 2048 =>
    (do
      (execute_SSUBLTB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) sel1 sel2 is_unsigned))
  | _ => (pure (()))


def decode_CADD_Z_ZZ__ (size : (BitVec 2)) (rot : (BitVec 1)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let m : Int := (BitVec.toNat Zm)
  let dn : Int := (BitVec.toNat Zdn)
  let sub_i : Bool := (rot == 0#1)
  let sub_r : Bool := (rot == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_CADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 256 =>
    (do
      (execute_CADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 512 =>
    (do
      (execute_CADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_CADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_CADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | _ => (pure (()))


def decode_SQCADD_Z_ZZ__ (size : (BitVec 2)) (rot : (BitVec 1)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let m : Int := (BitVec.toNat Zm)
  let dn : Int := (BitVec.toNat Zdn)
  let sub_i : Bool := (rot == 0#1)
  let sub_r : Bool := (rot == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_SQCADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 256 =>
    (do
      (execute_SQCADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 512 =>
    (do
      (execute_SQCADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_SQCADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_SQCADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | _ => (pure (()))


def decode_CMLA_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  let sub_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_CMLA_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 256 =>
    (do
      (execute_CMLA_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 512 =>
    (do
      (execute_CMLA_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_CMLA_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_CMLA_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | _ => (pure (()))


def decode_CMLA_Z_ZZZi_H (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let index : Int := (BitVec.toNat i2)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  let sub_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_CMLA_Z_ZZZi_H 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 256 =>
    (do
      (execute_CMLA_Z_ZZZi_H 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 512 =>
    (do
      (execute_CMLA_Z_ZZZi_H 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_CMLA_Z_ZZZi_H 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_CMLA_Z_ZZZi_H 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | _ => (pure (()))


def decode_CMLA_Z_ZZZi_S (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let index : Int := (BitVec.toNat i1)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  let sub_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_CMLA_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 256 =>
    (do
      (execute_CMLA_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 512 =>
    (do
      (execute_CMLA_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_CMLA_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_CMLA_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | _ => (pure (()))


def decode_SQRDCMLAH_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  let sub_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 256 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 512 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (sel_a))
        (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | _ => (pure (()))


def decode_SQRDCMLAH_Z_ZZZi_H (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let index : Int := (BitVec.toNat i2)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  let sub_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_H 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 256 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_H 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 512 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_H 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_H 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_H 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | _ => (pure (()))


def decode_SQRDCMLAH_Z_ZZZi_S (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let index : Int := (BitVec.toNat i1)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let sub_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  let sub_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 256 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 512 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_SQRDCMLAH_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b)) sub_i sub_r))
  | _ => (pure (()))


def decode_MUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_MUL_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_MUL_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_MUL_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_MUL_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_MUL_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_MUL_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_MUL_Z_ZZi_H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_MUL_Z_ZZi_H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_MUL_Z_ZZi_H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_MUL_Z_ZZi_H 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_MUL_Z_ZZi_H 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_MUL_Z_ZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let index : Int := (BitVec.toNat i2)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_MUL_Z_ZZi_S 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_MUL_Z_ZZi_S 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_MUL_Z_ZZi_S 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_MUL_Z_ZZi_S 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_MUL_Z_ZZi_S 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_MUL_Z_ZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let index : Int := (BitVec.toNat i1)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_MUL_Z_ZZi_D 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_MUL_Z_ZZi_D 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_MUL_Z_ZZi_D 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_MUL_Z_ZZi_D 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_MUL_Z_ZZi_D 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


end ArmFull.Functions
