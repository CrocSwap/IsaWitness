import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M1121
import ArmFull.Fn.M1122

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

def decode_FCVTXNT_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FCVTXNT_Z_P_Z_D2S 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCVTXNT_Z_P_Z_D2S 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCVTXNT_Z_P_Z_D2S 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCVTXNT_Z_P_Z_D2S 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCVTXNT_Z_P_Z_D2S 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      (execute_FCLAMP_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FCLAMP_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FCLAMP_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FCLAMP_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FCLAMP_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFMUL_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFMUL_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFMUL_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFMUL_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFMUL_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFSUB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFSUB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFSUB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFSUB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFSUB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFADD_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_BFADD_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_BFADD_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_BFADD_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_BFADD_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_BFADD_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_BFMUL_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_BFMUL_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_BFMUL_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_BFMUL_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_BFMUL_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_BFMUL_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_BFSUB_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_BFSUB_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_BFSUB_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_BFSUB_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_BFSUB_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_BFSUB_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_BFMLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BFMLA_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 256 =>
    (do
      (execute_BFMLA_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 512 =>
    (do
      (execute_BFMLA_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 1024 =>
    (do
      (execute_BFMLA_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 2048 =>
    (do
      (execute_BFMLA_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | _ => (pure (()))


def decode_BFMLS_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BFMLS_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 256 =>
    (do
      (execute_BFMLS_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 512 =>
    (do
      (execute_BFMLS_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 1024 =>
    (do
      (execute_BFMLS_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 2048 =>
    (do
      (execute_BFMLS_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | _ => (pure (()))


def decode_BFMLA_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BFMLA_Z_ZZZi_H 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 256 =>
    (do
      (execute_BFMLA_Z_ZZZi_H 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 512 =>
    (do
      (execute_BFMLA_Z_ZZZi_H 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 1024 =>
    (do
      (execute_BFMLA_Z_ZZZi_H 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 2048 =>
    (do
      (execute_BFMLA_Z_ZZZi_H 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | _ => (pure (()))


def decode_BFMLS_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := true
  let op3_neg : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_BFMLS_Z_ZZZi_H 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 256 =>
    (do
      (execute_BFMLS_Z_ZZZi_H 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 512 =>
    (do
      (execute_BFMLS_Z_ZZZi_H 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 1024 =>
    (do
      (execute_BFMLS_Z_ZZZi_H 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 2048 =>
    (do
      (execute_BFMLS_Z_ZZZi_H 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | _ => (pure (()))


def decode_BFMUL_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFMUL_Z_ZZi_H 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFMUL_Z_ZZi_H 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFMUL_Z_ZZi_H 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFMUL_Z_ZZi_H 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFMUL_Z_ZZi_H 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_BFMAXNM_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_BFMAXNM_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_BFMAXNM_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_BFMAXNM_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_BFMAXNM_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_BFMAXNM_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_BFMINNM_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_BFMINNM_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_BFMINNM_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_BFMINNM_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_BFMINNM_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_BFMINNM_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_BFMAX_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_BFMAX_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_BFMAX_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_BFMAX_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_BFMAX_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_BFMAX_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_BFMIN_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  match VL with
  | 128 =>
    (do
      (execute_BFMIN_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_BFMIN_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_BFMIN_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_BFMIN_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_BFMIN_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_BFCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_BFCLAMP_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_BFCLAMP_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_BFCLAMP_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_BFCLAMP_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_BFCLAMP_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


end ArmFull.Functions
