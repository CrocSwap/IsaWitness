module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1018
public import ArmFull.Fn.M1019
public import ArmFull.Fn.M1020 set_option backward.proofsInPublic true @[expose] public section

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

def decode_HISTCNT_Z_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((let b__0 := size
         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (0#1 : (BitVec 1))) : Bool)
         then true
         else false : Bool)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let d : Int := (BitVec.toNat Zd)
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTCNT_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTCNT_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTCNT_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTCNT_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTCNT_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_HISTSEG_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Nat := 8
          let d : Int := (BitVec.toNat Zd)
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTSEG_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTSEG_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTSEG_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTSEG_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_HISTSEG_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_BDEP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2BitPerm ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BDEP_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BDEP_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BDEP_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BDEP_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BDEP_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BEXT_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2BitPerm ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BEXT_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BEXT_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BEXT_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BEXT_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BEXT_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BGRP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2BitPerm ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BGRP_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BGRP_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BGRP_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BGRP_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BGRP_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SMMLA_Z_ZZZ__ (uns : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      let op1_unsigned : Bool := false
      let op2_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMMLA_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMMLA_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMMLA_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMMLA_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMMLA_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | _ => (pure (())))


def decode_UMMLA_Z_ZZZ__ (uns : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      let op1_unsigned : Bool := true
      let op2_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMMLA_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMMLA_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMMLA_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMMLA_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMMLA_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | _ => (pure (())))


def decode_USMMLA_Z_ZZZ__ (uns : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveInt8MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      let op1_unsigned : Bool := true
      let op2_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMMLA_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMMLA_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMMLA_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMMLA_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USMMLA_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) op1_unsigned op2_unsigned))
      | _ => (pure (())))


def decode_AESD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2AES ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let m : Int := (BitVec.toNat Zm)
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESD_Z_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESD_Z_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESD_Z_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_AESE_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2AES ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let m : Int := (BitVec.toNat Zm)
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESE_Z_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESE_Z_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESE_Z_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESE_Z_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESE_Z_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_AESIMC_Z_Z__ (size : (BitVec 2)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2AES ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESIMC_Z_Z__ 128 (Sail.Int.toNatChecked (dn))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESIMC_Z_Z__ 256 (Sail.Int.toNatChecked (dn))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESIMC_Z_Z__ 512 (Sail.Int.toNatChecked (dn))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESIMC_Z_Z__ 1024 (Sail.Int.toNatChecked (dn))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESIMC_Z_Z__ 2048 (Sail.Int.toNatChecked (dn))))
      | _ => (pure (())))


def decode_AESMC_Z_Z__ (size : (BitVec 2)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2AES ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESMC_Z_Z__ 128 (Sail.Int.toNatChecked (dn))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESMC_Z_Z__ 256 (Sail.Int.toNatChecked (dn))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESMC_Z_Z__ 512 (Sail.Int.toNatChecked (dn))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESMC_Z_Z__ 1024 (Sail.Int.toNatChecked (dn))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AESMC_Z_Z__ 2048 (Sail.Int.toNatChecked (dn))))
      | _ => (pure (())))


def decode_RAX1_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2SHA3 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RAX1_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RAX1_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RAX1_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RAX1_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RAX1_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


end ArmFull.Functions
