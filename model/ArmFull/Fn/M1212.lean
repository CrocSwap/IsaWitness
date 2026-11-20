module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1138
public import ArmFull.Fn.M1172
public import ArmFull.Fn.M1173 set_option backward.proofsInPublic true @[expose] public section

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

def decode_FNMLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let da : Int := (BitVec.toNat Zda)
          let op1_neg : Bool := true
          let op3_neg : Bool := true
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLA_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLA_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLA_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLA_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLA_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | _ => (pure (()))))


def decode_FNMLS_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let da : Int := (BitVec.toNat Zda)
          let op1_neg : Bool := false
          let op3_neg : Bool := true
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLS_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLS_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLS_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLS_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMLS_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
          | _ => (pure (()))))


def decode_FMAD_Z_P_ZZZ__ (size : (BitVec 2)) (Za : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let dn : Int := (BitVec.toNat Zdn)
          let m : Int := (BitVec.toNat Zm)
          let a : Int := (BitVec.toNat Za)
          let op1_neg : Bool := false
          let op3_neg : Bool := false
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAD_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAD_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAD_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAD_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAD_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | _ => (pure (()))))


def decode_FMSB_Z_P_ZZZ__ (size : (BitVec 2)) (Za : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let dn : Int := (BitVec.toNat Zdn)
          let m : Int := (BitVec.toNat Zm)
          let a : Int := (BitVec.toNat Za)
          let op1_neg : Bool := true
          let op3_neg : Bool := false
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMSB_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMSB_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMSB_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMSB_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMSB_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | _ => (pure (()))))


def decode_FNMAD_Z_P_ZZZ__ (size : (BitVec 2)) (Za : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let dn : Int := (BitVec.toNat Zdn)
          let m : Int := (BitVec.toNat Zm)
          let a : Int := (BitVec.toNat Za)
          let op1_neg : Bool := true
          let op3_neg : Bool := true
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMAD_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMAD_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMAD_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMAD_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMAD_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | _ => (pure (()))))


def decode_FNMSB_Z_P_ZZZ__ (size : (BitVec 2)) (Za : (BitVec 5)) (N : (BitVec 1)) (op : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let dn : Int := (BitVec.toNat Zdn)
          let m : Int := (BitVec.toNat Zm)
          let a : Int := (BitVec.toNat Za)
          let op1_neg : Bool := false
          let op3_neg : Bool := true
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMSB_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMSB_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMSB_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMSB_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNMSB_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (a)) (Sail.Int.toNatChecked (dn))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) op1_neg op3_neg))
          | _ => (pure (()))))


def decode_FADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
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
          (execute_FADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
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
          (execute_FMUL_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMUL_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMUL_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMUL_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMUL_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
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
          (execute_FSUB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FSUB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FSUB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FSUB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FSUB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FTSMUL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5093)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:7303.49-7303.50"
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPTrigSMul element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_FRECPS_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
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
              (execute_FRECPS_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRECPS_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRECPS_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRECPS_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FRECPS_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


end ArmFull.Functions
