module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0920 set_option backward.proofsInPublic true @[expose] public section

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

def decode_XAR_Z_ZZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let tsize : (BitVec 4) := (tszh +++ tszl)
      let esize : Int := 8
      let esize ← (( do
        match tsize with
        | 0b0000 =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | 0b0001 => (pure (8))
        | b__0 =>
          (let esize : Int :=
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
            then 16
            else
              (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b01#2 : (BitVec 2))) : Bool)
              then 32
              else 64)
          (pure (esize))) ) : SailM Int )
      let esize : Int := esize
      let m : Int := (BitVec.toNat Zm)
      let dn : Int := (BitVec.toNat Zdn)
      let rot : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
      match esize with
      | 8 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m))
                rot))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m))
                rot))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m))
                rot))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m))
                rot))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) 8 (Sail.Int.toNatChecked (m))
                rot))
          | _ => (pure (())))
      | 16 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m))
                rot))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m))
                rot))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m))
                rot))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m))
                rot))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) 16 (Sail.Int.toNatChecked (m))
                rot))
          | _ => (pure (())))
      | 32 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m))
                rot))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m))
                rot))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m))
                rot))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m))
                rot))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) 32 (Sail.Int.toNatChecked (m))
                rot))
          | _ => (pure (())))
      | 64 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 128 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m))
                rot))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 256 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m))
                rot))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 512 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m))
                rot))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 1024 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m))
                rot))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_XAR_Z_ZZI__ 2048 (Sail.Int.toNatChecked (dn)) 64 (Sail.Int.toNatChecked (m))
                rot))
          | _ => (pure (())))
      | _ =>
        (do
          ArmFull.assert false "sail-inputs/16-instrs64_sve.sail:52750.22-52750.23"
          throw Error.Exit))


def decode_BCAX_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let m : Int := (BitVec.toNat Zm)
      let k : Int := (BitVec.toNat Zk)
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BCAX_Z_ZZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BCAX_Z_ZZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BCAX_Z_ZZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BCAX_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BCAX_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_EOR3_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let m : Int := (BitVec.toNat Zm)
      let k : Int := (BitVec.toNat Zk)
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR3_Z_ZZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR3_Z_ZZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR3_Z_ZZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR3_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR3_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_BSL_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let m : Int := (BitVec.toNat Zm)
      let k : Int := (BitVec.toNat Zk)
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL_Z_ZZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL_Z_ZZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL_Z_ZZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_BSL1N_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let m : Int := (BitVec.toNat Zm)
      let k : Int := (BitVec.toNat Zk)
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL1N_Z_ZZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL1N_Z_ZZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL1N_Z_ZZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL1N_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL1N_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_BSL2N_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let m : Int := (BitVec.toNat Zm)
      let k : Int := (BitVec.toNat Zk)
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL2N_Z_ZZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL2N_Z_ZZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL2N_Z_ZZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL2N_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BSL2N_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_NBSL_Z_ZZZ__ (Zm : (BitVec 5)) (Zk : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let m : Int := (BitVec.toNat Zm)
      let k : Int := (BitVec.toNat Zk)
      let dn : Int := (BitVec.toNat Zdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NBSL_Z_ZZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NBSL_Z_ZZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NBSL_Z_ZZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NBSL_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NBSL_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (k))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_ADCLB_Z_ZZZ__ (sz : (BitVec 1)) (Zm : (BitVec 5)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLB_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLB_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLB_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLB_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLB_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_ADCLT_Z_ZZZ__ (sz : (BitVec 1)) (Zm : (BitVec 5)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ADCLT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SBCLB_Z_ZZZ__ (sz : (BitVec 1)) (Zm : (BitVec 5)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 32 (BitVec.toNat sz))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLB_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLB_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLB_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLB_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLB_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


end ArmFull.Functions
