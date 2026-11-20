module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0902 set_option backward.proofsInPublic true @[expose] public section

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

def decode_PNEXT_P_P_P__ (size : (BitVec 2)) (Pv : (BitVec 4)) (Pdn : (BitVec 4)) : SailM Unit := do
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
      let v : Int := (BitVec.toNat Pv)
      let dn : Int := (BitVec.toNat Pdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PNEXT_P_P_P__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (v))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PNEXT_P_P_P__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (v))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PNEXT_P_P_P__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (v))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PNEXT_P_P_P__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (v))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PNEXT_P_P_P__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (v))))
      | _ => (pure (())))


def decode_RDVL_R_I__ (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
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
      let d : Int := (BitVec.toNat Rd)
      let imm : Int := (BitVec.toInt imm6)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDVL_R_I__ 128 (Sail.Int.toNatChecked (d)) imm))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDVL_R_I__ 256 (Sail.Int.toNatChecked (d)) imm))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDVL_R_I__ 512 (Sail.Int.toNatChecked (d)) imm))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDVL_R_I__ 1024 (Sail.Int.toNatChecked (d)) imm))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDVL_R_I__ 2048 (Sail.Int.toNatChecked (d)) imm))
      | _ => (pure (())))


def decode_SEL_Z_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pv : (BitVec 4)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let v : Int := (BitVec.toNat Pv)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (v))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (v))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (v))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (v))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (v))))
      | _ => (pure (())))


def decode_LSL_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let shift : Int := ((BitVec.toNat (tsize +++ imm3)) -i esize)
      match esize with
      | 8 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 16 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 32 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 64 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSL_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | _ =>
        (do
          ArmFull.assert false "sail-inputs/16-instrs64_sve.sail:31348.22-31348.23"
          throw Error.Exit))


def decode_LSR_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let shift : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
      match esize with
      | 8 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 16 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 32 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 64 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_LSR_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | _ =>
        (do
          ArmFull.assert false "sail-inputs/16-instrs64_sve.sail:31492.22-31492.23"
          throw Error.Exit))


def decode_ASR_Z_ZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let shift : Int := ((2 *i esize) -i (BitVec.toNat (tsize +++ imm3)))
      match esize with
      | 8 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 16 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 32 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 64 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 128 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 256 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 512 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 1024 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_ASR_Z_ZI__ 2048 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | _ =>
        (do
          ArmFull.assert false "sail-inputs/16-instrs64_sve.sail:31637.22-31637.23"
          throw Error.Exit))


end ArmFull.Functions
