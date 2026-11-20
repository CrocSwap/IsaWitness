module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0918
public import ArmFull.Fn.M0919 set_option backward.proofsInPublic true @[expose] public section

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

def decode_SUQADD_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUQADD_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUQADD_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUQADD_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUQADD_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SUQADD_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_USQADD_Z_P_ZZ__ (size : (BitVec 2)) (S : (BitVec 1)) (U : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USQADD_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USQADD_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USQADD_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USQADD_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_USQADD_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_SLI_Z_ZZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
              (execute_SLI_Z_ZZI__ 128 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 256 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 512 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 1024 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 2048 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 16 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 128 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 256 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 512 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 1024 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 2048 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 32 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 128 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 256 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 512 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 1024 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 2048 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 64 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 128 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 256 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 512 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 1024 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SLI_Z_ZZI__ 2048 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | _ =>
        (do
          ArmFull.assert false "sail-inputs/16-instrs64_sve.sail:49830.22-49830.23"
          throw Error.Exit))


def decode_SRI_Z_ZZI__ (tszh : (BitVec 2)) (tszl : (BitVec 2)) (imm3 : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
              (execute_SRI_Z_ZZI__ 128 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 256 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 512 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 1024 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 2048 (Sail.Int.toNatChecked (d)) 8 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 16 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 128 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 256 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 512 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 1024 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 2048 (Sail.Int.toNatChecked (d)) 16 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 32 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 128 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 256 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 512 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 1024 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 2048 (Sail.Int.toNatChecked (d)) 32 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | 64 =>
        (do
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 128 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 256 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 512 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 1024 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SRI_Z_ZZI__ 2048 (Sail.Int.toNatChecked (d)) 64 (Sail.Int.toNatChecked (n))
                shift))
          | _ => (pure (())))
      | _ =>
        (do
          ArmFull.assert false "sail-inputs/16-instrs64_sve.sail:49978.22-49978.23"
          throw Error.Exit))


def decode_TBX_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_TBX_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_TBX_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_TBX_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_TBX_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_TBX_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_URECPE_Z_P_Z__ (size : (BitVec 2)) (Q : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      if ((size != 0b10#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Nat := 32
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URECPE_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URECPE_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URECPE_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URECPE_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URECPE_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_URSQRTE_Z_P_Z__ (size : (BitVec 2)) (Q : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      if ((size != 0b10#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Nat := 32
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URSQRTE_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URSQRTE_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URSQRTE_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URSQRTE_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_URSQRTE_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) esize
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_MATCH_P_P_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let eltspersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let w__2 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand2 ← (( do
    if (w__2 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5634)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__4 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let segmentbase : Int := (e -i (Nat.mod (Sail.Int.toNatChecked (e)) eltspersegment))
              let w__5 ← (( do
                (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize)))
                ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
              let result := (w__5 : (BitVec (Sail.Int.toNatChecked PL)))
              let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let loop_i_lower : Int := segmentbase
              let loop_i_upper : Int := ((segmentbase +i eltspersegment) -i 1)
              (do
                let mut loop_vars_1 := result
                for i in [loop_i_lower:loop_i_upper:1]i do
                  let result := loop_vars_1
                  loop_vars_1 ← do
                    let element2 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 i esize)) ) : SailM
                      (BitVec esize) )
                    if ((element1 == element2) : Bool)
                    then
                      (do
                        (Elem_set result e psize
                          (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 1#1 psize))))
                    else (pure (result))
                (pure loop_vars_1)))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__11 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
  (P_set d PL (Sail.BitVec.castWidth result))


end ArmFull.Functions
