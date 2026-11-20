module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0904 set_option backward.proofsInPublic true @[expose] public section

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

def decode_BRKPAS_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let m : Int := (BitVec.toNat Pm)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPAS_P_P_PP__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPAS_P_P_PP__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPAS_P_P_PP__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPAS_P_P_PP__ 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPAS_P_P_PP__ 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            setflags))
      | _ => (pure (())))


def decode_BRKPB_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let m : Int := (BitVec.toNat Pm)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPB_P_P_PP__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPB_P_P_PP__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPB_P_P_PP__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPB_P_P_PP__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPB_P_P_PP__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_BRKPBS_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (B : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let m : Int := (BitVec.toNat Pm)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPBS_P_P_PP__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPBS_P_P_PP__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPBS_P_P_PP__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPBS_P_P_PP__ 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKPBS_P_P_PP__ 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            setflags))
      | _ => (pure (())))


def decode_BRKN_P_P_PP__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pdm : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let dm : Int := (BitVec.toNat Pdm)
      let setflags : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKN_P_P_PP__ 128 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKN_P_P_PP__ 256 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKN_P_P_PP__ 512 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKN_P_P_PP__ 1024 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKN_P_P_PP__ 2048 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_BRKNS_P_P_PP__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pdm : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let dm : Int := (BitVec.toNat Pdm)
      let setflags : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKNS_P_P_PP__ 128 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKNS_P_P_PP__ 256 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKNS_P_P_PP__ 512 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKNS_P_P_PP__ 1024 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKNS_P_P_PP__ 2048 (Sail.Int.toNatChecked (dm)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_INSR_Z_V__ (size : (BitVec 2)) (Vm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Vm)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_V__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_V__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_V__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_V__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_V__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_INSR_Z_R__ (size : (BitVec 2)) (Rm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Rm)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_R__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_R__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_R__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_R__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_INSR_Z_R__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_SDOT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let da : Int := (BitVec.toNat Zda)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SDOT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SDOT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SDOT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SDOT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_SDOT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_SDOT_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let index : Int := (BitVec.toNat i2)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SDOT_Z_ZZZi_D (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let index : Int := (BitVec.toNat i1)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_D 128 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_D 256 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_D 512 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_D 1024 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SDOT_Z_ZZZi_D 2048 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UDOT_Z_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          let da : Int := (BitVec.toNat Zda)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UDOT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UDOT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UDOT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UDOT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_UDOT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_UDOT_Z_ZZZi_S (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let index : Int := (BitVec.toNat i2)
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UDOT_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UDOT_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UDOT_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UDOT_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UDOT_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
            (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


end ArmFull.Functions
