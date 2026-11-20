module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0901
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

def decode_EOR_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_EOR_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EOR_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_EORS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_EORS_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EORS_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EORS_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EORS_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_EORS_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_NAND_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_NAND_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NAND_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NAND_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NAND_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NAND_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_NANDS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_NANDS_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NANDS_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NANDS_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NANDS_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NANDS_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_NOR_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_NOR_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NOR_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NOR_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NOR_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NOR_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_NORS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_NORS_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NORS_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NORS_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NORS_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_NORS_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_ORN_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_ORN_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORN_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORN_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORN_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORN_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_ORNS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_ORNS_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORNS_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORNS_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORNS_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORNS_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_ORR_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_ORR_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORR_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORR_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORR_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORR_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_ORRS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
          (execute_ORRS_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORRS_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORRS_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORRS_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ORRS_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_SEL_P_P_PP__ (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_P_P_PP__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_P_P_PP__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_P_P_PP__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_P_P_PP__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_P_P_PP__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_PFIRST_P_P_P__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pdn : (BitVec 4)) : SailM Unit := do
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
      let dn : Int := (BitVec.toNat Pdn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFIRST_P_P_P__ 128 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (g))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFIRST_P_P_P__ 256 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (g))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFIRST_P_P_P__ 512 (Sail.Int.toNatChecked (dn)) esize (Sail.Int.toNatChecked (g))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFIRST_P_P_P__ 1024 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (g))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFIRST_P_P_P__ 2048 (Sail.Int.toNatChecked (dn)) esize
            (Sail.Int.toNatChecked (g))))
      | _ => (pure (())))


end ArmFull.Functions
