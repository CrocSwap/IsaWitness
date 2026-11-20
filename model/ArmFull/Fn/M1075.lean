module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0988
public import ArmFull.Fn.M0990
public import ArmFull.Fn.M0991
public import ArmFull.Fn.M1006
public import ArmFull.Fn.M1017
public import ArmFull.Fn.M1018 set_option backward.proofsInPublic true @[expose] public section

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

def decode_ZIP1_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      let part : Nat := 0
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP1_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP1_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP1_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP1_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP1_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | _ => (pure (())))


def decode_ZIP2_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      let part : Nat := 1
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | _ => (pure (())))


def decode_UZP1_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      let part : Nat := 0
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP1_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP1_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP1_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP1_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP1_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | _ => (pure (())))


def decode_UZP2_Z_ZZ_Q (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      let part : Nat := 1
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP2_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP2_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP2_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP2_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP2_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n)) part))
      | _ => (pure (())))


def decode_COMPACT_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
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
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_COMPACT_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_COMPACT_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_COMPACT_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_COMPACT_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_COMPACT_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_SETFFR_F__ (_ : Unit) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SETFFR_F__ 128))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SETFFR_F__ 256))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SETFFR_F__ 512))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SETFFR_F__ 1024))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SETFFR_F__ 2048))
      | _ => (pure (())))


def decode_RDFFR_P_F__ (S : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Pd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_F__ 128 (Sail.Int.toNatChecked (d))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_F__ 256 (Sail.Int.toNatChecked (d))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_F__ 512 (Sail.Int.toNatChecked (d))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_F__ 1024 (Sail.Int.toNatChecked (d))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_F__ 2048 (Sail.Int.toNatChecked (d))))
      | _ => (pure (())))


def decode_WRFFR_F_P__ (Pn : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Pn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WRFFR_F_P__ 128 (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WRFFR_F_P__ 256 (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WRFFR_F_P__ 512 (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WRFFR_F_P__ 1024 (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WRFFR_F_P__ 2048 (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_RDFFR_P_P_F__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let g : Int := (BitVec.toNat Pg)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_P_F__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_P_F__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_P_F__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_P_F__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFR_P_P_F__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | _ => (pure (())))


def decode_RDFFRS_P_P_F__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let g : Int := (BitVec.toNat Pg)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFRS_P_P_F__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFRS_P_P_F__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFRS_P_P_F__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFRS_P_P_F__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_RDFFRS_P_P_F__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (g))
            setflags))
      | _ => (pure (())))


def decode_PMULLT_Z_ZZ_Q (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2PMULL128 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLT_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLT_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLT_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLT_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLT_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_PMULLB_Z_ZZ_Q (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2PMULL128 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLB_Z_ZZ_Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLB_Z_ZZ_Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLB_Z_ZZ_Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLB_Z_ZZ_Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PMULLB_Z_ZZ_Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_MATCH_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
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
         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (1#1 : (BitVec 1))) : Bool)
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
          let d : Int := (BitVec.toNat Pd)
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_MATCH_P_P_ZZ__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_MATCH_P_P_ZZ__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_MATCH_P_P_ZZ__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_MATCH_P_P_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_MATCH_P_P_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_NMATCH_P_P_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
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
         (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 1 1)) == (1#1 : (BitVec 1))) : Bool)
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
          let d : Int := (BitVec.toNat Pd)
          let n : Int := (BitVec.toNat Zn)
          let m : Int := (BitVec.toNat Zm)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_NMATCH_P_P_ZZ__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_NMATCH_P_P_ZZ__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_NMATCH_P_P_ZZ__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_NMATCH_P_P_ZZ__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_NMATCH_P_P_ZZ__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


end ArmFull.Functions
