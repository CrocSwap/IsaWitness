import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0977
import ArmFull.Fn.M0982
import ArmFull.Fn.M0983
import ArmFull.Fn.M0984

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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let m : Int := (BitVec.toNat Zm)
  let dn : Int := (BitVec.toNat Zdn)
  match VL with
  | 128 =>
    (do
      (execute_AESE_Z_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_AESE_Z_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_AESE_Z_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_AESE_Z_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_AESE_Z_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat Zdn)
  match VL with
  | 128 =>
    (do
      (execute_AESIMC_Z_Z__ 128 (Sail.Int.toNatChecked (dn))))
  | 256 =>
    (do
      (execute_AESIMC_Z_Z__ 256 (Sail.Int.toNatChecked (dn))))
  | 512 =>
    (do
      (execute_AESIMC_Z_Z__ 512 (Sail.Int.toNatChecked (dn))))
  | 1024 =>
    (do
      (execute_AESIMC_Z_Z__ 1024 (Sail.Int.toNatChecked (dn))))
  | 2048 =>
    (do
      (execute_AESIMC_Z_Z__ 2048 (Sail.Int.toNatChecked (dn))))
  | _ => (pure (()))


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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let dn : Int := (BitVec.toNat Zdn)
  match VL with
  | 128 =>
    (do
      (execute_AESMC_Z_Z__ 128 (Sail.Int.toNatChecked (dn))))
  | 256 =>
    (do
      (execute_AESMC_Z_Z__ 256 (Sail.Int.toNatChecked (dn))))
  | 512 =>
    (do
      (execute_AESMC_Z_Z__ 512 (Sail.Int.toNatChecked (dn))))
  | 1024 =>
    (do
      (execute_AESMC_Z_Z__ 1024 (Sail.Int.toNatChecked (dn))))
  | 2048 =>
    (do
      (execute_AESMC_Z_Z__ 2048 (Sail.Int.toNatChecked (dn))))
  | _ => (pure (()))


def decode_RAX1_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE2SHA3 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_RAX1_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_RAX1_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_RAX1_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_RAX1_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_RAX1_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_SM4E_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2SM4 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let m : Int := (BitVec.toNat Zm)
  let dn : Int := (BitVec.toNat Zdn)
  match VL with
  | 128 =>
    (do
      (execute_SM4E_Z_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | 256 =>
    (do
      (execute_SM4E_Z_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | 512 =>
    (do
      (execute_SM4E_Z_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | 1024 =>
    (do
      (execute_SM4E_Z_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | 2048 =>
    (do
      (execute_SM4E_Z_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (m))))
  | _ => (pure (()))


def decode_SM4EKEY_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVE2SM4 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_SM4EKEY_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_SM4EKEY_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_SM4EKEY_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_SM4EKEY_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_SM4EKEY_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
        (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_PRFB_I_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_PRFB_I_P_BZ_S_x32_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFB_I_P_BZ_S_x32_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFB_I_P_BZ_S_x32_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFB_I_P_BZ_S_x32_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFB_I_P_BZ_S_x32_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFH_I_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale : Nat := 1
  match VL with
  | 128 =>
    (do
      (execute_PRFH_I_P_BZ_S_x32_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFH_I_P_BZ_S_x32_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFH_I_P_BZ_S_x32_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFH_I_P_BZ_S_x32_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFH_I_P_BZ_S_x32_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFW_I_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale : Nat := 2
  match VL with
  | 128 =>
    (do
      (execute_PRFW_I_P_BZ_S_x32_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFW_I_P_BZ_S_x32_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFW_I_P_BZ_S_x32_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFW_I_P_BZ_S_x32_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFW_I_P_BZ_S_x32_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFD_I_P_BZ_S_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale : Nat := 3
  match VL with
  | 128 =>
    (do
      (execute_PRFD_I_P_BZ_S_x32_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFD_I_P_BZ_S_x32_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFD_I_P_BZ_S_x32_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFD_I_P_BZ_S_x32_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFD_I_P_BZ_S_x32_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFB_I_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 0
  let offset : Int := (BitVec.toNat imm5)
  match VL with
  | 128 =>
    (do
      (execute_PRFB_I_P_AI_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFB_I_P_AI_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFB_I_P_AI_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFB_I_P_AI_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFB_I_P_AI_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFH_I_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 1
  let offset : Int := (BitVec.toNat imm5)
  match VL with
  | 128 =>
    (do
      (execute_PRFH_I_P_AI_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFH_I_P_AI_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFH_I_P_AI_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFH_I_P_AI_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFH_I_P_AI_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFW_I_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 2
  let offset : Int := (BitVec.toNat imm5)
  match VL with
  | 128 =>
    (do
      (execute_PRFW_I_P_AI_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFW_I_P_AI_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFW_I_P_AI_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFW_I_P_AI_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFW_I_P_AI_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFD_I_P_AI_S (msz : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let scale : Nat := 3
  let offset : Int := (BitVec.toNat imm5)
  match VL with
  | 128 =>
    (do
      (execute_PRFD_I_P_AI_S 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFD_I_P_AI_S 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFD_I_P_AI_S 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFD_I_P_AI_S 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFD_I_P_AI_S 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (level))
        (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (offset)) pref_hint scale stream))
  | _ => (pure (()))


def decode_PRFB_I_P_BZ_D_x32_scaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (msz : (BitVec 2)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (prfop : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 64
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Zm)
  let level : Int := (BitVec.toNat (Sail.BitVec.extractLsb prfop 2 1))
  let stream : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 0)])) == 1#1)
  let pref_hint : PrefetchHint :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prfop 3)])) == 0#1) : Bool)
    then Prefetch_READ
    else Prefetch_WRITE
  let offs_size : Nat := 32
  let offs_unsigned : Bool := (xs == 0#1)
  let scale : Nat := 0
  match VL with
  | 128 =>
    (do
      (execute_PRFB_I_P_BZ_D_x32_scaled 128 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 256 =>
    (do
      (execute_PRFB_I_P_BZ_D_x32_scaled 256 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 512 =>
    (do
      (execute_PRFB_I_P_BZ_D_x32_scaled 512 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 1024 =>
    (do
      (execute_PRFB_I_P_BZ_D_x32_scaled 1024 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | 2048 =>
    (do
      (execute_PRFB_I_P_BZ_D_x32_scaled 2048 esize (Sail.Int.toNatChecked (g))
        (Sail.Int.toNatChecked (level)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        offs_size offs_unsigned pref_hint scale stream))
  | _ => (pure (()))


end ArmFull.Functions
