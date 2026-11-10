import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0218
import ArmFull.Fn.M0227
import ArmFull.Fn.M0238
import ArmFull.Fn.M0244
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0258
import ArmFull.Fn.M0840
import ArmFull.Fn.M1002
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071
import ArmFull.Fn.M1072
import ArmFull.Fn.M1086

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

def decode_SCVTF_MZ_Z_4 (Zn : (BitVec 3)) (U : (BitVec 1)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let is_unsigned : Bool := false
  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
  let rounding ← (( do (FPRoundingMode w__1) ) : SailM FPRounding )
  match VL with
  | 128 =>
    (do
      (execute_SCVTF_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 256 =>
    (do
      (execute_SCVTF_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 512 =>
    (do
      (execute_SCVTF_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 1024 =>
    (do
      (execute_SCVTF_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | 2048 =>
    (do
      (execute_SCVTF_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (n)) nreg
        rounding is_unsigned))
  | _ => (pure (()))


def decode_FRINTA_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEAWAY
  match VL with
  | 128 =>
    (do
      (execute_FRINTA_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 256 =>
    (do
      (execute_FRINTA_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 512 =>
    (do
      (execute_FRINTA_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 1024 =>
    (do
      (execute_FRINTA_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 2048 =>
    (do
      (execute_FRINTA_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | _ => (pure (()))


def decode_FRINTM_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_NEGINF
  match VL with
  | 128 =>
    (do
      (execute_FRINTM_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 256 =>
    (do
      (execute_FRINTM_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 512 =>
    (do
      (execute_FRINTM_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 1024 =>
    (do
      (execute_FRINTM_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 2048 =>
    (do
      (execute_FRINTM_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | _ => (pure (()))


def decode_FRINTN_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEEVEN
  match VL with
  | 128 =>
    (do
      (execute_FRINTN_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 256 =>
    (do
      (execute_FRINTN_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 512 =>
    (do
      (execute_FRINTN_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 1024 =>
    (do
      (execute_FRINTN_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 2048 =>
    (do
      (execute_FRINTN_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | _ => (pure (()))


def decode_FRINTP_MZ_Z_2 (size : (BitVec 2)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0#1))
  let d : Int := (BitVec.toNat (Zd +++ 0#1))
  let nreg : Nat := 2
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_POSINF
  match VL with
  | 128 =>
    (do
      (execute_FRINTP_MZ_Z_2 128 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 256 =>
    (do
      (execute_FRINTP_MZ_Z_2 256 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 512 =>
    (do
      (execute_FRINTP_MZ_Z_2 512 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 1024 =>
    (do
      (execute_FRINTP_MZ_Z_2 1024 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 2048 =>
    (do
      (execute_FRINTP_MZ_Z_2 2048 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | _ => (pure (()))


def decode_FRINTA_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEAWAY
  match VL with
  | 128 =>
    (do
      (execute_FRINTA_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 256 =>
    (do
      (execute_FRINTA_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 512 =>
    (do
      (execute_FRINTA_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 1024 =>
    (do
      (execute_FRINTA_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 2048 =>
    (do
      (execute_FRINTA_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | _ => (pure (()))


def decode_FRINTM_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_NEGINF
  match VL with
  | 128 =>
    (do
      (execute_FRINTM_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 256 =>
    (do
      (execute_FRINTM_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 512 =>
    (do
      (execute_FRINTM_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 1024 =>
    (do
      (execute_FRINTM_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 2048 =>
    (do
      (execute_FRINTM_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | _ => (pure (()))


def decode_FRINTN_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_TIEEVEN
  match VL with
  | 128 =>
    (do
      (execute_FRINTN_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 256 =>
    (do
      (execute_FRINTN_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 512 =>
    (do
      (execute_FRINTN_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 1024 =>
    (do
      (execute_FRINTN_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 2048 =>
    (do
      (execute_FRINTN_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | _ => (pure (()))


def decode_FRINTP_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
  let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
  let nreg : Nat := 4
  let exact : Bool := false
  let rounding : FPRounding := FPRounding_POSINF
  match VL with
  | 128 =>
    (do
      (execute_FRINTP_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 256 =>
    (do
      (execute_FRINTP_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 512 =>
    (do
      (execute_FRINTP_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 1024 =>
    (do
      (execute_FRINTP_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | 2048 =>
    (do
      (execute_FRINTP_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) exact (Sail.Int.toNatChecked (n)) nreg
        rounding))
  | _ => (pure (()))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def execute_LDR_ZT_BR__ (n : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 512 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7564) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 7565) 512) ) : SailM (BitVec 512) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSME MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (FailTransaction TMFailure_ERR false))
  else (pure (()))
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let aligned : Bool := (IsAligned__1 base 16)
  let w__6 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AlignmentEnforced ()))
    else (pure false) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      let w__7 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort base w__7))
  else (pure (()))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__8 ← (( do (AArch64_MemSingle_read (BitVec.addInt base e) 1 accdesc aligned) ) :
            SailM (BitVec (1 * 8)) )
          (Elem_set result e 8 w__8)
      (pure loop_vars)) ) : SailM (BitVec 512) )
  (ZT0_set 512 result)


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 31 -/
def execute_STR_ZT_BR__ (n : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 512 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7566) 64) ) : SailM (BitVec 64) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSME MemOp_STORE nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (FailTransaction TMFailure_ERR false))
  else (pure (()))
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let aligned : Bool := (IsAligned__1 base 16)
  let w__6 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AlignmentEnforced ()))
    else (pure false) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      let w__7 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort base w__7))
  else (pure (()))
  let loop_e_lower : Nat := 0
  let loop_e_upper : Int := (elements -i 1)
  (do
    let mut loop_vars := ()
    for e in [loop_e_lower:loop_e_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__8 ← (( do (Elem_read table e 8) ) : SailM (BitVec (1 * 8)) )
        (AArch64_MemSingle_set (BitVec.addInt base e) 1 accdesc aligned w__8)
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 16 ∧
  List.elem da [0, 1] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPA_ZA_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7571)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize))
                  ) : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 col esize))
                  ) : SailM (BitVec esize) )
                let element3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then
                        (do
                          (FPNeg element1))
                      else (pure (element1)) ) : SailM (BitVec esize) )
                    let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (FPMulAdd_ZA element3 element1 element2 w__4) ) : SailM
                      (BitVec esize) )
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth w__5)))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 16 ∧
  List.elem da [0, 1] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_FMOPS_ZA_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7572)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize))
                  ) : SailM (BitVec esize) )
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 col esize))
                  ) : SailM (BitVec esize) )
                let element3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then
                        (do
                          (FPNeg element1))
                      else (pure (element1)) ) : SailM (BitVec esize) )
                    let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (FPMulAdd_ZA element3 element1 element2 w__4) ) : SailM
                      (BitVec esize) )
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth w__5)))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_16 : Nat, m : Nat, n : Nat, k_sub_op
  : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem da [0, 1] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧ (is_VL VL) ∧ dim_dim_16 = (VL / 16 * (VL / 16 * 16)) -/
def execute_BFMOPA_ZA_PP_ZZ_16 (VL : Nat) (dim_dim_16 : Nat) (a : Nat) (b : Nat) (da : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da 16 dim_dim_16)) ) : SailM
    (BitVec dim_dim_16) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7573)
      (Sail.Int.toNatChecked (dim_dim_16)))) ) : SailM (BitVec dim_dim_16) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do (Elem_read operand1 row 16) ) : SailM (BitVec 16) )
                let element2 ← (( do (Elem_read operand2 col 16) ) : SailM (BitVec 16) )
                let element3 ← (( do (Elem_read operand3 ((row *i dim) +i col) 16) ) : SailM
                  (BitVec 16) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row 16)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col 16))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let element1 ← (( do
                      if (sub_op : Bool)
                      then
                        (do
                          (BFNeg (k_N := 16) element1))
                      else (pure (element1)) ) : SailM (BitVec 16) )
                    let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                    let w__5 ← (( do (BFMulAdd_ZA (k_N := 16) element3 element1 element2 w__4) ) :
                      SailM (BitVec 16) )
                    (Elem_set result ((row *i dim) +i col) 16 w__5))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) 16 element3))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_16) )
  (ZAtile_set VL da 16 dim_dim_16 (Sail.BitVec.castWidth result))


end ArmFull.Functions
