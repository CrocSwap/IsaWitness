module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0888
public import ArmFull.Fn.M0889
public import ArmFull.Fn.M0890 set_option backward.proofsInPublic true @[expose] public section

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

def decode_WHILEGT_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let rsize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Pd)
      let is_unsigned : Bool := false
      let op : SVECmp := Cmp_GT
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_P_P_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_P_P_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_P_P_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_P_P_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGT_P_P_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | _ => (pure (())))


def decode_WHILEGE_P_P_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (eq : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let rsize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Pd)
      let is_unsigned : Bool := false
      let op : SVECmp := Cmp_GE
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_P_P_RR__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_P_P_RR__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_P_P_RR__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_P_P_RR__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILEGE_P_P_RR__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op
            (Sail.Int.toNatChecked (rsize)) is_unsigned))
      | _ => (pure (())))


def decode_CMPEQ_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_EQ
      let imm : Int := (BitVec.toInt imm5)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPEQ_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPEQ_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPEQ_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPEQ_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPEQ_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | _ => (pure (())))


def decode_CMPNE_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_NE
      let imm : Int := (BitVec.toInt imm5)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPNE_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPNE_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPNE_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPNE_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPNE_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | _ => (pure (())))


def decode_CMPHS_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_GE
      let imm : Int := (BitVec.toNat imm7)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHS_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHS_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHS_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHS_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHS_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | _ => (pure (())))


def decode_CMPHI_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_GT
      let imm : Int := (BitVec.toNat imm7)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHI_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHI_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHI_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHI_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPHI_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | _ => (pure (())))


def decode_CMPLO_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_LT
      let imm : Int := (BitVec.toNat imm7)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLO_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLO_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLO_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLO_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLO_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | _ => (pure (())))


def decode_CMPLS_P_P_ZI__ (size : (BitVec 2)) (imm7 : (BitVec 7)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_LE
      let imm : Int := (BitVec.toNat imm7)
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLS_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLS_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLS_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLS_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLS_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n)) op
            is_unsigned))
      | _ => (pure (())))


def decode_CMPGE_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_GE
      let imm : Int := (BitVec.toInt imm5)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGE_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGE_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGE_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGE_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGE_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | _ => (pure (())))


def decode_CMPGT_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_GT
      let imm : Int := (BitVec.toInt imm5)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGT_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGT_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGT_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGT_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPGT_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | _ => (pure (())))


def decode_CMPLT_P_P_ZI__ (size : (BitVec 2)) (imm5 : (BitVec 5)) (lt : (BitVec 1)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (ne : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Pd)
      let op : SVECmp := Cmp_LT
      let imm : Int := (BitVec.toInt imm5)
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLT_P_P_ZI__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLT_P_P_ZI__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLT_P_P_ZI__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLT_P_P_ZI__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CMPLT_P_P_ZI__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) imm (Sail.Int.toNatChecked (n)) op is_unsigned))
      | _ => (pure (())))


end ArmFull.Functions
