module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0920
public import ArmFull.Fn.M0921 set_option backward.proofsInPublic true @[expose] public section

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

def decode_SBCLT_Z_ZZZ__ (sz : (BitVec 1)) (Zm : (BitVec 5)) (T : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
          (execute_SBCLT_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLT_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLT_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLT_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SBCLT_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SMULH_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let is_unsigned : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SMULH_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | _ => (pure (())))


def decode_UMULH_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let is_unsigned : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UMULH_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) is_unsigned))
      | _ => (pure (())))


def decode_SCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
          (execute_SCLAMP_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SCLAMP_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SCLAMP_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SCLAMP_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SCLAMP_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (U : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
          (execute_UCLAMP_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCLAMP_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCLAMP_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCLAMP_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UCLAMP_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_REVD_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let swsize : Nat := 64
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_REVD_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) swsize))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_REVD_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) swsize))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_REVD_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) swsize))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_REVD_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) swsize))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_REVD_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (n)) swsize))
      | _ => (pure (())))


def decode_PSEL_P_PPi__ (i1 : (BitVec 1)) (tszh : (BitVec 1)) (tszl : (BitVec 3)) (Rv : (BitVec 2)) (Pn : (BitVec 4)) (S : (BitVec 1)) (Pm : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let imm5 : (BitVec 5) := ((i1 +++ tszh) +++ tszl)
      let esize : Int := 8
      let imm ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 5694) 0 15))) ) :
        SailM Nat )
      let (esize, imm) ← (( do
        match (BitVec.setWidth 4 (tszh +++ tszl)) with
        | 0b0000 =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | 0b1000 =>
          (let esize : Int := 64
          let imm : Nat :=
            (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm5 4)])))
          (pure ((esize, imm))))
        | b__0 =>
          (let (esize, imm) : (Int × Nat) :=
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 2 0)) == (0b100#3 : (BitVec 3))) : Bool)
            then
              (let esize : Int := 32
              let imm : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 3))
              (esize, imm))
            else
              (let (esize, imm) : (Int × Nat) :=
                if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 1 0)) == (0b10#2 : (BitVec 2))) : Bool)
                then
                  (let esize : Int := 16
                  let imm : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 2))
                  (esize, imm))
                else
                  (let esize : Int := 8
                  let imm : Nat := (BitVec.toNat (Sail.BitVec.extractLsb imm5 4 1))
                  (esize, imm))
              (esize, imm))
          (pure ((esize, imm)))) ) : SailM (Int × Nat) )
      let imm : Int := imm
      let esize : Int := esize
      let n : Int := (BitVec.toNat Pn)
      let m : Int := (BitVec.toNat Pm)
      let d : Int := (BitVec.toNat Pd)
      let v : Int := (BitVec.toNat (0b011#3 +++ Rv))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PSEL_P_PPi__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (v))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PSEL_P_PPi__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (v))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PSEL_P_PPi__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (v))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PSEL_P_PPi__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (v))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PSEL_P_PPi__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (v))))
      | _ => (pure (())))


def decode_WHILELO_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      let rsize : Nat := 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d0 : Int := (BitVec.toNat (Pd +++ 0#1))
      let d1 : Int := (BitVec.toNat (Pd +++ 1#1))
      let is_unsigned : Bool := true
      let op : SVECmp := Cmp_LT
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELO_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | _ => (pure (())))


def decode_WHILELS_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      let rsize : Nat := 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d0 : Int := (BitVec.toNat (Pd +++ 0#1))
      let d1 : Int := (BitVec.toNat (Pd +++ 1#1))
      let is_unsigned : Bool := true
      let op : SVECmp := Cmp_LE
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELS_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | _ => (pure (())))


def decode_WHILELT_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      let rsize : Nat := 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d0 : Int := (BitVec.toNat (Pd +++ 0#1))
      let d1 : Int := (BitVec.toNat (Pd +++ 1#1))
      let is_unsigned : Bool := false
      let op : SVECmp := Cmp_LT
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELT_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | _ => (pure (())))


def decode_WHILELE_PP_RR__ (size : (BitVec 2)) (Rm : (BitVec 5)) (U : (BitVec 1)) (lt : (BitVec 1)) (Rn : (BitVec 5)) (Pd : (BitVec 3)) (eq : (BitVec 1)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
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
      let rsize : Nat := 64
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      let d0 : Int := (BitVec.toNat (Pd +++ 0#1))
      let d1 : Int := (BitVec.toNat (Pd +++ 1#1))
      let is_unsigned : Bool := false
      let op : SVECmp := Cmp_LE
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_PP_RR__ 128 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_PP_RR__ 256 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_PP_RR__ 512 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_PP_RR__ 1024 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_WHILELE_PP_RR__ 2048 (Sail.Int.toNatChecked (d0)) (Sail.Int.toNatChecked (d1))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
            op rsize is_unsigned))
      | _ => (pure (())))


end ArmFull.Functions
