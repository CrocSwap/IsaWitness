import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0144
import ArmFull.Fn.M0178
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0852
import ArmFull.Fn.M1087
import ArmFull.Fn.M1117
import ArmFull.Fn.M1118

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

def decode_FADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FMUL_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FMUL_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FMUL_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FMUL_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FMUL_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FSUB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FSUB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FSUB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FSUB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FSUB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FTSMUL_Z_ZZ__ (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5093)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7303.49-7303.50"
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPTrigSMul element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_FRECPS_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FRECPS_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FRECPS_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FRECPS_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FRECPS_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FRECPS_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FRSQRTS_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FRSQRTS_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FRSQRTS_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FRSQRTS_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FRSQRTS_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FRSQRTS_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FTSSEL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FTSSEL_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FTSSEL_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FTSSEL_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FTSSEL_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FTSSEL_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, imm : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧
  List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_FTMAD_Z_ZZI__ (VL : Nat) (dn : Nat) (esize : Nat) (imm : Nat) (m : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5098)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
            SailM (BitVec esize) )
          let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
            SailM (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7619.49-7619.50"
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (FPTrigMAdd imm element1 element2 w__0) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


def decode_FCADD_Z_P_ZZ__ (size : (BitVec 2)) (rot : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let dn : Int := (BitVec.toNat Zdn)
  let m : Int := (BitVec.toNat Zm)
  let sub_i : Bool := (rot == 0#1)
  let sub_r : Bool := (rot == 1#1)
  match VL with
  | 128 =>
    (do
      (execute_FCADD_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 256 =>
    (do
      (execute_FCADD_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 512 =>
    (do
      (execute_FCADD_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 1024 =>
    (do
      (execute_FCADD_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | 2048 =>
    (do
      (execute_FCADD_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) sub_i sub_r))
  | _ => (pure (()))


def decode_FCMLA_Z_P_ZZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (rot : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if ((size == 0b00#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let g : Int := (BitVec.toNat Pg)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let neg_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  let neg_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  match VL with
  | 128 =>
    (do
      (execute_FCMLA_Z_P_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i
        neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 256 =>
    (do
      (execute_FCMLA_Z_P_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i
        neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 512 =>
    (do
      (execute_FCMLA_Z_P_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i
        neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 1024 =>
    (do
      (execute_FCMLA_Z_P_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i
        neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 2048 =>
    (do
      (execute_FCMLA_Z_P_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i
        neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | _ => (pure (()))


def decode_FCMLA_Z_ZZZi_H (size : (BitVec 2)) (i2 : (BitVec 2)) (Zm : (BitVec 3)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let index : Int := (BitVec.toNat i2)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let neg_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  let neg_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  match VL with
  | 128 =>
    (do
      (execute_FCMLA_Z_ZZZi_H 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i neg_r
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 256 =>
    (do
      (execute_FCMLA_Z_ZZZi_H 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i neg_r
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 512 =>
    (do
      (execute_FCMLA_Z_ZZZi_H 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i neg_r
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 1024 =>
    (do
      (execute_FCMLA_Z_ZZZi_H 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        neg_i neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 2048 =>
    (do
      (execute_FCMLA_Z_ZZZi_H 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        neg_i neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | _ => (pure (()))


def decode_FCMLA_Z_ZZZi_S (size : (BitVec 2)) (i1 : (BitVec 1)) (Zm : (BitVec 4)) (rot : (BitVec 2)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 32
  let index : Int := (BitVec.toNat i1)
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let sel_a : Int := (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])))
  let sel_b : Int :=
    (BitVec.toNat (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)]))))
  let neg_i : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 1)])) == 1#1)
  let neg_r : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access rot 0)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          rot 1)])))
  match VL with
  | 128 =>
    (do
      (execute_FCMLA_Z_ZZZi_S 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i neg_r
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 256 =>
    (do
      (execute_FCMLA_Z_ZZZi_S 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i neg_r
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 512 =>
    (do
      (execute_FCMLA_Z_ZZZi_S 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) neg_i neg_r
        (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 1024 =>
    (do
      (execute_FCMLA_Z_ZZZi_S 1024 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        neg_i neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | 2048 =>
    (do
      (execute_FCMLA_Z_ZZZi_S 2048 (Sail.Int.toNatChecked (da)) esize
        (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
        neg_i neg_r (Sail.Int.toNatChecked (sel_a)) (Sail.Int.toNatChecked (sel_b))))
  | _ => (pure (()))


def decode_FMUL_Z_ZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let d : Int := (BitVec.toNat Zd)
  match VL with
  | 128 =>
    (do
      (execute_FMUL_Z_ZZi_H 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_FMUL_Z_ZZi_H 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_FMUL_Z_ZZi_H 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_FMUL_Z_ZZi_H 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_FMUL_Z_ZZi_H 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_FMLA_Z_ZZZi_H (i3h : (BitVec 1)) (i3l : (BitVec 2)) (Zm : (BitVec 3)) (op : (BitVec 1)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
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
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Nat := 16
  let index : Int := (BitVec.toNat (i3h +++ i3l))
  let n : Int := (BitVec.toNat Zn)
  let m : Int := (BitVec.toNat Zm)
  let da : Int := (BitVec.toNat Zda)
  let op1_neg : Bool := false
  let op3_neg : Bool := false
  match VL with
  | 128 =>
    (do
      (execute_FMLA_Z_ZZZi_H 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 256 =>
    (do
      (execute_FMLA_Z_ZZZi_H 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 512 =>
    (do
      (execute_FMLA_Z_ZZZi_H 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 1024 =>
    (do
      (execute_FMLA_Z_ZZZi_H 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | 2048 =>
    (do
      (execute_FMLA_Z_ZZZi_H 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (index))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) op1_neg op3_neg))
  | _ => (pure (()))


end ArmFull.Functions
