import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0202
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0852
import ArmFull.Fn.M0855

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

/-- Type quantifiers: d : Nat, datasize : Nat, esize : Nat, m : Nat, n : Nat, pairs : Int, part :
  Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  List.elem esize [8, 16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_transfer_vector_permute_zip (d : Nat) (datasize : Nat) (esize : Nat) (m : Nat) (n : Nat) (pairs : Int) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (V_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5032)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let base : Int := (part *i pairs)
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 (base +i p) esize)) )
            : SailM (BitVec esize) )
          let w__1 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__0)) )
            : SailM (BitVec datasize) )
          let result := (w__1 : (BitVec datasize))
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (base +i p) esize)) )
            : SailM (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec datasize) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FEXPA_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5097)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/instrs64_sve.sail:7557.49-7557.50"
          let w__0 ← (( do (FPExpA element) ) : SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, mbytes : Nat, n
  : Nat, osize : Nat, osize = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem mbytes [1, 2, 4, 8] ∧
  0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADR_Z_AZ_D_u32_scaled (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (mbytes : Nat) (n : Nat) (osize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let offs ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5189)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let addr ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
            (BitVec esize) )
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offs e esize)) ) : SailM
            (BitVec esize) )
          let offset ← (( do
            (asl_Int (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((osize -i 1))) 0)
              is_unsigned) ) : SailM Int )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt addr (offset *i mbytes))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, mbytes : Nat, n
  : Nat, osize : Nat, osize = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem mbytes [1, 2, 4, 8] ∧
  0 ≤ m ∧ m ≤ 31 ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADR_Z_AZ_D_s32_scaled (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (mbytes : Nat) (n : Nat) (osize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let offs ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5190)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let addr ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
            (BitVec esize) )
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offs e esize)) ) : SailM
            (BitVec esize) )
          let offset ← (( do
            (asl_Int (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((osize -i 1))) 0)
              is_unsigned) ) : SailM Int )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt addr (offset *i mbytes))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, mbytes : Nat, n
  : Nat, osize : Nat, List.elem osize [32, 64] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem mbytes [1, 2, 4, 8] ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ADR_Z_AZ_SD_same_scaled (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (mbytes : Nat) (n : Nat) (osize : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let offs ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5191)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let addr ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read base e esize)) ) : SailM
            (BitVec esize) )
          ArmFull.assert ((osize -i 1) <b esize) "sail-arm/instrs64_sve.sail:12914.46-12914.47"
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offs e esize)) ) : SailM
            (BitVec esize) )
          let offset ← (( do
            (asl_Int (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((osize -i 1))) 0)
              is_unsigned) ) : SailM Int )
          (Elem_set result e esize (Sail.BitVec.castWidth (BitVec.addInt addr (offset *i mbytes))))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_ADD_Z_ZI__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if (((size +++ sh) == 0b001#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm : Int := imm
  match VL with
  | 128 =>
    (do
      (execute_ADD_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 256 =>
    (do
      (execute_ADD_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 512 =>
    (do
      (execute_ADD_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 1024 =>
    (do
      (execute_ADD_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 2048 =>
    (do
      (execute_ADD_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | _ => (pure (()))


def decode_SUB_Z_ZI__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if (((size +++ sh) == 0b001#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm : Int := imm
  match VL with
  | 128 =>
    (do
      (execute_SUB_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 256 =>
    (do
      (execute_SUB_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 512 =>
    (do
      (execute_SUB_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 1024 =>
    (do
      (execute_SUB_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 2048 =>
    (do
      (execute_SUB_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | _ => (pure (()))


def decode_SUBR_Z_ZI__ (size : (BitVec 2)) (sh : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  if (((size +++ sh) == 0b001#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let dn : Int := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toNat imm8)
  let imm : Int :=
    if ((sh == 1#1) : Bool)
    then (Int.shiftl imm 8)
    else imm
  let imm : Int := imm
  match VL with
  | 128 =>
    (do
      (execute_SUBR_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 256 =>
    (do
      (execute_SUBR_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 512 =>
    (do
      (execute_SUBR_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 1024 =>
    (do
      (execute_SUBR_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 2048 =>
    (do
      (execute_SUBR_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | _ => (pure (()))


def decode_MUL_Z_ZI__ (size : (BitVec 2)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let imm : Int := (BitVec.toInt imm8)
  match VL with
  | 128 =>
    (do
      (execute_MUL_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 256 =>
    (do
      (execute_MUL_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 512 =>
    (do
      (execute_MUL_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 1024 =>
    (do
      (execute_MUL_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | 2048 =>
    (do
      (execute_MUL_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm))
  | _ => (pure (()))


def decode_UMAX_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let is_unsigned : Bool := true
  let imm ← (( do (asl_Int imm8 is_unsigned) ) : SailM Int )
  match VL with
  | 128 =>
    (do
      (execute_UMAX_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 256 =>
    (do
      (execute_UMAX_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 512 =>
    (do
      (execute_UMAX_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 1024 =>
    (do
      (execute_UMAX_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 2048 =>
    (do
      (execute_UMAX_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | _ => (pure (()))


def decode_SMAX_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let is_unsigned : Bool := false
  let imm ← (( do (asl_Int imm8 is_unsigned) ) : SailM Int )
  match VL with
  | 128 =>
    (do
      (execute_SMAX_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 256 =>
    (do
      (execute_SMAX_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 512 =>
    (do
      (execute_SMAX_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 1024 =>
    (do
      (execute_SMAX_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 2048 =>
    (do
      (execute_SMAX_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | _ => (pure (()))


def decode_UMIN_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let is_unsigned : Bool := true
  let imm ← (( do (asl_Int imm8 is_unsigned) ) : SailM Int )
  match VL with
  | 128 =>
    (do
      (execute_UMIN_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 256 =>
    (do
      (execute_UMIN_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 512 =>
    (do
      (execute_UMIN_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 1024 =>
    (do
      (execute_UMIN_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 2048 =>
    (do
      (execute_UMIN_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | _ => (pure (()))


def decode_SMIN_Z_ZI__ (size : (BitVec 2)) (U : (BitVec 1)) (imm8 : (BitVec 8)) (Zdn : (BitVec 5)) : SailM Unit := do
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
  let dn : Int := (BitVec.toNat Zdn)
  let is_unsigned : Bool := false
  let imm ← (( do (asl_Int imm8 is_unsigned) ) : SailM Int )
  match VL with
  | 128 =>
    (do
      (execute_SMIN_Z_ZI__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 256 =>
    (do
      (execute_SMIN_Z_ZI__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 512 =>
    (do
      (execute_SMIN_Z_ZI__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 1024 =>
    (do
      (execute_SMIN_Z_ZI__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | 2048 =>
    (do
      (execute_SMIN_Z_ZI__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize)) imm
        is_unsigned))
  | _ => (pure (()))


def decode_ADDPL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toInt imm6)
  match VL with
  | 128 =>
    (do
      (execute_ADDPL_R_RI__ 128 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADDPL_R_RI__ 256 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADDPL_R_RI__ 512 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADDPL_R_RI__ 1024 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADDPL_R_RI__ 2048 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ADDVL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
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
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toInt imm6)
  match VL with
  | 128 =>
    (do
      (execute_ADDVL_R_RI__ 128 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADDVL_R_RI__ 256 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADDVL_R_RI__ 512 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADDVL_R_RI__ 1024 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADDVL_R_RI__ 2048 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      (execute_ADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


end ArmFull.Functions
