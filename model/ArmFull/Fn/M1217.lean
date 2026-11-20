module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1138
public import ArmFull.Fn.M1176
public import ArmFull.Fn.M1177 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, da : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ da ∧ da ≤ 31 ∧ (is_VL VL) -/
def execute_BFMMLA_Z_ZZZ__ (VL : Nat) (da : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read da VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5164)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let op1 ← (( do (undefined_bitvector_at (← occLabel 5165) 128) ) : SailM (BitVec 128) )
  let op2 ← (( do (undefined_bitvector_at (← occLabel 5166) 128) ) : SailM (BitVec 128) )
  let addend ← (( do (undefined_bitvector_at (← occLabel 5167) 128) ) : SailM (BitVec 128) )
  let res ← (( do (undefined_bitvector_at (← occLabel 5168) 128) ) : SailM (BitVec 128) )
  let (addend, op1, op2, res, result) ← (( do
    let loop_s_lower : Nat := 0
    let loop_s_upper : Int := (segments -i 1)
    (do
      let mut loop_vars := (addend, op1, op2, res, result)
      for s in [loop_s_lower:loop_s_upper:1]i do
        let (addend, op1, op2, res, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do (Elem_read operand1 s 128) ) : SailM (BitVec 128) )
          let op1 := (w__0 : (BitVec 128))
          let w__1 ← (( do (Elem_read operand2 s 128) ) : SailM (BitVec 128) )
          let op2 := (w__1 : (BitVec 128))
          let w__2 ← (( do (Elem_read operand3 s 128) ) : SailM (BitVec 128) )
          let addend := (w__2 : (BitVec 128))
          let w__3 ← (( do (BFMatMulAdd (k_N := 128) addend op1 op2) ) : SailM (BitVec 128) )
          let res := (w__3 : (BitVec 128))
          let w__4 ← (( do (Elem_set result s 128 res) ) : SailM (BitVec VL) )
          let result := (w__4 : (BitVec VL))
          (pure ((addend, op1, op2, res, result)))
      (pure loop_vars)) ) : SailM
    ((BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec 128) × (BitVec VL)) )
  (Z_set da VL (Sail.BitVec.castWidth result))


def decode_FCVTNT_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_D2S 128 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_D2S 256 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_D2S 512 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_D2S 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_D2S 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FCVTNT_Z_P_Z_S2H (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_S2H 128 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_S2H 256 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_S2H 512 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_S2H 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTNT_Z_P_Z_S2H 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FCVTLT_Z_P_Z_S2D (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_S2D 128 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_S2D 256 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_S2D 512 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_S2D 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_S2D 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FCVTLT_Z_P_Z_H2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 32
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_H2S 128 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_H2S 256 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_H2S 512 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_H2S 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTLT_Z_P_Z_H2S 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FCVTX_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      let s_esize : Nat := 64
      let d_esize : Nat := 32
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTX_Z_P_Z_D2S 128 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTX_Z_P_Z_D2S 256 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTX_Z_P_Z_D2S 512 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTX_Z_P_Z_D2S 1024 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTX_Z_P_Z_D2S 2048 (Sail.Int.toNatChecked (d)) d_esize esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n)) s_esize))
      | _ => (pure (())))


def decode_FCVTXNT_Z_P_Z_D2S (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let esize : Nat := 64
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Zn)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTXNT_Z_P_Z_D2S 128 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTXNT_Z_P_Z_D2S 256 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTXNT_Z_P_Z_D2S 512 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTXNT_Z_P_Z_D2S 1024 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCVTXNT_Z_P_Z_D2S 2048 (Sail.Int.toNatChecked (d)) esize
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_FCLAMP_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCLAMP_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCLAMP_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCLAMP_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCLAMP_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FCLAMP_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFADD_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFMUL_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFSUB_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFADD_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFADD_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_BFMUL_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMUL_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_BFSUB_Z_P_ZZ__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVEB16B16 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFSUB_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


end ArmFull.Functions
