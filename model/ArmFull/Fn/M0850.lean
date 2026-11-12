import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0147
import ArmFull.Fn.M0151
import ArmFull.Fn.M0179
import ArmFull.Fn.M0195
import ArmFull.Fn.M0215
import ArmFull.Fn.M0218
import ArmFull.Fn.M0230
import ArmFull.Fn.M0231
import ArmFull.Fn.M0232
import ArmFull.Fn.M0240
import ArmFull.Fn.M0258
import ArmFull.Fn.M0582
import ArmFull.Fn.M0838
import ArmFull.Fn.M0839
import ArmFull.Fn.M0840

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

/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 4 ∧
  List.elem imm [0, 1] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 1 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ4_ZTZ_1 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (fmod_int imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7563)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-arm/instrs64_sme.sail:36318.46-36318.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


def decode_ZERO_ZT_I__ (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_ZERO_ZT_I__ ())


def decode_MOVT_R_ZT__ (off3 : (BitVec 3)) (Rt : (BitVec 5)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (Halted ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let offset : Int := (BitVec.toNat off3)
  (execute_MOVT_R_ZT__ (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t)))


def decode_MOVT_ZT_R__ (off3 : (BitVec 3)) (Rt : (BitVec 5)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (Halted ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Rt)
  let offset : Int := (BitVec.toNat off3)
  (execute_MOVT_ZT_R__ (Sail.Int.toNatChecked (offset)) (Sail.Int.toNatChecked (t)))


def decode_RDSVL_R_I__ (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toInt imm6)
  match SVL with
  | 128 =>
    (do
      (execute_RDSVL_R_I__ 128 (Sail.Int.toNatChecked (d)) imm))
  | 256 =>
    (do
      (execute_RDSVL_R_I__ 256 (Sail.Int.toNatChecked (d)) imm))
  | 512 =>
    (do
      (execute_RDSVL_R_I__ 512 (Sail.Int.toNatChecked (d)) imm))
  | 1024 =>
    (do
      (execute_RDSVL_R_I__ 1024 (Sail.Int.toNatChecked (d)) imm))
  | 2048 =>
    (do
      (execute_RDSVL_R_I__ 2048 (Sail.Int.toNatChecked (d)) imm))
  | _ => (pure (()))


def decode_ADDSPL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toInt imm6)
  match SVL with
  | 128 =>
    (do
      (execute_ADDSPL_R_RI__ 128 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADDSPL_R_RI__ 256 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADDSPL_R_RI__ 512 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADDSPL_R_RI__ 1024 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADDSPL_R_RI__ 2048 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


def decode_ADDSVL_R_RI__ (Rn : (BitVec 5)) (imm6 : (BitVec 6)) (Rd : (BitVec 5)) : SailM Unit := do
  let SVL ← (( do (CurrentSVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let n : Int := (BitVec.toNat Rn)
  let d : Int := (BitVec.toNat Rd)
  let imm : Int := (BitVec.toInt imm6)
  match SVL with
  | 128 =>
    (do
      (execute_ADDSVL_R_RI__ 128 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 256 =>
    (do
      (execute_ADDSVL_R_RI__ 256 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 512 =>
    (do
      (execute_ADDSVL_R_RI__ 512 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 1024 =>
    (do
      (execute_ADDSVL_R_RI__ 1024 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | 2048 =>
    (do
      (execute_ADDSVL_R_RI__ 2048 (Sail.Int.toNatChecked (d)) imm (Sail.Int.toNatChecked (n))))
  | _ => (pure (()))


/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 2 ∧
  List.elem imm [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 8 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_MZ2_ZTZ_8 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (Nat.mod imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7567)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-arm/instrs64_sme.sail:37205.46-37205.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 4 ∧
  List.elem imm [0, 1, 2, 3] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 8 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ2_ZTZ_8 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (Nat.mod imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7568)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-arm/instrs64_sme.sail:37279.46-37279.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 2 ∧
  List.elem imm [0, 1, 2, 3] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 4 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI2_MZ4_ZTZ_4 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (Nat.mod imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7569)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-arm/instrs64_sme.sail:37353.46-37353.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, d__arg : Nat, dstride : Nat, esize : Nat, imm : Nat, isize : Nat, n
  : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  isize = 4 ∧
  List.elem imm [0, 1] ∧
  List.elem esize [8, 16, 32, 64] ∧ dstride = 4 ∧ 0 ≤ d__arg ∧ d__arg ≤ 31 ∧ (is_VL VL) -/
def execute_LUTI4_MZ4_ZTZ_4 (VL : Nat) (d__arg : Nat) (dstride : Nat) (esize : Nat) (imm : Nat) (isize : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  let d : Int := d__arg
  (CheckStreamingSVEEnabled ())
  (CheckSMEZT0Enabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let segments : Nat :=
    (Sail.Int.toNatChecked ((Int.ediv esize (Sail.Int.toNatChecked ((isize *i nreg))))))
  let segment : Int := (fmod_int imm segments)
  let indexes ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let table ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let d ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := d
      for r in [loop_r_lower:loop_r_upper:1]i do
        let d := loop_vars
        loop_vars ← do
          let base : Int := (((segment *i nreg) +i r) *i elements)
          let result ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7570)
              (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let w__0 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (Elem_read indexes (base +i e) isize)) ) : SailM
                    (BitVec isize) )
                  let index : Int := (BitVec.toNat w__0)
                  ArmFull.assert ((esize -i 1) <b 32) "sail-arm/instrs64_sme.sail:37427.46-37427.47"
                  let w__1 ← (( do (Elem_read table index 32) ) : SailM (BitVec 32) )
                  (Elem_set result e esize
                    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                      (Sail.Int.toNatChecked ((esize -i 1))) 0)))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          (Z_set d VL (Sail.BitVec.castWidth result))
          let d : Int := (d +i dstride)
          (pure (d))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: pc : Int -/
def __DecodeT32__seg2 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__162 ← (( do
    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb __opcode 31 20)) == (0xFB0#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 7 4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
    then
      (do
        let w__161 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__161 <b 3029) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__162 : Bool)
  then
    (do
      writeReg SEE 3029
      let Rn := (BitVec.slice __opcode 16 4)
      let Rd := (BitVec.slice __opcode 8 4)
      let Rm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_MUL_T2enc_A_txt Rn Rd Rm)
      (pure false))
  else
    (do
      let w__164 ← (( do
        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                   __opcode 25 21)) == (0b00011#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                   __opcode 19 15)) == (0b11110#5 : (BitVec 5))))) : Bool) : Bool)
        then
          (do
            let w__163 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__163 <b 3031) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__164 : Bool)
      then
        (do
          writeReg SEE 3031
          let i := (BitVec.slice __opcode 26 1)
          let S := (BitVec.slice __opcode 20 1)
          let imm3 := (BitVec.slice __opcode 12 3)
          let Rd := (BitVec.slice __opcode 8 4)
          let imm8 := (BitVec.slice __opcode 0 8)
          (decode_aarch32_instrs_MVN_i_T1enc_A_txt i S imm3 Rd imm8)
          (pure false))
      else
        (do
          let w__166 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11101010011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                     __opcode 19 15)) == (0b11110#5 : (BitVec 5)))) : Bool) : Bool)
            then
              (do
                let w__165 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__165 <b 3034) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__166 : Bool)
          then
            (do
              writeReg SEE 3034
              let S := (BitVec.slice __opcode 20 1)
              let imm3 := (BitVec.slice __opcode 12 3)
              let Rd := (BitVec.slice __opcode 8 4)
              let imm2 := (BitVec.slice __opcode 6 2)
              let stype := (BitVec.slice __opcode 4 2)
              let Rm := (BitVec.slice __opcode 0 4)
              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 15)])) != 0#1) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_aarch32_instrs_MVN_r_T2enc_A_txt S imm3 Rd imm2 stype Rm))
              (pure false))
          else
            (do
              let w__168 ← (( do
                if (((__opcode == 0b11110011101011111000000000000000#32) : Bool) : Bool)
                then
                  (do
                    let w__167 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__167 <b 3038) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__168 : Bool)
              then
                (do
                  writeReg SEE 3038
                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 11)])) != 0#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_NOP_T2enc_A_txt ()))
                  (pure false))
              else
                (do
                  let w__170 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode 31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                               __opcode 25 21)) == (0b00011#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                    then
                      (do
                        let w__169 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__169 <b 3039) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__170 : Bool)
                  then
                    (do
                      writeReg SEE 3039
                      let i := (BitVec.slice __opcode 26 1)
                      let S := (BitVec.slice __opcode 20 1)
                      let Rn := (BitVec.slice __opcode 16 4)
                      let imm3 := (BitVec.slice __opcode 12 3)
                      let Rd := (BitVec.slice __opcode 8 4)
                      let imm8 := (BitVec.slice __opcode 0 8)
                      (decode_aarch32_instrs_ORN_i_T1enc_A_txt i S Rn imm3 Rd imm8)
                      (pure false))
                  else
                    (do
                      let w__172 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b11101010011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                 __opcode 15 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                        then
                          (do
                            let w__171 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__171 <b 3040) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__172 : Bool)
                      then
                        (do
                          writeReg SEE 3040
                          let S := (BitVec.slice __opcode 20 1)
                          let Rn := (BitVec.slice __opcode 16 4)
                          let imm3 := (BitVec.slice __opcode 12 3)
                          let Rd := (BitVec.slice __opcode 8 4)
                          let imm2 := (BitVec.slice __opcode 6 2)
                          let stype := (BitVec.slice __opcode 4 2)
                          let Rm := (BitVec.slice __opcode 0 4)
                          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 15)])) != 0#1) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_ORN_r_T1enc_A_txt S Rn imm3 Rd imm2 stype Rm))
                          (pure false))
                      else
                        (do
                          let w__174 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb __opcode
                                     31 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                       __opcode 25 21)) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                       __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                            then
                              (do
                                let w__173 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__173 <b 3042) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__174 : Bool)
                          then
                            (do
                              writeReg SEE 3042
                              let i := (BitVec.slice __opcode 26 1)
                              let S := (BitVec.slice __opcode 20 1)
                              let Rn := (BitVec.slice __opcode 16 4)
                              let imm3 := (BitVec.slice __opcode 12 3)
                              let Rd := (BitVec.slice __opcode 8 4)
                              let imm8 := (BitVec.slice __opcode 0 8)
                              (decode_aarch32_instrs_ORR_i_T1enc_A_txt i S Rn imm3 Rd imm8)
                              (pure false))
                          else
                            (do
                              let w__176 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11101010010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                         __opcode 15 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__175 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__175 <b 3045) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__176 : Bool)
                              then
                                (do
                                  writeReg SEE 3045
                                  let S := (BitVec.slice __opcode 20 1)
                                  let Rn := (BitVec.slice __opcode 16 4)
                                  let imm3 := (BitVec.slice __opcode 12 3)
                                  let Rd := (BitVec.slice __opcode 8 4)
                                  let imm2 := (BitVec.slice __opcode 6 2)
                                  let stype := (BitVec.slice __opcode 4 2)
                                  let Rm := (BitVec.slice __opcode 0 4)
                                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 15)])) != 0#1) : Bool)
                                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                                  else
                                    (do
                                      (decode_aarch32_instrs_ORR_r_T2enc_A_txt S Rn imm3 Rd imm2
                                        stype Rm))
                                  (pure false))
                              else
                                (do
                                  let w__178 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b11101010110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             __opcode 15 15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__177 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__177 <b 3048) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__178 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3048
                                      let S := (BitVec.slice __opcode 20 1)
                                      let Rn := (BitVec.slice __opcode 16 4)
                                      let imm3 := (BitVec.slice __opcode 12 3)
                                      let Rd := (BitVec.slice __opcode 8 4)
                                      let imm2 := (BitVec.slice __opcode 6 2)
                                      let tb := (BitVec.slice __opcode 5 1)
                                      let T := (BitVec.slice __opcode 4 1)
                                      let Rm := (BitVec.slice __opcode 0 4)
                                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode
                                               15)])) != 0#1) : Bool)
                                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                                      else
                                        (do
                                          (decode_aarch32_instrs_PKH_T1enc_A_txt S Rn imm3 Rd imm2
                                            tb T Rm))
                                      (pure false))
                                  else
                                    (do
                                      let w__180 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                 __opcode 31 22)) == (0b1111100010#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   __opcode 15 12)) == (0xF#4 : (BitVec 4))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__179 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__179 <b 3050) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__180 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3050
                                          let W := (BitVec.slice __opcode 21 1)
                                          let Rn := (BitVec.slice __opcode 16 4)
                                          let imm12 := (BitVec.slice __opcode 0 12)
                                          (decode_aarch32_instrs_PLD_i_T1enc_A_txt W Rn imm12)
                                          (pure false))
                                      else
                                        (do
                                          let w__182 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                     __opcode 31 22)) == (0b1111100000#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                       __opcode 15 8)) == (0xFC#8 : (BitVec 8))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__181 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__181 <b 3051) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__182 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3051
                                              let W := (BitVec.slice __opcode 21 1)
                                              let Rn := (BitVec.slice __opcode 16 4)
                                              let imm8 := (BitVec.slice __opcode 0 8)
                                              (decode_aarch32_instrs_PLD_i_T2enc_A_txt W Rn imm8)
                                              (pure false))
                                          else
                                            (do
                                              let w__184 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0xF8#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 22 12)) == (0b00111111111#11 : (BitVec 11)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__183 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__183 <b 3053) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__184 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3053
                                                  let U := (BitVec.slice __opcode 23 1)
                                                  let imm12 := (BitVec.slice __opcode 0 12)
                                                  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                           __opcode 21)])) != 0#1) : Bool)
                                                  then
                                                    sailThrow ((Error_ConstrainedUnpredictable ()))
                                                  else
                                                    (do
                                                      (decode_aarch32_instrs_PLD_l_T1enc_A_txt U
                                                        imm12))
                                                  (pure false))
                                              else
                                                (do
                                                  let w__186 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                             __opcode 31 22)) == (0b1111100000#10 : (BitVec 10))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 20 20)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                               __opcode 15 6)) == (0b1111000000#10 : (BitVec 10))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__185 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__185 <b 3055) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__186 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3055
                                                      let W := (BitVec.slice __opcode 21 1)
                                                      let Rn := (BitVec.slice __opcode 16 4)
                                                      let imm2 := (BitVec.slice __opcode 4 2)
                                                      let Rm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_PLD_r_T1enc_A_txt W Rn
                                                        imm2 Rm)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__188 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                 __opcode 31 20)) == (0xF99#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                 __opcode 15 12)) == (0xF#4 : (BitVec 4)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__187 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__187 <b 3057) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__188 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3057
                                                          let Rn := (BitVec.slice __opcode 16 4)
                                                          let imm12 := (BitVec.slice __opcode 0 12)
                                                          (decode_aarch32_instrs_PLI_i_T1enc_A_txt
                                                            Rn imm12)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__190 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                     __opcode 31 20)) == (0xF91#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 15 8)) == (0xFC#8 : (BitVec 8)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__189 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__189 <b 3058) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__190 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3058
                                                              let Rn := (BitVec.slice __opcode 16 4)
                                                              let imm8 :=
                                                                (BitVec.slice __opcode 0 8)
                                                              (decode_aarch32_instrs_PLI_i_T2enc_A_txt
                                                                Rn imm8)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__192 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0xF9#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 22 12)) == (0b00111111111#11 : (BitVec 11)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__191 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__191 <b 3059) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__192 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3059
                                                                  let U :=
                                                                    (BitVec.slice __opcode 23 1)
                                                                  let imm12 :=
                                                                    (BitVec.slice __opcode 0 12)
                                                                  (decode_aarch32_instrs_PLI_i_T3enc_A_txt
                                                                    U imm12)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__194 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                             __opcode 31 20)) == (0xF91#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                             __opcode 15 6)) == (0b1111000000#10 : (BitVec 10)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__193 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__193 <b 3061) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__194 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3061
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let imm2 :=
                                                                        (BitVec.slice __opcode 4 2)
                                                                      let Rm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_PLI_r_T1enc_A_txt
                                                                        Rn imm2 Rm)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__196 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                   __opcode 7 4)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__195 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__195 <b 3065) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__196 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3065
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 8
                                                                              4)
                                                                          let Rm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_QADD16_T1enc_A_txt
                                                                            Rn Rd Rm)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__198 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                       __opcode 15
                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                       __opcode 7 4)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__197 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__197 <b 3067) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__198 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3067
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 8 4)
                                                                              let Rm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_QADD8_T1enc_A_txt
                                                                                Rn Rd Rm)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__200 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           7 4)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__199 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__199 <b 3069) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__200 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3069
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 8 4)
                                                                                  let Rm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_QADD_T1enc_A_txt
                                                                                    Rn Rd Rm)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__202 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 20)) == (0xFAA#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               7 4)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__201 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__201 <b 3071) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__202 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3071
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 4)
                                                                                      let Rd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 8
                                                                                          4)
                                                                                      let Rm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_QASX_T1enc_A_txt
                                                                                        Rn Rd Rm)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__204 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   7
                                                                                                   4)) == (0x9#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__203 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__203 <b 3073) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__204 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3073
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              8 4)
                                                                                          let Rm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_QDADD_T1enc_A_txt
                                                                                            Rn Rd Rm)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__206 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       7
                                                                                                       4)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__205 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__205 <b 3075) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__206 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3075
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  8
                                                                                                  4)
                                                                                              let Rm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_QDSUB_T1enc_A_txt
                                                                                                Rn
                                                                                                Rd
                                                                                                Rm)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__208 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         20)) == (0xFAE#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           15
                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           7
                                                                                                           4)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__207 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__207 <b 3077) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__208 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3077
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Rd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      8
                                                                                                      4)
                                                                                                  let Rm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_QSAX_T1enc_A_txt
                                                                                                    Rn
                                                                                                    Rd
                                                                                                    Rm)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__210 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             20)) == (0xFAD#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               7
                                                                                                               4)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__209 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__209 <b 3079) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__210 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3079
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Rd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          8
                                                                                                          4)
                                                                                                      let Rm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_QSUB16_T1enc_A_txt
                                                                                                        Rn
                                                                                                        Rd
                                                                                                        Rm)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__212 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 20)) == (0xFAC#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   15
                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   7
                                                                                                                   4)) == (0x1#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__211 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__211 <b 3081) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__212 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3081
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Rd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              8
                                                                                                              4)
                                                                                                          let Rm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_QSUB8_T1enc_A_txt
                                                                                                            Rn
                                                                                                            Rd
                                                                                                            Rm)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__214 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       15
                                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       7
                                                                                                                       4)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__213 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__213 <b 3083) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__214 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3083
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  4)
                                                                                                              let Rd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  8
                                                                                                                  4)
                                                                                                              let Rm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_aarch32_instrs_QSUB_T1enc_A_txt
                                                                                                                Rn
                                                                                                                Rd
                                                                                                                Rm)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__216 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           15
                                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           7
                                                                                                                           4)) == (0xA#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__215 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__215 <b 3085) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__216 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 3085
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let Rd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      8
                                                                                                                      4)
                                                                                                                  let Rm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  (decode_aarch32_instrs_RBIT_T1enc_A_txt
                                                                                                                    Rn
                                                                                                                    Rd
                                                                                                                    Rm)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__218 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               15
                                                                                                                               12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               7
                                                                                                                               4)) == (0x9#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__217 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__217 <b 3088) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__218 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 3088
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let Rd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          8
                                                                                                                          4)
                                                                                                                      let Rm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          4)
                                                                                                                      (decode_aarch32_instrs_REV16_T2enc_A_txt
                                                                                                                        Rn
                                                                                                                        Rd
                                                                                                                        Rm)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__220 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   7
                                                                                                                                   4)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__219 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__219 <b 3091) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__220 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 3091
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let Rd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              8
                                                                                                                              4)
                                                                                                                          let Rm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_aarch32_instrs_REV_T2enc_A_txt
                                                                                                                            Rn
                                                                                                                            Rd
                                                                                                                            Rm)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__222 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       7
                                                                                                                                       4)) == (0xB#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__221 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__221 <b 3094) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__222 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 3094
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let Rd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  8
                                                                                                                                  4)
                                                                                                                              let Rm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_aarch32_instrs_REVSH_T2enc_A_txt
                                                                                                                                Rn
                                                                                                                                Rd
                                                                                                                                Rm)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__224 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           25
                                                                                                                                           21)) == (0b01110#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__223 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__223 <b 3098) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__224 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 3098
                                                                                                                                  let i :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      26
                                                                                                                                      1)
                                                                                                                                  let S :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      20
                                                                                                                                      1)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let imm3 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      12
                                                                                                                                      3)
                                                                                                                                  let Rd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      8
                                                                                                                                      4)
                                                                                                                                  let imm8 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      8)
                                                                                                                                  (decode_aarch32_instrs_RSB_i_T2enc_A_txt
                                                                                                                                    i
                                                                                                                                    S
                                                                                                                                    Rn
                                                                                                                                    imm3
                                                                                                                                    Rd
                                                                                                                                    imm8)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__226 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b11101011110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__225 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__225 <b 3100) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__226 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 3100
                                                                                                                                      let S :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          20
                                                                                                                                          1)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let imm3 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          12
                                                                                                                                          3)
                                                                                                                                      let Rd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          8
                                                                                                                                          4)
                                                                                                                                      let imm2 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          6
                                                                                                                                          2)
                                                                                                                                      let stype :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          4
                                                                                                                                          2)
                                                                                                                                      let Rm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                               __opcode
                                                                                                                                               15)])) != 0#1) : Bool)
                                                                                                                                      then
                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                          ()))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          (decode_aarch32_instrs_RSB_r_T1enc_A_txt
                                                                                                                                            S
                                                                                                                                            Rn
                                                                                                                                            imm3
                                                                                                                                            Rd
                                                                                                                                            imm2
                                                                                                                                            stype
                                                                                                                                            Rm))
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__228 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   15
                                                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   7
                                                                                                                                                   4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__227 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__227 <b 3106) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__228 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 3106
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              4)
                                                                                                                                          let Rd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              8
                                                                                                                                              4)
                                                                                                                                          let Rm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              4)
                                                                                                                                          (decode_aarch32_instrs_SADD16_T1enc_A_txt
                                                                                                                                            Rn
                                                                                                                                            Rd
                                                                                                                                            Rm)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__230 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     20)) == (0xFA8#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       7
                                                                                                                                                       4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__229 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__229 <b 3108) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__230 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 3108
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  4)
                                                                                                                                              let Rd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  8
                                                                                                                                                  4)
                                                                                                                                              let Rm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  4)
                                                                                                                                              (decode_aarch32_instrs_SADD8_T1enc_A_txt
                                                                                                                                                Rn
                                                                                                                                                Rd
                                                                                                                                                Rm)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__232 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         20)) == (0xFAA#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           7
                                                                                                                                                           4)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__231 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__231 <b 3110) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__232 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 3110
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      4)
                                                                                                                                                  let Rd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      8
                                                                                                                                                      4)
                                                                                                                                                  let Rm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      4)
                                                                                                                                                  (decode_aarch32_instrs_SASX_T1enc_A_txt
                                                                                                                                                    Rn
                                                                                                                                                    Rd
                                                                                                                                                    Rm)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__234 ← (( do
                                                                                                                                                    if (((__opcode == 0b11110011101111111000111101110000#32) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__233 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__233 <b 3112) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__234 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 3112
                                                                                                                                                      if (((((((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                       __opcode
                                                                                                                                                                                       17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                               __opcode
                                                                                                                                                                               8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                             __opcode
                                                                                                                                                                             9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                           __opcode
                                                                                                                                                                           10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                         __opcode
                                                                                                                                                                         11)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                       __opcode
                                                                                                                                                                       0)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                     __opcode
                                                                                                                                                                     1)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                   __opcode
                                                                                                                                                                   2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                 __opcode
                                                                                                                                                                 3)])) != 0#1)) : Bool)
                                                                                                                                                      then
                                                                                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                          ()))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          (decode_aarch32_instrs_SB_T1enc_A_txt
                                                                                                                                                            ()))
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__236 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 27)) == (0b11110#5 : (BitVec 5))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   25
                                                                                                                                                                   21)) == (0b01011#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__235 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__235 <b 3114) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__236 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 3114
                                                                                                                                                          let i :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              26
                                                                                                                                                              1)
                                                                                                                                                          let S :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              20
                                                                                                                                                              1)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              4)
                                                                                                                                                          let imm3 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              12
                                                                                                                                                              3)
                                                                                                                                                          let Rd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              8
                                                                                                                                                              4)
                                                                                                                                                          let imm8 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              8)
                                                                                                                                                          (decode_aarch32_instrs_SBC_i_T1enc_A_txt
                                                                                                                                                            i
                                                                                                                                                            S
                                                                                                                                                            Rn
                                                                                                                                                            imm3
                                                                                                                                                            Rd
                                                                                                                                                            imm8)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__238 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     21)) == (0b11101011011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     15
                                                                                                                                                                     15)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__237 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__237 <b 3117) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__238 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 3117
                                                                                                                                                              let S :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  20
                                                                                                                                                                  1)
                                                                                                                                                              let Rn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  4)
                                                                                                                                                              let imm3 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  12
                                                                                                                                                                  3)
                                                                                                                                                              let Rd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  8
                                                                                                                                                                  4)
                                                                                                                                                              let imm2 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  6
                                                                                                                                                                  2)
                                                                                                                                                              let stype :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  4
                                                                                                                                                                  2)
                                                                                                                                                              let Rm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  4)
                                                                                                                                                              if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                       __opcode
                                                                                                                                                                       15)])) != 0#1) : Bool)
                                                                                                                                                              then
                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                  ()))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  (decode_aarch32_instrs_SBC_r_T2enc_A_txt
                                                                                                                                                                    S
                                                                                                                                                                    Rn
                                                                                                                                                                    imm3
                                                                                                                                                                    Rd
                                                                                                                                                                    imm2
                                                                                                                                                                    stype
                                                                                                                                                                    Rm))
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__240 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         20)) == (0xF34#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           15
                                                                                                                                                                           15)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           5
                                                                                                                                                                           5)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__239 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__239 <b 3120) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__240 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 3120
                                                                                                                                                                  let Rn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      4)
                                                                                                                                                                  let imm3 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      12
                                                                                                                                                                      3)
                                                                                                                                                                  let Rd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      8
                                                                                                                                                                      4)
                                                                                                                                                                  let imm2 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      6
                                                                                                                                                                      2)
                                                                                                                                                                  let widthm1 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                             __opcode
                                                                                                                                                                             26)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                             __opcode
                                                                                                                                                                             5)])) != 0#1)) : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                      ()))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      (decode_aarch32_instrs_SBFX_T1enc_A_txt
                                                                                                                                                                        Rn
                                                                                                                                                                        imm3
                                                                                                                                                                        Rd
                                                                                                                                                                        imm2
                                                                                                                                                                        widthm1))
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__242 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             20)) == (0xFB9#12 : (BitVec 12))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             7
                                                                                                                                                                             4)) == (0xF#4 : (BitVec 4)))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__241 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__241 <b 3122) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__242 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 3122
                                                                                                                                                                      let Rn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          4)
                                                                                                                                                                      let Ra :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          12
                                                                                                                                                                          4)
                                                                                                                                                                      let Rd :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          8
                                                                                                                                                                          4)
                                                                                                                                                                      let Rm :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          4)
                                                                                                                                                                      (decode_aarch32_instrs_SDIV_T1enc_A_txt
                                                                                                                                                                        Rn
                                                                                                                                                                        Ra
                                                                                                                                                                        Rd
                                                                                                                                                                        Rm)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__244 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 20)) == (0xFAA#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   15
                                                                                                                                                                                   12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   7
                                                                                                                                                                                   4)) == (0x8#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__243 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__243 <b 3124) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__244 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 3124
                                                                                                                                                                          let Rn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              4)
                                                                                                                                                                          let Rd :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              8
                                                                                                                                                                              4)
                                                                                                                                                                          let Rm :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              4)
                                                                                                                                                                          (decode_aarch32_instrs_SEL_T1enc_A_txt
                                                                                                                                                                            Rn
                                                                                                                                                                            Rd
                                                                                                                                                                            Rm)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__246 ← (( do
                                                                                                                                                                            if (((__opcode == 0b11110011101011111000000000000100#32) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__245 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__245 <b 3129) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__246 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 3129
                                                                                                                                                                              if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                               __opcode
                                                                                                                                                                                               18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         11)])) != 0#1)) : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                                                                                  ()))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  (decode_aarch32_instrs_SEV_T2enc_A_txt
                                                                                                                                                                                    ()))
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__248 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         20)) == (0xFA9#12 : (BitVec 12))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           15
                                                                                                                                                                                           12)) == (0xF#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                                           __opcode
                                                                                                                                                                                           7
                                                                                                                                                                                           4)) == (0x2#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__247 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__247 <b 3131) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__248 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 3131
                                                                                                                                                                                  let Rn :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      16
                                                                                                                                                                                      4)
                                                                                                                                                                                  let Rd :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      8
                                                                                                                                                                                      4)
                                                                                                                                                                                  let Rm :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      4)
                                                                                                                                                                                  (decode_aarch32_instrs_SHADD16_T1enc_A_txt
                                                                                                                                                                                    Rn
                                                                                                                                                                                    Rd
                                                                                                                                                                                    Rm)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
