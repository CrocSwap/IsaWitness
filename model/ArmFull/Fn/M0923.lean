import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0018
import ArmFull.Fn.M0087
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0204
import ArmFull.Fn.M0215
import ArmFull.Fn.M0238
import ArmFull.Fn.M0840
import ArmFull.Fn.M0851
import ArmFull.Fn.M0852

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical :
  Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3] ∧
  List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_W (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Sail.BitVec.castWidth (Zeros (n := VL))))
  (Z_set d VL (Sail.BitVec.castWidth operand))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical :
  Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1] ∧
  List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_D (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Sail.BitVec.castWidth (Zeros (n := VL))))
  (Z_set d VL (Sail.BitVec.castWidth operand))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, offset : Nat, s : Nat, k_vertical :
  Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧ 0 ≤ n ∧ n ≤ 15 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_Z_RZA_Q (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat index) +i offset))) dim)
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical slice_name VL))
    ) : SailM (BitVec VL) )
  (ZAslice_set n esize vertical slice_name VL (Sail.BitVec.castWidth (Zeros (n := VL))))
  (Z_set d VL (Sail.BitVec.castWidth operand))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 15 ∧ nreg = 2 ∧ n = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ2_ZA_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ2_ZA_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3] ∧
  nreg = 2 ∧ List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ2_ZA_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧
  nreg = 2 ∧
  List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ2_ZA_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  0 ≤ offset ∧
  offset ≤ 15 ∧ nreg = 4 ∧ n = 0 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_B1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧
  nreg = 4 ∧ List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧
  nreg = 4 ∧
  List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  if ((((nreg == 4) && (esize == 64)) && (VL == 128)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ_ZA2_1 (VL : Nat) (d : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let result ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth (Zeros (n := VL))))
          (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ_ZA4_1 (VL : Nat) (d : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let result ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth (Zeros (n := VL))))
          (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: N : Nat, k_fpexc : Bool, List.elem N [16, 32, 64] -/
def FPRound__2 (op : real) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (fpexc : Bool) (N : Nat) : SailM (BitVec N) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let isbfloat16 : Bool := false
  ((Sail.BitVec.castWidth ) <$> (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPUnpackBase (fpval : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType (← occLabel 909) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 910) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 911) ()) ) : SailM real )
  let isbfloat16 : Bool := false
  let w__0 ← (( do (FPUnpackBase__1 fpval fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fp_type : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  (pure ((fp_type, sign, value_name)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPProcessNaN (fptype : FPType) (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPProcessNaN__1 fptype op fpcr fpexc)


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPProcessNaNs__1 (type1 : FPType) (type2 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-arm/v8_base.sail:16206.41-16206.42"
  let done ← (( do (undefined_bool_at (← occLabel 919) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 920)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let any_snan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN))
  let type_nan : FPType :=
    if (any_snan : Bool)
    then FPType_SNaN
    else FPType_QNaN
  if (((altfp && op1_nan) && op2_nan) : Bool)
  then
    (do
      let done : Bool := true
      let w__3 ← (( do (FPProcessNaN__1 type_nan op1 fpcr fpexc) ) : SailM (BitVec k_N) )
      let result := (w__3 : (BitVec k_N))
      (pure ((done, result))))
  else
    (do
      if ((BEq.beq type1 FPType_SNaN) : Bool)
      then
        (do
          let done : Bool := true
          let w__4 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec k_N) )
          let result := (w__4 : (BitVec k_N))
          (pure ((done, result))))
      else
        (do
          if ((BEq.beq type2 FPType_SNaN) : Bool)
          then
            (do
              let done : Bool := true
              let w__5 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM (BitVec k_N) )
              let result := (w__5 : (BitVec k_N))
              (pure ((done, result))))
          else
            (do
              if ((BEq.beq type1 FPType_QNaN) : Bool)
              then
                (do
                  let done : Bool := true
                  let w__6 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec k_N) )
                  let result := (w__6 : (BitVec k_N))
                  (pure ((done, result))))
              else
                (do
                  if ((BEq.beq type2 FPType_QNaN) : Bool)
                  then
                    (do
                      let done : Bool := true
                      let w__7 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM
                        (BitVec k_N) )
                      let result := (w__7 : (BitVec k_N))
                      (pure ((done, result))))
                  else
                    (let done : Bool := false
                    let result : (BitVec k_N) :=
                      (Sail.BitVec.castWidth (Zeros (n := (Sail.BitVec.length result))))
                    (pure ((done, result))))))))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPRoundCV (op : real) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (N : Nat) : SailM (BitVec N) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 19 19 0#1)
  let fpexc : Bool := true
  let isbfloat16 : Bool := false
  ((Sail.BitVec.castWidth ) <$> (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPProcessNaNs3__1 (type1 : FPType) (type2 : FPType) (type3 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (op3 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  ArmFull.assert (((Sail.BitVec.length op3) == 16) || (((Sail.BitVec.length op3) == 32) || ((Sail.BitVec.length
          op3) == 64))) "sail-arm/v8_base.sail:16864.41-16864.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1025)
      (Sail.BitVec.length op3))) ) : SailM (BitVec k_N) )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let op3_nan : Bool := ((BEq.beq type3 FPType_SNaN) || (BEq.beq type3 FPType_QNaN))
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let type_nan ← (( do (undefined_FPType (← occLabel 1026) ()) ) : SailM FPType )
  let type_nan : FPType :=
    if (altfp : Bool)
    then
      (if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) || (BEq.beq type3
             FPType_SNaN)) : Bool)
      then FPType_SNaN
      else FPType_QNaN)
    else type_nan
  let done ← (( do (undefined_bool_at (← occLabel 1027) ()) ) : SailM Bool )
  if ((((altfp && op1_nan) && op2_nan) && op3_nan) : Bool)
  then
    (do
      let done : Bool := true
      let w__3 ← (( do (FPProcessNaN__1 type_nan op2 fpcr fpexc) ) : SailM (BitVec k_N) )
      let result := (w__3 : (BitVec k_N))
      (pure ((done, result))))
  else
    (do
      if (((altfp && op2_nan) && (op1_nan || op3_nan)) : Bool)
      then
        (do
          let done : Bool := true
          let w__4 ← (( do (FPProcessNaN__1 type_nan op2 fpcr fpexc) ) : SailM (BitVec k_N) )
          let result := (w__4 : (BitVec k_N))
          (pure ((done, result))))
      else
        (do
          if (((altfp && op3_nan) && op1_nan) : Bool)
          then
            (do
              let done : Bool := true
              let w__5 ← (( do (FPProcessNaN__1 type_nan op3 fpcr fpexc) ) : SailM (BitVec k_N) )
              let result := (w__5 : (BitVec k_N))
              (pure ((done, result))))
          else
            (do
              if ((BEq.beq type1 FPType_SNaN) : Bool)
              then
                (do
                  let done : Bool := true
                  let w__6 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec k_N) )
                  let result := (w__6 : (BitVec k_N))
                  (pure ((done, result))))
              else
                (do
                  if ((BEq.beq type2 FPType_SNaN) : Bool)
                  then
                    (do
                      let done : Bool := true
                      let w__7 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM
                        (BitVec k_N) )
                      let result := (w__7 : (BitVec k_N))
                      (pure ((done, result))))
                  else
                    (do
                      if ((BEq.beq type3 FPType_SNaN) : Bool)
                      then
                        (do
                          let done : Bool := true
                          let w__8 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) : SailM
                            (BitVec k_N) )
                          let result := (w__8 : (BitVec k_N))
                          (pure ((done, result))))
                      else
                        (do
                          if ((BEq.beq type1 FPType_QNaN) : Bool)
                          then
                            (do
                              let done : Bool := true
                              let w__9 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM
                                (BitVec k_N) )
                              let result := (w__9 : (BitVec k_N))
                              (pure ((done, result))))
                          else
                            (do
                              if ((BEq.beq type2 FPType_QNaN) : Bool)
                              then
                                (do
                                  let done : Bool := true
                                  let w__10 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) :
                                    SailM (BitVec k_N) )
                                  let result := (w__10 : (BitVec k_N))
                                  (pure ((done, result))))
                              else
                                (do
                                  if ((BEq.beq type3 FPType_QNaN) : Bool)
                                  then
                                    (do
                                      let done : Bool := true
                                      let w__11 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) :
                                        SailM (BitVec k_N) )
                                      let result := (w__11 : (BitVec k_N))
                                      (pure ((done, result))))
                                  else
                                    (let done : Bool := false
                                    let result : (BitVec k_N) :=
                                      (Sail.BitVec.castWidth (Zeros
                                        (n := (Sail.BitVec.length result))))
                                    (pure ((done, result))))))))))))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [32, 64] -/
def FPProcessNaNs3H (type1 : FPType) (type2 : FPType) (type3 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec (k_N / 2))) (op3 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  ArmFull.assert (((Sail.BitVec.length op1) == 32) || ((Sail.BitVec.length op1) == 64)) "sail-arm/v8_base.sail:17069.30-17069.31"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1059)
      (Sail.BitVec.length op1))) ) : SailM (BitVec k_N) )
  let type_nan ← (( do (undefined_FPType (← occLabel 1060) ()) ) : SailM FPType )
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let op3_nan : Bool := ((BEq.beq type3 FPType_SNaN) || (BEq.beq type3 FPType_QNaN))
  let type_nan : FPType :=
    if (altfp : Bool)
    then
      (if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) || (BEq.beq type3
             FPType_SNaN)) : Bool)
      then FPType_SNaN
      else FPType_QNaN)
    else type_nan
  let done ← (( do (undefined_bool_at (← occLabel 1061) ()) ) : SailM Bool )
  if ((((altfp && op1_nan) && op2_nan) && op3_nan) : Bool)
  then
    (do
      let done : Bool := true
      let w__3 ← (( do (FPProcessNaN__1 type_nan op2 fpcr fpexc) ) : SailM (BitVec (k_N / 2)) )
      let w__4 ← (( do
        ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__3 (Sail.BitVec.length result))) ) : SailM
        (BitVec k_N) )
      let result := (w__4 : (BitVec k_N))
      (pure ((done, result))))
  else
    (do
      if (((altfp && op2_nan) && (op1_nan || op3_nan)) : Bool)
      then
        (do
          let done : Bool := true
          let w__5 ← (( do (FPProcessNaN__1 type_nan op2 fpcr fpexc) ) : SailM (BitVec (k_N / 2))
            )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__5 (Sail.BitVec.length result))) ) : SailM
            (BitVec k_N) )
          let result := (w__6 : (BitVec k_N))
          (pure ((done, result))))
      else
        (do
          if (((altfp && op3_nan) && op1_nan) : Bool)
          then
            (do
              let done : Bool := true
              let w__7 ← (( do (FPProcessNaN__1 type_nan op3 fpcr fpexc) ) : SailM
                (BitVec (k_N / 2)) )
              let w__8 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__7 (Sail.BitVec.length result))) ) :
                SailM (BitVec k_N) )
              let result := (w__8 : (BitVec k_N))
              (pure ((done, result))))
          else
            (do
              if ((BEq.beq type1 FPType_SNaN) : Bool)
              then
                (do
                  let done : Bool := true
                  let w__9 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec k_N) )
                  let result := (w__9 : (BitVec k_N))
                  (pure ((done, result))))
              else
                (do
                  if ((BEq.beq type2 FPType_SNaN) : Bool)
                  then
                    (do
                      let done : Bool := true
                      let w__10 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM
                        (BitVec (k_N / 2)) )
                      let w__11 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__10
                          (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                      let result := (w__11 : (BitVec k_N))
                      (pure ((done, result))))
                  else
                    (do
                      if ((BEq.beq type3 FPType_SNaN) : Bool)
                      then
                        (do
                          let done : Bool := true
                          let w__12 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) : SailM
                            (BitVec (k_N / 2)) )
                          let w__13 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__12
                              (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                          let result := (w__13 : (BitVec k_N))
                          (pure ((done, result))))
                      else
                        (do
                          if ((BEq.beq type1 FPType_QNaN) : Bool)
                          then
                            (do
                              let done : Bool := true
                              let w__14 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM
                                (BitVec k_N) )
                              let result := (w__14 : (BitVec k_N))
                              (pure ((done, result))))
                          else
                            (do
                              if ((BEq.beq type2 FPType_QNaN) : Bool)
                              then
                                (do
                                  let done : Bool := true
                                  let w__15 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) :
                                    SailM (BitVec (k_N / 2)) )
                                  let w__16 ← (( do
                                    ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__15
                                      (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                                  let result := (w__16 : (BitVec k_N))
                                  (pure ((done, result))))
                              else
                                (do
                                  if ((BEq.beq type3 FPType_QNaN) : Bool)
                                  then
                                    (do
                                      let done : Bool := true
                                      let w__17 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) :
                                        SailM (BitVec (k_N / 2)) )
                                      let w__18 ← (( do
                                        ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__17
                                          (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                                      let result := (w__18 : (BitVec k_N))
                                      (pure ((done, result))))
                                  else
                                    (let done : Bool := false
                                    let result : (BitVec k_N) :=
                                      (Sail.BitVec.castWidth (Zeros
                                        (n := (Sail.BitVec.length result))))
                                    (pure ((done, result))))))))))))


end ArmFull.Functions
