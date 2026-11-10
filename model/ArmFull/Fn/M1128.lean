import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0118
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0203
import ArmFull.Fn.M0204
import ArmFull.Fn.M0218
import ArmFull.Fn.M0238
import ArmFull.Fn.M0244
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0582
import ArmFull.Fn.M0840
import ArmFull.Fn.M1041
import ArmFull.Fn.M1071

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

/-- Type quantifiers: SVL : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL SVL) -/
def execute_LDR_ZA_RI__ (SVL : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckSMEAndZAEnabled ())
  let SVL : Nat := SVL
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv SVL 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7023) 64) ) : SailM (BitVec 64) )
  let moffs : Int := (offset *i dim)
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7024)
      (Sail.Int.toNatChecked (SVL)))) ) : SailM (BitVec SVL) )
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset))) dim)
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
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base moffs) 16)
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
      (AArch64_Abort (BitVec.addInt base moffs) w__7))
  else (pure (()))
  let (moffs, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := (moffs, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (moffs, result) := loop_vars
        loop_vars ← do
          let moffs : Int := moffs
          let w__8 ← (( do (AArch64_MemSingle_read (BitVec.addInt base moffs) 1 accdesc aligned) )
            : SailM (BitVec (1 * 8)) )
          let w__9 ← (( do (Elem_set result e 8 w__8) ) : SailM (BitVec SVL) )
          let result := (w__9 : (BitVec SVL))
          let moffs : Int := (moffs +i 1)
          (pure ((moffs, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec SVL)) )
  (ZAvector_set vec SVL (Sail.BitVec.castWidth result))


/-- Type quantifiers: SVL : Nat, n : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧ 0 ≤ offset ∧ offset ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL SVL) -/
def execute_STR_ZA_RI__ (SVL : Nat) (n : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckSMEAndZAEnabled ())
  let SVL : Nat := SVL
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv SVL 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 7025) 64) ) : SailM (BitVec 64) )
  let moffs : Int := (offset *i dim)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int := (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset))) dim)
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
  let src ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec SVL)) ) : SailM (BitVec SVL) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base moffs) 16)
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
      (AArch64_Abort (BitVec.addInt base moffs) w__7))
  else (pure (()))
  let moffs ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := moffs
      for e in [loop_e_lower:loop_e_upper:1]i do
        let moffs := loop_vars
        loop_vars ← do
          let moffs : Int := moffs
          let w__8 ← (( do (Elem_read src e 8) ) : SailM (BitVec (1 * 8)) )
          (AArch64_MemSingle_set (BitVec.addInt base moffs) 1 accdesc aligned w__8)
          let moffs : Int := (moffs +i 1)
          (pure (moffs))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FADD_ZA_ZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7215)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize))
                    ) : SailM (BitVec esize) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__1 ← (( do (FPAdd_ZA element1 element2 w__0) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__1))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FSUB_ZA_ZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7216)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize))
                    ) : SailM (BitVec esize) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__1 ← (( do (FPSub_ZA element1 element2 w__0) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__1))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FADD_ZA_ZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7217)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize))
                    ) : SailM (BitVec esize) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__1 ← (( do (FPAdd_ZA element1 element2 w__0) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__1))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FSUB_ZA_ZW_4x4 (VL : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7218)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize))
                    ) : SailM (BitVec esize) )
                  let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__1 ← (( do (FPSub_ZA element1 element2 w__0) ) : SailM (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__1))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op :
  Bool, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7219)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize))
                    ) : SailM (BitVec esize) )
                  let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize))
                    ) : SailM (BitVec esize) )
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec esize) )
                  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__2 ← (( do (FPMulAdd_ZA element3 element1 element2 w__1) ) : SailM
                    (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op :
  Bool, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZW_2x2 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7220)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (n +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize))
                    ) : SailM (BitVec esize) )
                  let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize))
                    ) : SailM (BitVec esize) )
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec esize) )
                  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__2 ← (( do (FPMulAdd_ZA element3 element1 element2 w__1) ) : SailM
                    (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op :
  Bool, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLA_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7221)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((n +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize))
                    ) : SailM (BitVec esize) )
                  let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize))
                    ) : SailM (BitVec esize) )
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec esize) )
                  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__2 ← (( do (FPMulAdd_ZA element3 element1 element2 w__1) ) : SailM
                    (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


/-- Type quantifiers: VL : Nat, esize : Nat, m : Nat, n : Nat, nreg : Nat, offset : Nat, k_sub_op :
  Bool, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [32, 64] ∧ (is_VL VL) -/
def execute_FMLS_ZA_ZZV_2x1 (VL : Nat) (esize : Nat) (m : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (sub_op : Bool) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7222)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result, vec) ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := (result, vec)
      for r in [loop_r_lower:loop_r_upper:1]i do
        let (result, vec) := loop_vars
        loop_vars ← do
          let operand1 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Z_read (Nat.mod (Sail.Int.toNatChecked ((n +i r))) 32) VL))
            ) : SailM (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let vec : Int := vec
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let result ← (( do
            let loop_e_lower : Nat := 0
            let loop_e_upper : Int := (elements -i 1)
            (do
              let mut loop_vars_1 := result
              for e in [loop_e_lower:loop_e_upper:1]i do
                let result := loop_vars_1
                loop_vars_1 ← do
                  let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize))
                    ) : SailM (BitVec esize) )
                  let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize))
                    ) : SailM (BitVec esize) )
                  let element3 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 e esize))
                    ) : SailM (BitVec esize) )
                  let element1 ← (( do
                    if (sub_op : Bool)
                    then
                      (do
                        (FPNeg element1))
                    else (pure (element1)) ) : SailM (BitVec esize) )
                  let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                  let w__2 ← (( do (FPMulAdd_ZA element3 element1 element2 w__1) ) : SailM
                    (BitVec esize) )
                  (Elem_set result e esize (Sail.BitVec.castWidth w__2))
              (pure loop_vars_1)) ) : SailM (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure ((result, vec)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (pure (()))


end ArmFull.Functions
