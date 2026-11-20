module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0120
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0237
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0255
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1123
public import ArmFull.Fn.M1136 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMINNM_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5185)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do (BFMinNum (k_N := 16) element1 element2 w__3) ) : SailM (BitVec 16)
                )
              (Elem_set result e 16 w__4))
          else
            (do
              (Elem_set result e 16 element1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMAX_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5186)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do (BFMax (k_N := 16) element1 element2 w__3) ) : SailM (BitVec 16) )
              (Elem_set result e 16 w__4))
          else
            (do
              (Elem_set result e 16 element1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, dn : Nat, g : Nat, m : Nat, 0 ≤ m ∧
  m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_BFMIN_Z_P_ZZ__ (VL : Nat) (dn : Nat) (g : Nat) (m : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read dn VL)) ) : SailM (BitVec VL) )
  let w__0 ← (( do (AnyActiveElement mask 16) ) : SailM Bool )
  let operand2 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read m VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5187)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let w__2 ← (( do (ActivePredicateElement mask e 16) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
              let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
              let w__4 ← (( do (BFMin (k_N := 16) element1 element2 w__3) ) : SailM (BitVec 16) )
              (Elem_set result e 16 w__4))
          else
            (do
              (Elem_set result e 16 element1))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set dn VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCLAMP_Z_ZZ__ (VL : Nat) (d : Nat) (m : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5188)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read d VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
          let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__1 ← (( do (BFMaxNum (k_N := 16) element1 element3 w__0) ) : SailM (BitVec 16) )
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (BFMinNum (k_N := 16) w__1 element2 w__2) ) : SailM (BitVec 16) )
          (Elem_set result e 16 w__3)
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_FABS_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FABS_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FABS_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FABS_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FABS_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FABS_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_FNEG_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Zd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNEG_Z_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNEG_Z_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNEG_Z_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNEG_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FNEG_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


/-- Type quantifiers: VL : Nat, imm : Int, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_LDR_P_BI__ (VL : Nat) (imm : Int) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Int := (Int.ediv PL 8)
  let base ← (( do (undefined_bitvector_at (← occLabel 5825) 64) ) : SailM (BitVec 64) )
  let offset : Int := (imm *i elements)
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5826)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base offset) 2)
  let w__3 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AlignmentEnforced ()))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let w__4 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort (BitVec.addInt base offset) w__4))
  else (pure (()))
  let (offset, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (offset, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (offset, result) := loop_vars
        loop_vars ← do
          let offset : Int := offset
          let w__5 ← (( do (AArch64_MemSingle_read (BitVec.addInt base offset) 1 accdesc aligned)
            ) : SailM (BitVec (1 * 8)) )
          let w__6 ← (( do (Elem_set result e 8 w__5) ) : SailM
            (BitVec (Sail.Int.toNatChecked PL)) )
          let result := (w__6 : (BitVec (Sail.Int.toNatChecked PL)))
          let offset : Int := (offset +i 1)
          (pure ((offset, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec (Sail.Int.toNatChecked PL))) )
  (P_set t PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, imm : Int, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 ∧ (is_VL VL) -/
def execute_LDR_Z_BI__ (VL : Nat) (imm : Int) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let base ← (( do (undefined_bitvector_at (← occLabel 5827) 64) ) : SailM (BitVec 64) )
  let offset : Int := (imm *i elements)
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5828)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let base ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let aligned : Bool := (IsAligned__1 (BitVec.addInt base offset) 16)
  let w__3 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AlignmentEnforced ()))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let w__4 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort (BitVec.addInt base offset) w__4))
  else (pure (()))
  let (offset, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (offset, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (offset, result) := loop_vars
        loop_vars ← do
          let offset : Int := offset
          let w__5 ← (( do (AArch64_MemSingle_read (BitVec.addInt base offset) 1 accdesc aligned)
            ) : SailM (BitVec (1 * 8)) )
          let w__6 ← (( do (Elem_set result e 8 w__5) ) : SailM (BitVec VL) )
          let result := (w__6 : (BitVec VL))
          let offset : Int := (offset +i 1)
          (pure ((offset, result)))
      (pure loop_vars)) ) : SailM (Int × (BitVec VL)) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LDNF1B_Z_P_BI_U8 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6188) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6189)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let orig ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6190)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure (base)))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64))) ) : SailM (BitVec 64) )
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, fault, faulted, result, unknown)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, fault, faulted, result, unknown) := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let (data, fault) ← (( do
            if (w__6 : Bool)
            then
              (do
                let eoff : Int := ((offset *i elements) +i e)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                let w__7 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemNF_read addr mbytes
                    accdesc)) ) : SailM ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool) )
                let (tup__0, tup__1) :=
                  (w__7 : ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool))
                let data : (BitVec msize) := (Sail.BitVec.castWidth tup__0)
                let fault : Bool := tup__1
                (pure ((data, fault))))
            else
              (let (tup__0, tup__1) :=
                (((Sail.BitVec.castWidth (Zeros (n := msize))), false) : ((BitVec msize) × Bool))
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure ((data, fault)))) ) : SailM ((BitVec msize) × Bool) )
          let faulted : Bool := (faulted || fault)
          if (faulted : Bool)
          then
            (do
              (ElemFFR_set e esize 0#1))
          else (pure (()))
          let w__9 ← (( do
            if ((unknown : Bool) : Bool)
            then (pure true)
            else
              (do
                let w__8 ← (( do (ElemFFR_read e esize) ) : SailM (BitVec 1) )
                (pure (((w__8 == 0#1) : Bool)))) ) : SailM Bool )
          let unknown := (w__9 : Bool)
          let result ← (( do
            if (unknown : Bool)
            then
              (do
                let w__11 ← (( do
                  if (((! fault) : Bool) : Bool)
                  then
                    (do
                      (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA))
                  else (pure false) ) : SailM Bool )
                if (w__11 : Bool)
                then
                  (do
                    let w__12 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) : SailM
                      (BitVec esize) )
                    (Elem_set result e esize (Sail.BitVec.castWidth w__12)))
                else
                  (do
                    let w__14 ← (( do (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO) ) :
                      SailM Bool )
                    if (w__14 : Bool)
                    then
                      (do
                        (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))))
                    else
                      (do
                        let w__16 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read orig e esize))
                          ) : SailM (BitVec esize) )
                        (Elem_set result e esize (Sail.BitVec.castWidth w__16)))))
            else
              (do
                let w__18 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) )
                  : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__18))) ) : SailM (BitVec VL) )
          (pure ((data, fault, faulted, result, unknown)))
      (pure loop_vars)) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, msize : Nat, n : Nat, offset
  : Int, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ msize = 8 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LDNF1B_Z_P_BI_U16 (VL : Nat) (esize : Nat) (g : Nat) (msize : Nat) (n : Nat) (offset : Int) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6191) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6192)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let orig ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read t VL)) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6193)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let fault : Bool := false
  let faulted : Bool := false
  let unknown : Bool := false
  let contiguous : Bool := true
  let tagchecked : Bool := (n != 31)
  let accdesc ← (( do (CreateAccDescSVENF contiguous tagchecked) ) : SailM AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let base ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure (base)))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        if ((n == 31) : Bool)
        then
          (do
            (SP_read ()))
        else
          (do
            (X_read n 64))) ) : SailM (BitVec 64) )
  let (data, fault, faulted, result, unknown) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, fault, faulted, result, unknown)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, fault, faulted, result, unknown) := loop_vars
        loop_vars ← do
          let w__6 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          let (data, fault) ← (( do
            if (w__6 : Bool)
            then
              (do
                let eoff : Int := ((offset *i elements) +i e)
                let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
                let w__7 ← (( do
                  ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (MemNF_read addr mbytes
                    accdesc)) ) : SailM ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool) )
                let (tup__0, tup__1) :=
                  (w__7 : ((BitVec (8 * (Sail.Int.toNatChecked mbytes))) × Bool))
                let data : (BitVec msize) := (Sail.BitVec.castWidth tup__0)
                let fault : Bool := tup__1
                (pure ((data, fault))))
            else
              (let (tup__0, tup__1) :=
                (((Sail.BitVec.castWidth (Zeros (n := msize))), false) : ((BitVec msize) × Bool))
              let data : (BitVec msize) := tup__0
              let fault : Bool := tup__1
              (pure ((data, fault)))) ) : SailM ((BitVec msize) × Bool) )
          let faulted : Bool := (faulted || fault)
          if (faulted : Bool)
          then
            (do
              (ElemFFR_set e esize 0#1))
          else (pure (()))
          let w__9 ← (( do
            if ((unknown : Bool) : Bool)
            then (pure true)
            else
              (do
                let w__8 ← (( do (ElemFFR_read e esize) ) : SailM (BitVec 1) )
                (pure (((w__8 == 0#1) : Bool)))) ) : SailM Bool )
          let unknown := (w__9 : Bool)
          let result ← (( do
            if (unknown : Bool)
            then
              (do
                let w__11 ← (( do
                  if (((! fault) : Bool) : Bool)
                  then
                    (do
                      (ConstrainUnpredictableBool Unpredictable_SVELDNFDATA))
                  else (pure false) ) : SailM Bool )
                if (w__11 : Bool)
                then
                  (do
                    let w__12 ← (( do
                      ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) : SailM
                      (BitVec esize) )
                    (Elem_set result e esize (Sail.BitVec.castWidth w__12)))
                else
                  (do
                    let w__14 ← (( do (ConstrainUnpredictableBool Unpredictable_SVELDNFZERO) ) :
                      SailM Bool )
                    if (w__14 : Bool)
                    then
                      (do
                        (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))))
                    else
                      (do
                        let w__16 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read orig e esize))
                          ) : SailM (BitVec esize) )
                        (Elem_set result e esize (Sail.BitVec.castWidth w__16)))))
            else
              (do
                let w__18 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) )
                  : SailM (BitVec esize) )
                (Elem_set result e esize (Sail.BitVec.castWidth w__18))) ) : SailM (BitVec VL) )
          (pure ((data, fault, faulted, result, unknown)))
      (pure loop_vars)) ) : SailM ((BitVec msize) × Bool × Bool × (BitVec VL) × Bool) )
  (Z_set t VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
