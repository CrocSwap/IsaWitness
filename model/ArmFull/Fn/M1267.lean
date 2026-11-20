module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0237
public import ArmFull.Fn.M0255
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1197 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1RQB_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6116) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6117) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6118) 128) ) : SailM (BitVec 128) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
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
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let eoff : Int := ((BitVec.toNat offset) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__8))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Z_set t VL
    (Sail.BitVec.castWidth (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 128))))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1RQH_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6119) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6120) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6121) 128) ) : SailM (BitVec 128) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
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
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let eoff : Int := ((BitVec.toNat offset) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__8))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Z_set t VL
    (Sail.BitVec.castWidth (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 128))))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1RQW_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6122) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6123) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6124) 128) ) : SailM (BitVec 128) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
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
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let eoff : Int := ((BitVec.toNat offset) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__8))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Z_set t VL
    (Sail.BitVec.castWidth (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 128))))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1RQD_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6125) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6126) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6127) 128) ) : SailM (BitVec 128) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
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
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let eoff : Int := ((BitVec.toNat offset) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__8))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (Z_set t VL
    (Sail.BitVec.castWidth (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 128))))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 8 ∧ (is_VL VL) -/
def execute_LD1ROB_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  if ((VL <b 256) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 256 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6128) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6129) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6130) 256) ) : SailM (BitVec 256) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
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
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let eoff : Int := ((BitVec.toNat offset) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__8))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 256) )
  (Z_set t VL
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
      (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 256)))) VL)))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 16 ∧ (is_VL VL) -/
def execute_LD1ROH_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  if ((VL <b 256) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 256 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6131) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6132) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6133) 256) ) : SailM (BitVec 256) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
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
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let eoff : Int := ((BitVec.toNat offset) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__8))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 256) )
  (Z_set t VL
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
      (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 256)))) VL)))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1ROW_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  if ((VL <b 256) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 256 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6134) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6135) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6136) 256) ) : SailM (BitVec 256) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
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
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let eoff : Int := ((BitVec.toNat offset) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__8))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 256) )
  (Z_set t VL
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
      (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 256)))) VL)))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ (is_VL VL) -/
def execute_LD1ROD_Z_P_BR_Contiguous (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (t : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  if ((VL <b 256) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv 256 esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 6137) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do (undefined_bitvector_at (← occLabel 6138) 64) ) : SailM (BitVec 64) )
  let result ← (( do (undefined_bitvector_at (← occLabel 6139) 256) ) : SailM (BitVec 256) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let contiguous : Bool := true
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
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
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
        let offset := (w__6 : (BitVec 64))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec 64)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let eoff : Int := ((BitVec.toNat offset) +i e)
              let addr : (BitVec 64) := (BitVec.addInt base (eoff *i mbytes))
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (esize / 8 * 8)) )
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__8))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize
                (Sail.BitVec.castWidth (Zeros (n := esize))))))
      (pure loop_vars)) ) : SailM (BitVec 256) )
  (Z_set t VL
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
      (BitVec.replicateBits result (Sail.Int.toNatChecked ((Int.ediv VL 256)))) VL)))


end ArmFull.Functions
