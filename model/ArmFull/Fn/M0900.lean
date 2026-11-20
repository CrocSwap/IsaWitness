module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0866 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_hi : Bool, k_is_unsigned : Bool, n : Nat, 0
  ≤ n ∧ n ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_SUNPKHI_Z_Z__ (VL : Nat) (d : Nat) (esize : Nat) (hi : Bool) (n : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let hsize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 2)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5413)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do
            if (hi : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand (e +i elements) hsize)))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (Elem_read operand e hsize))) ) : SailM
            (BitVec (Sail.Int.toNatChecked hsize)) )
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend element esize is_unsigned)) ) :
            SailM (BitVec esize) )
          (Elem_set result e esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_setflags : Bool, List.elem esize
  [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PTRUE_P_S__ (VL : Nat) (d : Nat) (esize : Nat) (pat : (BitVec 5)) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5414)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let pbit : (BitVec 1) :=
            if ((e <b count) : Bool)
            then 1#1
            else 0#1
          (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest result result esize) ) : SailM (BitVec 4) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, k_setflags : Bool, List.elem esize
  [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PTRUES_P_S__ (VL : Nat) (d : Nat) (esize : Nat) (pat : (BitVec 5)) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let count ← (( do (DecodePredCount pat esize) ) : SailM Int )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5415)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let pbit : (BitVec 1) :=
            if ((e <b count) : Bool)
            then 1#1
            else 0#1
          (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest result result esize) ) : SailM (BitVec 4) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_PFALSE_P__ (VL : Nat) (d : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  (P_set d PL (Sail.BitVec.castWidth (Zeros (n := PL))))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ (is_VL VL) -/
def execute_PTEST__P_P__ (VL : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb split_vec 0 0) }


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, k_setflags
  : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKA_P_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read d PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let break' : Bool := false
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5416)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (break', result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (break', result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (break', result) := loop_vars
        loop_vars ← do
          let element ← (( do (ActivePredicateElement operand e esize) ) : SailM Bool )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              let pbit : (BitVec 1) :=
                if ((! break') : Bool)
                then 1#1
                else 0#1
              let w__1 ← (( do
                (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
                ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
              let result := (w__1 : (BitVec (Sail.Int.toNatChecked PL)))
              let break' : Bool := (break' || element)
              (pure ((break', result))))
          else
            (do
              let result ← (( do
                if (merging : Bool)
                then
                  (do
                    let pbit ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
                    (Elem_set result e psize
                      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
                else
                  (do
                    (Elem_set result e psize
                      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize)))) ) : SailM
                (BitVec (Sail.Int.toNatChecked PL)) )
              (pure ((break', result))))
      (pure loop_vars)) ) : SailM (Bool × (BitVec (Sail.Int.toNatChecked PL))) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, k_setflags
  : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKAS_P_P_P_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read d PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let break' : Bool := false
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5417)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (break', result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (break', result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (break', result) := loop_vars
        loop_vars ← do
          let element ← (( do (ActivePredicateElement operand e esize) ) : SailM Bool )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              let pbit : (BitVec 1) :=
                if ((! break') : Bool)
                then 1#1
                else 0#1
              let w__1 ← (( do
                (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
                ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
              let result := (w__1 : (BitVec (Sail.Int.toNatChecked PL)))
              let break' : Bool := (break' || element)
              (pure ((break', result))))
          else
            (do
              let result ← (( do
                if (merging : Bool)
                then
                  (do
                    let pbit ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
                    (Elem_set result e psize
                      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
                else
                  (do
                    (Elem_set result e psize
                      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize)))) ) : SailM
                (BitVec (Sail.Int.toNatChecked PL)) )
              (pure ((break', result))))
      (pure loop_vars)) ) : SailM (Bool × (BitVec (Sail.Int.toNatChecked PL))) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, k_setflags
  : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKB_P_P_P__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read d PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let break' : Bool := false
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5418)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (break', result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (break', result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (break', result) := loop_vars
        loop_vars ← do
          let element ← (( do (ActivePredicateElement operand e esize) ) : SailM Bool )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              let break' : Bool := (break' || element)
              let pbit : (BitVec 1) :=
                if ((! break') : Bool)
                then 1#1
                else 0#1
              let w__1 ← (( do
                (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
                ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
              let result := (w__1 : (BitVec (Sail.Int.toNatChecked PL)))
              (pure ((break', result))))
          else
            (do
              let result ← (( do
                if (merging : Bool)
                then
                  (do
                    let pbit ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
                    (Elem_set result e psize
                      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
                else
                  (do
                    (Elem_set result e psize
                      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize)))) ) : SailM
                (BitVec (Sail.Int.toNatChecked PL)) )
              (pure ((break', result))))
      (pure loop_vars)) ) : SailM (Bool × (BitVec (Sail.Int.toNatChecked PL))) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, k_merging : Bool, n : Nat, k_setflags
  : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BRKBS_P_P_P_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (merging : Bool) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read d PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let break' : Bool := false
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5419)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let (break', result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (break', result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (break', result) := loop_vars
        loop_vars ← do
          let element ← (( do (ActivePredicateElement operand e esize) ) : SailM Bool )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              let break' : Bool := (break' || element)
              let pbit : (BitVec 1) :=
                if ((! break') : Bool)
                then 1#1
                else 0#1
              let w__1 ← (( do
                (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize)))
                ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
              let result := (w__1 : (BitVec (Sail.Int.toNatChecked PL)))
              (pure ((break', result))))
          else
            (do
              let result ← (( do
                if (merging : Bool)
                then
                  (do
                    let pbit ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
                    (Elem_set result e psize
                      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend pbit psize))))
                else
                  (do
                    (Elem_set result e psize
                      (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize)))) ) : SailM
                (BitVec (Sail.Int.toNatChecked PL)) )
              (pure ((break', result))))
      (pure loop_vars)) ) : SailM (Bool × (BitVec (Sail.Int.toNatChecked PL))) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0
  ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_AND_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5420)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
          let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              (Elem_set result e psize
                (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (element1 &&& element2) psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0
  ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_ANDS_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5421)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
          let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              (Elem_set result e psize
                (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend (element1 &&& element2) psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, m : Nat, n : Nat, k_setflags : Bool, 0
  ≤ n ∧
  n ≤ 15 ∧
  0 ≤ m ∧
  m ≤ 15 ∧ 0 ≤ g ∧ g ≤ 15 ∧ esize = 8 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_BIC_P_P_PP_Z (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read m PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5422)
      (Sail.Int.toNatChecked (PL)))) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  let psize : Nat := (Sail.Int.toNatChecked ((Int.ediv esize 8)))
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do (PredicateElement operand1 e esize) ) : SailM (BitVec 1) )
          let element2 ← (( do (PredicateElement operand2 e esize) ) : SailM (BitVec 1) )
          let w__0 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              (Elem_set result e psize
                (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend
                  (element1 &&& (Complement.complement element2)) psize))))
          else
            (do
              (Elem_set result e psize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend 0#1 psize))))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked PL)) )
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result esize) ) : SailM (BitVec 4) )
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


end ArmFull.Functions
