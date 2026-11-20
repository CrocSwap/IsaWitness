module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0900
public import ArmFull.Fn.M0901 set_option backward.proofsInPublic true @[expose] public section

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

def decode_PTRUES_P_S__ (size : (BitVec 2)) (S : (BitVec 1)) (pattern : (BitVec 5)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := true
      let pat : (BitVec 5) := pattern
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUES_P_S__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUES_P_S__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUES_P_S__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUES_P_S__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTRUES_P_S__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize)) pat
            setflags))
      | _ => (pure (())))


def decode_PFALSE_P__ (S : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let d : Int := (BitVec.toNat Pd)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFALSE_P__ 128 (Sail.Int.toNatChecked (d))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFALSE_P__ 256 (Sail.Int.toNatChecked (d))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFALSE_P__ 512 (Sail.Int.toNatChecked (d))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFALSE_P__ 1024 (Sail.Int.toNatChecked (d))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PFALSE_P__ 2048 (Sail.Int.toNatChecked (d))))
      | _ => (pure (())))


/-- Type quantifiers: VL : Nat, d : Nat, 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_RDFFR_P_F__ (VL : Nat) (d : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let ffr ← (( do ((Sail.BitVec.castWidth ) <$> (FFR_read PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  (P_set d PL (Sail.BitVec.castWidth ffr))


/-- Type quantifiers: VL : Nat, n : Nat, 0 ≤ n ∧ n ≤ 15 ∧ (is_VL VL) -/
def execute_WRFFR_F_P__ (VL : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (P_read n PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let hsb : Int := (HighestSetBit operand)
  if (((hsb <b 0) || (is_ones_subrange operand hsb 0)) : Bool)
  then
    (do
      (FFR_set PL (Sail.BitVec.castWidth operand)))
  else
    (do
      let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits PL)) ) : SailM
        (BitVec (Sail.Int.toNatChecked PL)) )
      (FFR_set PL (Sail.BitVec.castWidth w__0)))


/-- Type quantifiers: VL : Nat, d : Nat, g : Nat, k_setflags : Bool, 0 ≤ g ∧
  g ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_RDFFR_P_P_F__ (VL : Nat) (d : Nat) (g : Nat) (setflags : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let ffr ← (( do ((Sail.BitVec.castWidth ) <$> (FFR_read PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result : (BitVec (Sail.Int.toNatChecked PL)) := (ffr &&& mask)
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result 8) ) : SailM (BitVec 4) )
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, g : Nat, k_setflags : Bool, 0 ≤ g ∧
  g ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 ∧ (is_VL VL) -/
def execute_RDFFRS_P_P_F__ (VL : Nat) (d : Nat) (g : Nat) (setflags : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let ffr ← (( do ((Sail.BitVec.castWidth ) <$> (FFR_read PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let result : (BitVec (Sail.Int.toNatChecked PL)) := (ffr &&& mask)
  if (setflags : Bool)
  then
    (do
      let split_vec ← (( do (PredTest mask result 8) ) : SailM (BitVec 4) )
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (P_set d PL (Sail.BitVec.castWidth result))


def decode_PTEST__P_P__ (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTEST__P_P__ 128 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTEST__P_P__ 256 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTEST__P_P__ 512 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTEST__P_P__ 1024 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_PTEST__P_P__ 2048 esize (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BRKA_P_P_P__ (B : (BitVec 1)) (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (M : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let d : Int := (BitVec.toNat Pd)
      let merging : Bool := (M == 1#1)
      let setflags : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKA_P_P_P__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKA_P_P_P__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKA_P_P_P__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKA_P_P_P__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKA_P_P_P__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_BRKAS_P_P_P_Z (B : (BitVec 1)) (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (M : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let d : Int := (BitVec.toNat Pd)
      let merging : Bool := false
      let setflags : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKAS_P_P_P_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKAS_P_P_P_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKAS_P_P_P_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKAS_P_P_P_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKAS_P_P_P_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_BRKB_P_P_P__ (B : (BitVec 1)) (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (M : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let d : Int := (BitVec.toNat Pd)
      let merging : Bool := (M == 1#1)
      let setflags : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKB_P_P_P__ 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKB_P_P_P__ 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKB_P_P_P__ 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKB_P_P_P__ 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKB_P_P_P__ 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_BRKBS_P_P_P_Z (B : (BitVec 1)) (S : (BitVec 1)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (M : (BitVec 1)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let d : Int := (BitVec.toNat Pd)
      let merging : Bool := false
      let setflags : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKBS_P_P_P_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKBS_P_P_P_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKBS_P_P_P_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKBS_P_P_P_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BRKBS_P_P_P_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            merging (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_AND_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let m : Int := (BitVec.toNat Pm)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_AND_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_ANDS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let m : Int := (BitVec.toNat Pm)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ANDS_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ANDS_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ANDS_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ANDS_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ANDS_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_BIC_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let m : Int := (BitVec.toNat Pm)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BIC_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


def decode_BICS_P_P_PP_Z (S : (BitVec 1)) (Pm : (BitVec 4)) (Pg : (BitVec 4)) (Pn : (BitVec 4)) (Pd : (BitVec 4)) : SailM Unit := do
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
      let esize : Nat := 8
      let g : Int := (BitVec.toNat Pg)
      let n : Int := (BitVec.toNat Pn)
      let m : Int := (BitVec.toNat Pm)
      let d : Int := (BitVec.toNat Pd)
      let setflags : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BICS_P_P_PP_Z 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BICS_P_P_PP_Z 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BICS_P_P_PP_Z 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BICS_P_P_PP_Z 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BICS_P_P_PP_Z 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))
      | _ => (pure (())))


end ArmFull.Functions
