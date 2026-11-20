module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0898 set_option backward.proofsInPublic true @[expose] public section

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

def decode_ZIP2_Z_ZZ__ (size : (BitVec 2)) (Zm : (BitVec 5)) (H : (BitVec 1)) (Zn : (BitVec 5)) (Zd : (BitVec 5)) : SailM Unit := do
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
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat Zd)
      let part : Nat := 1
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ__ 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP2_Z_ZZ__ 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) part))
      | _ => (pure (())))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TRN1_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__0)) )
            : SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_TRN2_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          let w__1 ← (( do (Elem_set result ((2 *i p) +i 0) esize (Sail.BitVec.castWidth w__0)) )
            : SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP1_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let base : Nat := (Sail.Int.toNatChecked ((part *i pairs)))
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
            : SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (base +i p) esize)) )
            : SailM (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_ZIP2_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
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
            : SailM (BitVec VL) )
          let result := (w__1 : (BitVec VL))
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 (base +i p) esize)) )
            : SailM (BitVec esize) )
          (Elem_set result ((2 *i p) +i 1) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 0 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP1_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result p esize (Sail.BitVec.castWidth w__0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result (pairs +i p) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, m : Nat, n : Nat, part : Nat, part = 1 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ esize = 128 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_UZP2_Z_ZZ_Q (VL : Nat) (d : Nat) (esize : Nat) (m : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  if ((VL <b (esize *i 2)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL (Sail.Int.toNatChecked ((esize *i 2))))))
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__0 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result p esize (Sail.BitVec.castWidth w__0))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  let result ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := result
      for p in [loop_p_lower:loop_p_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i p) +i part) esize)) ) : SailM
            (BitVec esize) )
          (Elem_set result (pairs +i p) esize (Sail.BitVec.castWidth w__2))
      (pure loop_vars)) ) : SailM (BitVec VL) )
  (Z_set d VL (Sail.BitVec.castWidth result))


def decode_CLASTA_R_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Zm)
      let csize : Nat :=
        if ((esize <b 64) : Bool)
        then 32
        else 64
      let isBefore : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_R_P_Z__ 128 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_R_P_Z__ 256 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_R_P_Z__ 512 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_R_P_Z__ 1024 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_R_P_Z__ 2048 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_CLASTB_R_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Rdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Rdn)
      let m : Int := (BitVec.toNat Zm)
      let csize : Nat :=
        if ((esize <b 64) : Bool)
        then 32
        else 64
      let isBefore : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_R_P_Z__ 128 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_R_P_Z__ 256 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_R_P_Z__ 512 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_R_P_Z__ 1024 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_R_P_Z__ 2048 csize (Sail.Int.toNatChecked (dn))
            (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g)) isBefore
            (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_CLASTA_V_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Vdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Vdn)
      let m : Int := (BitVec.toNat Zm)
      let isBefore : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_V_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_V_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_V_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_V_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_V_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_CLASTB_V_P_Z__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Vdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Vdn)
      let m : Int := (BitVec.toNat Zm)
      let isBefore : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_V_P_Z__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_V_P_Z__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_V_P_Z__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_V_P_Z__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_V_P_Z__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_CLASTA_Z_P_ZZ__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      let isBefore : Bool := false
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTA_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


def decode_CLASTB_Z_P_ZZ__ (size : (BitVec 2)) (B : (BitVec 1)) (Pg : (BitVec 3)) (Zm : (BitVec 5)) (Zdn : (BitVec 5)) : SailM Unit := do
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
      let g : Int := (BitVec.toNat Pg)
      let dn : Int := (BitVec.toNat Zdn)
      let m : Int := (BitVec.toNat Zm)
      let isBefore : Bool := true
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_Z_P_ZZ__ 128 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_Z_P_ZZ__ 256 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_Z_P_ZZ__ 512 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_Z_P_ZZ__ 1024 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_CLASTB_Z_P_ZZ__ 2048 (Sail.Int.toNatChecked (dn)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) isBefore (Sail.Int.toNatChecked (m))))
      | _ => (pure (())))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_COMPACT_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand1 ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  let result : (BitVec VL) := (Sail.BitVec.castWidth (Zeros (n := VL)))
  let x : Int := 0
  let (result, x) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (result, x)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (result, x) := loop_vars
        loop_vars ← do
          let w__2 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let element ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                SailM (BitVec esize) )
              let x : Int := x
              let w__3 ← (( do (Elem_set result x esize (Sail.BitVec.castWidth element)) ) : SailM
                (BitVec VL) )
              let result := (w__3 : (BitVec VL))
              let x : Int := (x +i 1)
              (pure ((result, x))))
          else (pure ((result, x)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × Int) )
  (Z_set d VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
