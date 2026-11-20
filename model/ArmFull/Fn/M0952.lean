module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0226
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M0878
public import ArmFull.Fn.M0879 set_option backward.proofsInPublic true @[expose] public section

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

def decode_UZP_MZ_ZZ_2Q (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let d : Int := (BitVec.toNat (Zd +++ 0#1))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_ZZ_2Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_ZIP_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UZP_MZ_Z_4 (size : (BitVec 2)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_ZIP_MZ_Z_4Q (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_ZIP_MZ_Z_4Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_UZP_MZ_Z_4Q (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 128
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4Q 128 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4Q 256 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4Q 512 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4Q 1024 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_UZP_MZ_Z_4Q 2048 (Sail.Int.toNatChecked (d)) esize (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_SEL_MZ_P_ZZ_2 (size : (BitVec 2)) (Zm : (BitVec 4)) (PNg : (BitVec 3)) (Zn : (BitVec 4)) (Zd : (BitVec 4)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat (Zn +++ 0#1))
      let m : Int := (BitVec.toNat (Zm +++ 0#1))
      let d : Int := (BitVec.toNat (Zd +++ 0#1))
      let g : Int := (BitVec.toNat (1#1 +++ PNg))
      let nreg : Nat := 2
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_2 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_2 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_2 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_2 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_2 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | _ => (pure (())))


def decode_SEL_MZ_P_ZZ_4 (size : (BitVec 2)) (Zm : (BitVec 3)) (PNg : (BitVec 3)) (Zn : (BitVec 3)) (Zd : (BitVec 3)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSME2 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
      let n : Int := (BitVec.toNat (Zn +++ 0b00#2))
      let m : Int := (BitVec.toNat (Zm +++ 0b00#2))
      let d : Int := (BitVec.toNat (Zd +++ 0b00#2))
      let g : Int := (BitVec.toNat (1#1 +++ PNg))
      let nreg : Nat := 4
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_4 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_4 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_4 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_4 1024 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_SEL_MZ_P_ZZ_4 2048 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
            (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) nreg))
      | _ => (pure (())))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_BMOPA_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7548)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize)) ) :
            SailM (BitVec esize) )
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 col esize))
                  ) : SailM (BitVec esize) )
                let element3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let res : Int := (BitCount (Complement.complement (element1 ^^^ element2)))
                    let res : Int :=
                      if (sub_op : Bool)
                      then (Neg.neg res)
                      else res
                    let res : Int := res
                    (Elem_set result ((row *i dim) +i col) esize
                      (Sail.BitVec.castWidth (BitVec.addInt element3 res))))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, m :
  Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_BMOPS_ZA_PP_ZZ_32 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7549)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let result ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := result
      for row in [loop_row_lower:loop_row_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 row esize)) ) :
            SailM (BitVec esize) )
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := result
            for col in [loop_col_lower:loop_col_upper:1]i do
              let result := loop_vars_1
              loop_vars_1 ← do
                let element2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 col esize))
                  ) : SailM (BitVec esize) )
                let element3 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let w__2 ← (( do
                  if ((← do
                       (ActivePredicateElement mask1 row esize)) : Bool)
                  then
                    (do
                      (ActivePredicateElement mask2 col esize))
                  else (pure false) ) : SailM Bool )
                if (w__2 : Bool)
                then
                  (do
                    let res : Int := (BitCount (Complement.complement (element1 ^^^ element2)))
                    let res : Int :=
                      if (sub_op : Bool)
                      then (Neg.neg res)
                      else res
                    let res : Int := res
                    (Elem_set result ((row *i dim) +i col) esize
                      (Sail.BitVec.castWidth (BitVec.addInt element3 res))))
                else
                  (do
                    (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth element3)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (BitVec dim_dim_esize) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_SMOPA_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7550)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7551) ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := (prod, result)
      for row in [loop_row_lower:loop_row_upper:1]i do
        let (prod, result) := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := (prod, result)
            for col in [loop_col_lower:loop_col_upper:1]i do
              let (prod, result) := loop_vars_1
              loop_vars_1 ← do
                let sum ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let (prod, sum) ← (( do
                  let loop_k_lower : Nat := 0
                  let loop_k_upper : Nat := 1
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__6 ← (( do (asl_Int w__5 is_unsigned) ) : SailM Int )
                            let prod : Int := ((w__4 *i w__6) : Int)
                            let prod : Int :=
                              if (sub_op : Bool)
                              then (Neg.neg prod)
                              else prod
                            let sum : (BitVec esize) := (BitVec.addInt sum prod)
                            (pure ((prod, sum))))
                        else (pure ((prod, sum)))
                    (pure loop_vars_2)) ) : SailM (Int × (BitVec esize)) )
                let w__7 ← (( do
                  (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth sum)) ) :
                  SailM (BitVec dim_dim_esize) )
                let result := (w__7 : (BitVec dim_dim_esize))
                (pure ((prod, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, a : Nat, b : Nat, da : Nat, dim_dim_esize : Nat, esize : Nat, k_is_unsigned
  : Bool, m : Nat, n : Nat, k_sub_op : Bool, 0 ≤ n ∧
  n ≤ 31 ∧
  0 ≤ m ∧
  m ≤ 31 ∧
  esize = 32 ∧
  List.elem da [0, 1, 2, 3] ∧
  List.elem b [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem a [0, 1, 2, 3, 4, 5, 6, 7] ∧
  (is_VL VL) ∧ dim_dim_esize = (VL / esize * (VL / esize * esize)) -/
def execute_UMOPA_ZA32_PP_ZZ_16 (VL : Nat) (dim_dim_esize : Nat) (a : Nat) (b : Nat) (da : Nat) (esize : Nat) (m : Nat) (n : Nat) (sub_op : Bool) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let mask1 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read a PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let mask2 ← (( do ((Sail.BitVec.castWidth ) <$> (P_read b PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
  let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (ZAtile_read VL da esize dim_dim_esize)) ) :
    SailM (BitVec dim_dim_esize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7552)
      (Sail.Int.toNatChecked (dim_dim_esize)))) ) : SailM (BitVec dim_dim_esize) )
  let prod ← (( do (undefined_int_at (← occLabel 7553) ()) ) : SailM Int )
  let (prod, result) ← (( do
    let loop_row_lower : Nat := 0
    let loop_row_upper : Int := (dim -i 1)
    (do
      let mut loop_vars := (prod, result)
      for row in [loop_row_lower:loop_row_upper:1]i do
        let (prod, result) := loop_vars
        loop_vars ← do
          let loop_col_lower : Nat := 0
          let loop_col_upper : Int := (dim -i 1)
          (do
            let mut loop_vars_1 := (prod, result)
            for col in [loop_col_lower:loop_col_upper:1]i do
              let (prod, result) := loop_vars_1
              loop_vars_1 ← do
                let sum ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read operand3 ((row *i dim) +i col) esize)) )
                  : SailM (BitVec esize) )
                let (prod, sum) ← (( do
                  let loop_k_lower : Nat := 0
                  let loop_k_upper : Nat := 1
                  (do
                    let mut loop_vars_2 := (prod, sum)
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let (prod, sum) := loop_vars_2
                      loop_vars_2 ← do
                        let w__2 ← (( do
                          if ((← do
                               (ActivePredicateElement mask1 ((2 *i row) +i k) (Int.ediv esize 2))) : Bool)
                          then
                            (do
                              (ActivePredicateElement mask2 ((2 *i col) +i k) (Int.ediv esize 2)))
                          else (pure false) ) : SailM Bool )
                        if (w__2 : Bool)
                        then
                          (do
                            let w__3 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 ((2 *i row) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__4 ← (( do (asl_Int w__3 is_unsigned) ) : SailM Int )
                            let w__5 ← (( do
                              ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 ((2 *i col) +i k)
                                (Sail.Int.toNatChecked ((Int.ediv esize 2))))) ) : SailM
                              (BitVec (esize / 2)) )
                            let w__6 ← (( do (asl_Int w__5 is_unsigned) ) : SailM Int )
                            let prod : Int := ((w__4 *i w__6) : Int)
                            let prod : Int :=
                              if (sub_op : Bool)
                              then (Neg.neg prod)
                              else prod
                            let sum : (BitVec esize) := (BitVec.addInt sum prod)
                            (pure ((prod, sum))))
                        else (pure ((prod, sum)))
                    (pure loop_vars_2)) ) : SailM (Int × (BitVec esize)) )
                let w__7 ← (( do
                  (Elem_set result ((row *i dim) +i col) esize (Sail.BitVec.castWidth sum)) ) :
                  SailM (BitVec dim_dim_esize) )
                let result := (w__7 : (BitVec dim_dim_esize))
                (pure ((prod, result)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Int × (BitVec dim_dim_esize)) )
  (ZAtile_set VL da esize dim_dim_esize (Sail.BitVec.castWidth result))


end ArmFull.Functions
