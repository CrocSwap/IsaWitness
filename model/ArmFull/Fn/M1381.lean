module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M1235
public import ArmFull.Fn.M1249
public import ArmFull.Fn.M1250 set_option backward.proofsInPublic true @[expose] public section

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

def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := true
      let zero_data : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodatapre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := false
      let zero_data : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stz2g_aarch64_instrs_integer_tags_mcsettagpairandzerodata (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := false
      let postindex : Bool := false
      let zero_data : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpairandzerodatapost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := true
      let zero_data : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodatapre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := false
      let zero_data : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stzg_aarch64_instrs_integer_tags_mcsettagandzerodata (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := false
      let postindex : Bool := false
      let zero_data : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagandzerodatapost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stzgm_aarch64_instrs_integer_tags_mcsettagandzeroarray (Xt : (BitVec 5)) (Xn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Xt)
      let n : Int := (BitVec.toNat Xn)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagandzeroarray (Sail.Int.toNatChecked (n))
        (Sail.Int.toNatChecked (t))))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FADDV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:5346.45-5346.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM (BitVec esize)
    )
  let w__2 ← (( do (ReducePredicated ReduceOp_FADD operand mask identity) ) : SailM (BitVec esize)
    )
  (V_set d esize (Sail.BitVec.castWidth w__2))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNMV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:5407.45-5407.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN esize)) ) : SailM
    (BitVec esize) )
  let w__2 ← (( do (ReducePredicated ReduceOp_FMAXNUM operand mask identity) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__2))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNMV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:5468.45-5468.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN esize)) ) : SailM
    (BitVec esize) )
  let w__2 ← (( do (ReducePredicated ReduceOp_FMINNUM operand mask identity) ) : SailM
    (BitVec esize) )
  (V_set d esize (Sail.BitVec.castWidth w__2))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:5529.45-5529.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 esize)) ) : SailM
    (BitVec esize) )
  let w__2 ← (( do (ReducePredicated ReduceOp_FMAX operand mask identity) ) : SailM (BitVec esize)
    )
  (V_set d esize (Sail.BitVec.castWidth w__2))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINV_V_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:5590.45-5590.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 esize)) ) : SailM
    (BitVec esize) )
  let w__2 ← (( do (ReducePredicated ReduceOp_FMIN operand mask identity) ) : SailM (BitVec esize)
    )
  (V_set d esize (Sail.BitVec.castWidth w__2))


def decode_FADDQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
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
          let d : Int := (BitVec.toNat Vd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_FMAXNMQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
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
          let d : Int := (BitVec.toNat Vd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_FMINNMQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
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
          let d : Int := (BitVec.toNat Vd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_FMAXQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
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
          let d : Int := (BitVec.toNat Vd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_FMINQV_Z_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE2p1 ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME2p1 ()) ) : SailM Bool )
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
          let d : Int := (BitVec.toNat Vd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINQV_Z_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINQV_Z_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINQV_Z_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINQV_Z_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINQV_Z_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_LD1B_Z_P_BZ_S_x32_unscaled (xs : (BitVec 1)) (Zm : (BitVec 5)) (U : (BitVec 1)) (ff : (BitVec 1)) (Pg : (BitVec 3)) (Rn : (BitVec 5)) (Zt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Zt)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Zm)
      let g : Int := (BitVec.toNat Pg)
      let esize : Nat := 32
      let msize : Nat := 8
      let offs_size : Nat := 32
      let is_unsigned : Bool := true
      let offs_unsigned : Bool := (xs == 0#1)
      let scale : Nat := 0
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LD1B_Z_P_BZ_S_x32_unscaled 128 esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) offs_size offs_unsigned
            scale (Sail.Int.toNatChecked (t)) is_unsigned))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LD1B_Z_P_BZ_S_x32_unscaled 256 esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) offs_size offs_unsigned
            scale (Sail.Int.toNatChecked (t)) is_unsigned))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LD1B_Z_P_BZ_S_x32_unscaled 512 esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) offs_size offs_unsigned
            scale (Sail.Int.toNatChecked (t)) is_unsigned))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LD1B_Z_P_BZ_S_x32_unscaled 1024 esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) offs_size offs_unsigned
            scale (Sail.Int.toNatChecked (t)) is_unsigned))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_LD1B_Z_P_BZ_S_x32_unscaled 2048 esize (Sail.Int.toNatChecked (g))
            (Sail.Int.toNatChecked (m)) msize (Sail.Int.toNatChecked (n)) offs_size offs_unsigned
            scale (Sail.Int.toNatChecked (t)) is_unsigned))
      | _ => (pure (())))


end ArmFull.Functions
