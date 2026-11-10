import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0049
import ArmFull.Fn.M0061
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0118
import ArmFull.Fn.M0123
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0178
import ArmFull.Fn.M0203
import ArmFull.Fn.M0215
import ArmFull.Fn.M0216
import ArmFull.Fn.M0227
import ArmFull.Fn.M0237
import ArmFull.Fn.M0257
import ArmFull.Fn.M0259
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M1040
import ArmFull.Fn.M1041
import ArmFull.Fn.M1042
import ArmFull.Fn.M1043
import ArmFull.Fn.M1044

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

/-- Type quantifiers: d : Nat, fltsize : Nat, intsize : Nat, k_is_unsigned : Bool, n : Nat, part :
  Nat, List.elem part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  List.elem intsize [32, 64] ∧ List.elem fltsize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_convert_int (d : Nat) (fltsize : Nat) (intsize : Nat) (n : Nat) (op : FPConvOp) (part : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  if ((BEq.beq op FPConvOp_CVT_FtoI_JS) : Bool)
  then
    (do
      (CheckFPAdvSIMDEnabled64 ()))
  else
    (do
      (CheckFPEnabled64 ()))
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let fsize : Int :=
    if (((BEq.beq op FPConvOp_CVT_ItoF) && merge) : Bool)
    then 128
    else fltsize
  let fltval ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4196)
      (Sail.Int.toNatChecked (fsize)))) ) : SailM (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
  let intval ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4197)
      (Sail.Int.toNatChecked (intsize)))) ) : SailM (BitVec intsize) )
  match op with
  | .FPConvOp_CVT_FtoI =>
    (do
      let fltval ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (fsize))))
        ) : SailM (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
      ArmFull.assert ((((fsize == 16) || (fsize == 32)) || (fsize == 64)) && (((intsize == 16) || (intsize == 32)) || (intsize == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14270.80-14270.81"
      let intval ← (( do
        ((Sail.BitVec.castWidth ) <$> (FPToFixed fltval 0 is_unsigned fpcr rounding intsize)) ) :
        SailM (BitVec intsize) )
      (X_set d intsize (Sail.BitVec.castWidth intval)))
  | .FPConvOp_CVT_ItoF =>
    (do
      let intval ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n intsize)) ) : SailM
        (BitVec intsize) )
      let w__1 ← (( do
        if (merge : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked (fsize)))))
        else (pure ((Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (fsize))))))) ) :
        SailM (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
      let fltval : (BitVec (Sail.Int.toNatChecked (fsize : Int))) :=
        (w__1 : (BitVec (Sail.Int.toNatChecked (fsize : Int))))
      ArmFull.assert ((((fltsize == 16) || (fltsize == 32)) || (fltsize == 64)) && (((intsize == 16) || (intsize == 32)) || (intsize == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14278.82-14278.83"
      let w__2 ← (( do
        ((Sail.BitVec.castWidth ) <$> (FixedToFP intval 0 is_unsigned fpcr rounding fltsize)) ) :
        SailM (BitVec fltsize) )
      let w__3 ← (( do (Elem_set fltval 0 fltsize (Sail.BitVec.castWidth w__2)) ) : SailM
        (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
      let fltval := (w__3 : (BitVec (Sail.Int.toNatChecked (fsize : Int))))
      (V_set d (Sail.Int.toNatChecked (fsize)) (Sail.BitVec.castWidth fltval)))
  | .FPConvOp_MOV_FtoI =>
    (do
      let fltval ← (( do
        ((Sail.BitVec.castWidth ) <$> (Vpart_read n part (Sail.Int.toNatChecked (fsize)))) ) : SailM
        (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
      ArmFull.assert ((fsize ≥b 0) && (intsize ≥b fsize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14284.63-14284.64"
      let intval : (BitVec intsize) :=
        (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend fltval intsize))
      (X_set d intsize (Sail.BitVec.castWidth intval)))
  | .FPConvOp_MOV_ItoF =>
    (do
      let intval ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n intsize)) ) : SailM
        (BitVec intsize) )
      ArmFull.assert ((0 ≤b (fsize -i 1)) && ((fsize -i 1) <b intsize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14290.70-14290.71"
      let fltval : (BitVec (Sail.Int.toNatChecked (fsize : Int))) :=
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb intval (Sail.Int.toNatChecked ((fsize -i 1)))
          0))
      (Vpart_set d part (Sail.Int.toNatChecked (fsize)) (Sail.BitVec.castWidth fltval)))
  | .FPConvOp_CVT_FtoI_JS =>
    (do
      let z ← (( do (undefined_bitvector_at (← occLabel 4198) 1) ) : SailM (BitVec 1) )
      let fltval ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (fsize))))
        ) : SailM (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
      ArmFull.assert (fsize == 64) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14297.41-14297.42"
      ArmFull.assert (intsize == 32) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:14298.43-14298.44"
      let w__4 ← (( do
        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (FPToFixedJS (k_M := 64)
          (Sail.BitVec.castWidth fltval) fpcr true intsize)) ) : SailM ((BitVec 32) × (BitVec 1)) )
      let (tup__0, tup__1) := (w__4 : ((BitVec 32) × (BitVec 1)))
      let intval : (BitVec intsize) := (Sail.BitVec.castWidth tup__0)
      let z : (BitVec 1) := tup__1
      let split_vec := ((0#1 +++ z) +++ 0b00#2)
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb split_vec 0 0) }
      (X_set d intsize (Sail.BitVec.castWidth intval)))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_is_unsigned : Bool, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_fp16_conv_float_bulk_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4242)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__2 : (BitVec esize))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPToFixed element 0 is_unsigned fpcr rounding esize)) ) :
            SailM (BitVec esize) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__3))) )
            : SailM (BitVec 128) )
          let result := (w__4 : (BitVec 128))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Nat, esize : Nat, n : Nat, part : Nat, List.elem
  part [0, 1] ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  esize = 32 ∧ List.elem elements [1, 2] ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_float_xtn_sisd (d : Nat) (datasize : Nat) (elements : Nat) (esize : Nat) (n : Nat) (part : Nat) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked ((2 *i datasize))))) ) : SailM
    (BitVec (2 * datasize)) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := (Sail.Int.toNatChecked ((elements -i 1)))
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let w__2 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_read operand e
              (Sail.Int.toNatChecked ((2 *i esize))))) ) : SailM (BitVec (2 * esize)) )
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPConvert w__2 fpcr FPRounding_ODD esize)) ) : SailM
            (BitVec esize) )
          ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__3)))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  if (merge : Bool)
  then
    (do
      (V_set d 128 result))
  else
    (do
      let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read result 0 datasize)) ) : SailM
        (BitVec datasize) )
      (Vpart_set d part datasize (Sail.BitVec.castWidth w__5)))


/-- Type quantifiers: d : Nat, fltsize : Nat, fracbits : Nat, intsize : Nat, k_is_unsigned : Bool, n
  : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem intsize [32, 64] ∧
  1 ≤ fracbits ∧ fracbits ≤ 64 ∧ List.elem fltsize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_convert_fix (d : Nat) (fltsize : Nat) (fracbits : Nat) (intsize : Nat) (n : Nat) (op : FPConvOp) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let fsize : Int :=
    if (((BEq.beq op FPConvOp_CVT_ItoF) && merge) : Bool)
    then 128
    else fltsize
  let fltval ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4244)
      (Sail.Int.toNatChecked (fsize)))) ) : SailM (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
  let intval ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4245)
      (Sail.Int.toNatChecked (intsize)))) ) : SailM (BitVec intsize) )
  match op with
  | .FPConvOp_CVT_FtoI =>
    (do
      let fltval ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n (Sail.Int.toNatChecked (fsize))))
        ) : SailM (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
      ArmFull.assert ((((fsize == 16) || (fsize == 32)) || (fsize == 64)) && (((intsize == 16) || (intsize == 32)) || (intsize == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:16857.80-16857.81"
      let intval ← (( do
        ((Sail.BitVec.castWidth ) <$> (FPToFixed fltval fracbits is_unsigned fpcr rounding intsize))
        ) : SailM (BitVec intsize) )
      (X_set d intsize (Sail.BitVec.castWidth intval)))
  | .FPConvOp_CVT_ItoF =>
    (do
      let intval ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n intsize)) ) : SailM
        (BitVec intsize) )
      let w__1 ← (( do
        if (merge : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (V_read d (Sail.Int.toNatChecked (fsize)))))
        else (pure ((Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (fsize))))))) ) :
        SailM (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
      let fltval : (BitVec (Sail.Int.toNatChecked (fsize : Int))) :=
        (w__1 : (BitVec (Sail.Int.toNatChecked (fsize : Int))))
      let w__2 ← (( do
        ((Sail.BitVec.castWidth ) <$> (FixedToFP intval fracbits is_unsigned fpcr rounding fltsize))
        ) : SailM (BitVec fltsize) )
      let w__3 ← (( do (Elem_set fltval 0 fltsize (Sail.BitVec.castWidth w__2)) ) : SailM
        (BitVec (Sail.Int.toNatChecked (fsize : Int))) )
      let fltval := (w__3 : (BitVec (Sail.Int.toNatChecked (fsize : Int))))
      (V_set d (Sail.Int.toNatChecked (fsize)) (Sail.BitVec.castWidth fltval)))
  | _ => (pure (()))


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, fracbits : Int, k_is_unsigned
  : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_shift_conv_float_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (fracbits : Int) (n : Nat) (rounding : FPRounding) (is_unsigned : Bool) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4258)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__2 : (BitVec esize))
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPToFixed element fracbits is_unsigned fpcr rounding
              esize)) ) : SailM (BitVec esize) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__3))) )
            : SailM (BitVec 128) )
          let result := (w__4 : (BitVec 128))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_recip_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  if ((elements == 1) : Bool)
  then
    (do
      (CheckFPEnabled64 ()))
  else
    (do
      (CheckFPAdvSIMDEnabled64 ()))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4296)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__2 : (BitVec esize))
          let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__4 ← (( do (FPRecipEstimate element w__3) ) : SailM (BitVec esize) )
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__4))) )
            : SailM (BitVec 128) )
          let result := (w__5 : (BitVec 128))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_frecpx_fp16 (d : Nat) (esize : Nat) (n : Nat) : SailM Unit := do
  (CheckFPEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n esize)) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let w__1 ← (( do (FPRecpX operand fpcr) ) : SailM (BitVec esize) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__1))) ) : SailM
    (BitVec 128) )
  let result := (w__2 : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, intsize : Nat, n : Nat, 0
  ≤ n ∧
  n ≤ 31 ∧
  List.elem intsize [32, 64] ∧
  List.elem esize [32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_float_round_frint_32_64 (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (intsize : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4299)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4300)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do (FPRoundIntN element w__1 rounding intsize) ) : SailM (BitVec esize) )
          let w__3 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__2)) ) : SailM
            (BitVec datasize) )
          let result := (w__3 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, esize : Nat, intsize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem intsize [32, 64] ∧ List.elem esize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_round_frint_32_64 (d : Nat) (esize : Nat) (intsize : Nat) (n : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n esize)) ) : SailM (BitVec esize) )
  let w__1 ← (( do (FPRoundIntN operand fpcr rounding intsize) ) : SailM (BitVec esize) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__1))) ) : SailM
    (BitVec 128) )
  let result := (w__2 : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, k_exact : Bool, n : Nat, 0
  ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_fp16_round (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (exact : Bool) (n : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckFPAdvSIMDEnabled64 ())
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4301)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4302)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__0 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__0 : (BitVec esize))
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let w__2 ← (( do (FPRoundInt element w__1 rounding exact) ) : SailM (BitVec esize) )
          let w__3 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__2)) ) : SailM
            (BitVec datasize) )
          let result := (w__3 : (BitVec datasize))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec datasize)) )
  (V_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, esize : Nat, k_exact : Bool, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem esize [16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_float_arithmetic_round_frint (d : Nat) (esize : Nat) (exact : Bool) (n : Nat) (rounding : FPRounding) : SailM Unit := do
  (CheckFPEnabled64 ())
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do (IsMerging fpcr) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n esize)) ) : SailM (BitVec esize) )
  let w__1 ← (( do (FPRoundInt operand fpcr rounding exact) ) : SailM (BitVec esize) )
  let w__2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (Elem_set result 0 esize (Sail.BitVec.castWidth w__1))) ) : SailM
    (BitVec 128) )
  let result := (w__2 : (BitVec 128))
  (V_set d 128 result)


/-- Type quantifiers: d : Nat, datasize : Nat, elements : Int, esize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem esize [16, 32, 64] ∧ List.elem datasize [16, 32, 64, 128] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_vector_arithmetic_unary_special_sqrt_est_fp16_sisd (d : Nat) (datasize : Nat) (elements : Int) (esize : Nat) (n : Nat) : SailM Unit := do
  if ((elements == 1) : Bool)
  then
    (do
      (CheckFPEnabled64 ()))
  else
    (do
      (CheckFPAdvSIMDEnabled64 ()))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (V_read n datasize)) ) : SailM
    (BitVec datasize) )
  let element ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 4324)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let merge ← (( do
    if (((elements == 1) : Bool) : Bool)
    then
      (do
        (IsMerging fpcr))
    else (pure false) ) : SailM Bool )
  let result ← (( do
    if (merge : Bool)
    then
      (do
        (V_read d 128))
    else (pure ((Zeros (n := 128)))) ) : SailM (BitVec 128) )
  let (element, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (element, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (element, result) := loop_vars
        loop_vars ← do
          let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand e esize)) ) : SailM
            (BitVec esize) )
          let element := (w__2 : (BitVec esize))
          let w__3 ← (( do (FPRSqrtEstimate element fpcr) ) : SailM (BitVec esize) )
          let w__4 ← (( do
            ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth w__3))) )
            : SailM (BitVec 128) )
          let result := (w__4 : (BitVec 128))
          (pure ((element, result)))
      (pure loop_vars)) ) : SailM ((BitVec esize) × (BitVec 128)) )
  (V_set d 128 result)


/-- Type quantifiers: n : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧ 0 ≤ n ∧ n ≤ 31 -/
def execute_aarch64_instrs_memory_atomicops_ld_acc (lst : (BitVec 2)) (memop : MemOp) (n : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  (CheckLDST64BEnabled ())
  let address ← (( do (undefined_bitvector_at (← occLabel 4365) 64) ) : SailM (BitVec 64) )
  let value_name ← (( do (undefined_bitvector_at (← occLabel 4366) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescLS64 memop tagchecked) ) : SailM AccessDescriptor )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let _ : Unit := (SetLoadStoreType lst)
  let _ : Unit := (AArch64_SetLSInstructionSyndrome 64 false t true false)
  let data ← (( do (MemLoad64B address accdesc) ) : SailM (BitVec 512) )
  let value_name ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 7
    (do
      let mut loop_vars := value_name
      for i in [loop_i_lower:loop_i_upper:1]i do
        let value_name := loop_vars
        loop_vars ← do
          let value_name : (BitVec 64) :=
            (Sail.BitVec.castWidth (Sail.BitVec.extractLsb data
              (Sail.Int.toNatChecked ((63 +i (64 *i i)))) (Sail.Int.toNatChecked ((64 *i i)))))
          let w__2 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
          let value_name : (BitVec 64) :=
            if (w__2 : Bool)
            then (reverse_endianness value_name)
            else value_name
          (X_set (t +i i) 64 value_name)
          (pure (value_name))
      (pure loop_vars)) ) : SailM (BitVec 64) )
  let w__3 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (SPESampleGeneralPurposeLoadStore ()))
  else (pure (()))


/-- Type quantifiers: k_acquire : Bool, datasize : Nat, k_is_load : Bool, n : Nat, regsize : Nat, k_release
  : Bool, s : Nat, t : Nat, k_tagchecked : Bool, 0 ≤ t ∧
  t ≤ 31 ∧
  0 ≤ s ∧
  s ≤ 31 ∧
  List.elem regsize [32, 64] ∧ 0 ≤ n ∧ n ≤ 31 ∧ List.elem datasize [8, 16, 32, 64] -/
def execute_aarch64_instrs_memory_atomicops_ld (acquire : Bool) (datasize : Nat) (is_load : Bool) (n : Nat) (op : MemAtomicOp) (regsize : Nat) (release : Bool) (s : Nat) (t : Nat) (tagchecked : Bool) : SailM Unit := do
  let address ← (( do (undefined_bitvector_at (← occLabel 4367) 64) ) : SailM (BitVec 64) )
  let accdesc ← (( do (CreateAccDescAtomicOp op acquire release tagchecked) ) : SailM
    AccessDescriptor )
  let value_name ← (( do ((Sail.BitVec.castWidth ) <$> (X_read s datasize)) ) : SailM
    (BitVec datasize) )
  let address ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (CheckSPAlignment ())
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let comparevalue ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits datasize)) ) : SailM
    (BitVec datasize) )
  let data ← (( do (MemAtomic address comparevalue value_name accdesc) ) : SailM (BitVec datasize)
    )
  if ((t != 31) : Bool)
  then
    (do
      ArmFull.assert ((datasize ≥b 0) && (regsize ≥b datasize)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs64.sail:25715.67-25715.68"
      (X_set t regsize (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend data regsize))))
  else (pure (()))
  let w__2 ← (( do readReg SPESampleInFlight ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let ar : (BitVec 1) :=
        if ((acquire || release) : Bool)
        then 1#1
        else 0#1
      let excl : (BitVec 1) := 0#1
      let at' : (BitVec 1) := 1#1
      (SPESampleExtendedLoadStore ar excl at' is_load))
  else (pure (()))


end ArmFull.Functions
