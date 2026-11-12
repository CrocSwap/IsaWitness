import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0015
import ArmFull.Fn.M0018
import ArmFull.Fn.M0116
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0167
import ArmFull.Fn.M0178
import ArmFull.Fn.M0840
import ArmFull.Fn.M0852
import ArmFull.Fn.M0923
import ArmFull.Fn.M1002
import ArmFull.Fn.M1024
import ArmFull.Fn.M1040
import ArmFull.Fn.M1041
import ArmFull.Fn.M1042
import ArmFull.Fn.M1043

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

/-- Type quantifiers: pc : Int -/
def __DecodeA64_DataProcFPSIMD__seg15 (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__1145 ← (( do
    if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
               __opcode 21 10)) == (0x84A#12 : (BitVec 12))))) : Bool) : Bool)
    then
      (do
        let w__1144 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__1144 <b 1034) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1145 : Bool)
  then
    (do
      writeReg SEE 1034
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let size := (BitVec.slice __opcode 22 2)
      let Q := (BitVec.slice __opcode 30 1)
      (decode_xtn_advsimd_aarch64_instrs_vector_arithmetic_unary_extract_nosat Rd Rn size Q))
  else
    (do
      let w__1147 ← (( do
        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                     __opcode 15 10)) == (0b001110#6 : (BitVec 6)))))) : Bool) : Bool)
        then
          (do
            let w__1146 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__1146 <b 1035) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1147 : Bool)
      then
        (do
          writeReg SEE 1035
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let op := (BitVec.slice __opcode 14 1)
          let Rm := (BitVec.slice __opcode 16 5)
          let size := (BitVec.slice __opcode 22 2)
          let Q := (BitVec.slice __opcode 30 1)
          (decode_zip1_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm size Q))
      else
        (do
          let w__1149 ← (( do
            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31 31)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 29 24)) == (0b001110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                         __opcode 15 10)) == (0b011110#6 : (BitVec 6)))))) : Bool) : Bool)
            then
              (do
                let w__1148 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__1148 <b 1036) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__1149 : Bool)
          then
            (do
              writeReg SEE 1036
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let op := (BitVec.slice __opcode 14 1)
              let Rm := (BitVec.slice __opcode 16 5)
              let size := (BitVec.slice __opcode 22 2)
              let Q := (BitVec.slice __opcode 30 1)
              (decode_zip2_advsimd_aarch64_instrs_vector_transfer_vector_permute_zip Rd Rn op Rm
                size Q))
          else sailThrow ((Error_Undefined ()))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPAdd (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPAdd__1 op1 op2 fpcr fpexc)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPAdd_ZA (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (FPAdd__1 op1 op2 fpcr fpexc)


/-- Type quantifiers: M : Nat, k_N : Nat, List.elem M [16, 32, 64] ∧ List.elem k_N [16, 32, 64] -/
def FPConvert__1 (op : (BitVec k_N)) (fpcr : (BitVec 64)) (M : Nat) : SailM (BitVec M) := do
  let w__0 ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  ((Sail.BitVec.castWidth ) <$> (FPConvert op fpcr w__0 M))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPDiv (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 973) ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool_at (← occLabel 974) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 975) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 976)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 977) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 978) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 979) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 980) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 981) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 982) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 983) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 984) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length
          result) == 64))) "sail-arm/v8_base.sail:16583.41-16583.42"
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs type1 type2 op1 op2 fpcr) ) : SailM (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && inf2) || (zero1 && zero2)) : Bool)
        then
          (do
            let w__3 ← (( do
              ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))) ) :
              SailM (BitVec k_N) )
            let result := (w__3 : (BitVec k_N))
            (FPProcessException FPExc_InvalidOp fpcr)
            (pure (result)))
        else
          (do
            if ((inf1 || zero2) : Bool)
            then
              (do
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity (sign1 ^^^ sign2)
                    (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                let result := (w__4 : (BitVec k_N))
                if ((! inf1) : Bool)
                then
                  (do
                    (FPProcessException FPExc_DivideByZero fpcr))
                else (pure (()))
                (pure (result)))
            else
              (do
                if ((zero1 || inf2) : Bool)
                then
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPZero (sign1 ^^^ sign2)
                      (Sail.BitVec.length result))))
                else
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPRound (div_real value1_name value2_name) fpcr
                      (Sail.BitVec.length result)))))) ) : SailM (BitVec k_N) )
      if ((! zero2) : Bool)
      then
        (do
          (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr))
      else (pure (()))
      (pure (result)))
  else (pure (result))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMax (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  (FPMax__1 op1 op2 fpcr altfp)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMaxNum (op1_in : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let type1 ← (( do (undefined_FPType (← occLabel 997) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 998) ()) ) : SailM FPType )
  ArmFull.assert (((Sail.BitVec.length op2_in) == 16) || (((Sail.BitVec.length op2_in) == 32) || ((Sail.BitVec.length
          op2_in) == 64))) "sail-arm/v8_base.sail:16680.41-16680.42"
  let op1 : (BitVec k_N) := op1_in
  let op2 : (BitVec k_N) := op2_in
  let (__tup_0, _, _) ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let type1 : FPType := __tup_0
  let (__tup_0, _, _) ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let type2 : FPType := __tup_0
  let type1_nan : Bool := ((BEq.beq type1 FPType_QNaN) || (BEq.beq type1 FPType_SNaN))
  let type2_nan : Bool := ((BEq.beq type2 FPType_QNaN) || (BEq.beq type2 FPType_SNaN))
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let (op1, op2) ← (( do
    if ((! ((altfp && type1_nan) && type2_nan)) : Bool)
    then
      (do
        if (((BEq.beq type1 FPType_QNaN) && (bne type2 FPType_QNaN)) : Bool)
        then
          (do
            let w__3 ← (( do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 (Sail.BitVec.length op2_in))) ) : SailM
              (BitVec k_N) )
            let op1 := (w__3 : (BitVec k_N))
            (pure ((op1, op2))))
        else
          (do
            let op2 ← (( do
              if (((bne type1 FPType_QNaN) && (BEq.beq type2 FPType_QNaN)) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 (Sail.BitVec.length op2_in))))
              else (pure (op2)) ) : SailM (BitVec k_N) )
            (pure ((op1, op2)))))
    else (pure ((op1, op2))) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
  let altfmaxfmin : Bool := false
  (FPMax__1 op1 op2 fpcr altfmaxfmin)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMin (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  (FPMin__1 op1 op2 fpcr altfp)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMinNum (op1_in : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let type1 ← (( do (undefined_FPType (← occLabel 1011) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1012) ()) ) : SailM FPType )
  ArmFull.assert (((Sail.BitVec.length op2_in) == 16) || (((Sail.BitVec.length op2_in) == 32) || ((Sail.BitVec.length
          op2_in) == 64))) "sail-arm/v8_base.sail:16782.41-16782.42"
  let op1 : (BitVec k_N) := op1_in
  let op2 : (BitVec k_N) := op2_in
  let (__tup_0, _, _) ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let type1 : FPType := __tup_0
  let (__tup_0, _, _) ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let type2 : FPType := __tup_0
  let type1_nan : Bool := ((BEq.beq type1 FPType_QNaN) || (BEq.beq type1 FPType_SNaN))
  let type2_nan : Bool := ((BEq.beq type2 FPType_QNaN) || (BEq.beq type2 FPType_SNaN))
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let (op1, op2) ← (( do
    if ((! ((altfp && type1_nan) && type2_nan)) : Bool)
    then
      (do
        if (((BEq.beq type1 FPType_QNaN) && (bne type2 FPType_QNaN)) : Bool)
        then
          (do
            let w__3 ← (( do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 (Sail.BitVec.length op2_in))) ) : SailM
              (BitVec k_N) )
            let op1 := (w__3 : (BitVec k_N))
            (pure ((op1, op2))))
        else
          (do
            let op2 ← (( do
              if (((bne type1 FPType_QNaN) && (BEq.beq type2 FPType_QNaN)) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 (Sail.BitVec.length op2_in))))
              else (pure (op2)) ) : SailM (BitVec k_N) )
            (pure ((op1, op2)))))
    else (pure ((op1, op2))) ) : SailM ((BitVec k_N) × (BitVec k_N)) )
  let altfmaxfmin : Bool := false
  (FPMin__1 op1 op2 fpcr altfmaxfmin)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMul (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 1013) ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool_at (← occLabel 1014) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1015) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1016)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1017) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1018) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1019) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1020) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1021) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1022) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1023) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1024) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length
          result) == 64))) "sail-arm/v8_base.sail:16824.41-16824.42"
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs type1 type2 op1 op2 fpcr) ) : SailM (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
        then
          (do
            let w__3 ← (( do
              ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))) ) :
              SailM (BitVec k_N) )
            let result := (w__3 : (BitVec k_N))
            (FPProcessException FPExc_InvalidOp fpcr)
            (pure (result)))
        else
          (do
            if ((inf1 || inf2) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (FPInfinity (sign1 ^^^ sign2)
                  (Sail.BitVec.length result))))
            else
              (do
                if ((zero1 || zero2) : Bool)
                then
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPZero (sign1 ^^^ sign2)
                      (Sail.BitVec.length result))))
                else
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPRound (mult_real value1_name value2_name) fpcr
                      (Sail.BitVec.length result)))))) ) : SailM (BitVec k_N) )
      (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
      (pure (result)))
  else (pure (result))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPMulAdd__1 addend op1 op2 fpcr fpexc)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMulAdd_ZA (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (FPMulAdd__1 addend op1 op2 fpcr fpexc)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPMulX (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool_at (← occLabel 1047) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1048) ()) ) : SailM Bool )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1049) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1050) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1051) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1052) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1053) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1054) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1055) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1056) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-arm/v8_base.sail:17040.41-17040.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1057)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let done ← (( do (undefined_bool_at (← occLabel 1058) ()) ) : SailM Bool )
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs type1 type2 op1 op2 fpcr) ) : SailM (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let result ← (( do
        if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (FPTwo (sign1 ^^^ sign2) (Sail.BitVec.length result))))
        else
          (do
            if ((inf1 || inf2) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (FPInfinity (sign1 ^^^ sign2)
                  (Sail.BitVec.length result))))
            else
              (do
                if ((zero1 || zero2) : Bool)
                then
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPZero (sign1 ^^^ sign2)
                      (Sail.BitVec.length result))))
                else
                  (do
                    ((Sail.BitVec.castWidth ) <$> (FPRound (mult_real value1_name value2_name) fpcr
                      (Sail.BitVec.length result)))))) ) : SailM (BitVec k_N) )
      (FPProcessDenorms type1 type2 (Sail.BitVec.length result) fpcr)
      (pure (result)))
  else (pure (result))


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPMulAddH (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  ((Sail.BitVec.castWidth ) <$> (FPMulAddH__1 (k_N := 32) (Sail.BitVec.castWidth addend)
    (Sail.BitVec.castWidth op1) (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPMulAddH_ZA (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  ((Sail.BitVec.castWidth ) <$> (FPMulAddH__1 (k_N := 32) (Sail.BitVec.castWidth addend)
    (Sail.BitVec.castWidth op1) (Sail.BitVec.castWidth op2) fpcr fpexc))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPSqrt (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType (← occLabel 1124) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1125) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1126) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "sail-arm/v8_base.sail:17724.41-17724.42"
  let w__0 ← (( do (FPUnpack op fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1127)
      (Sail.BitVec.length op))) ) : SailM (BitVec k_N) )
  if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
  then
    (do
      (FPProcessNaN fptype op fpcr))
  else
    (do
      if ((BEq.beq fptype FPType_Zero) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
      else
        (do
          if (((BEq.beq fptype FPType_Infinity) && (sign == 0#1)) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))))
          else
            (do
              if ((sign == 1#1) : Bool)
              then
                (do
                  let w__4 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result)))
                    ) : SailM (BitVec k_N) )
                  let result := (w__4 : (BitVec k_N))
                  (FPProcessException FPExc_InvalidOp fpcr)
                  (pure (result)))
              else
                (do
                  let w__5 ← (( do (sqrt_real value_name) ) : SailM real )
                  let w__6 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (FPRound w__5 fpcr (Sail.BitVec.length result))) )
                    : SailM (BitVec k_N) )
                  let result := (w__6 : (BitVec k_N))
                  (FPProcessDenorm fptype (Sail.BitVec.length result) fpcr)
                  (pure (result))))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPSub (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPSub__1 op1 op2 fpcr fpexc)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPSub_ZA (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpcr : FPCRType := fpcr_in
  let fpexc : Bool := false
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 25 25 1#1)
  (FPSub__1 op1 op2 fpcr fpexc)


/-- Type quantifiers: k_aligned : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch64_MemSingle_read (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (aligned : Bool) : SailM (BitVec (size * 8)) := do
  let ispair : Bool := false
  ((Sail.BitVec.castWidth ) <$> (AArch64_MemSingle_read__1 address size accdesc aligned ispair))


/-- Type quantifiers: k_aligned : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def AArch64_MemSingle_set (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (aligned : Bool) (value_name : (BitVec (size * 8))) : SailM Unit := do
  let ispair : Bool := false
  (AArch64_MemSingle_set__1 address size accdesc aligned ispair (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPRecipStepFused (op1_in : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool_at (← occLabel 1681) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1682) ()) ) : SailM Bool )
  let result_value ← (( do (undefined_real_at (← occLabel 1683) ()) ) : SailM real )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1684) 1) ) : SailM (BitVec 1) )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1685) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1686) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1687) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1688) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1689) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1690) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1691) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1692) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-arm/v8_base.sail:29114.41-29114.42"
  let op1 : (BitVec k_N) := op1_in
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1693)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let done ← (( do (undefined_bool_at (← occLabel 1694) ()) ) : SailM Bool )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let op1 ← (( do (FPNeg op1) ) : SailM (BitVec k_N) )
  let altfp ← (( do
    (pure ((← do
          (HaveAltFP ())) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType :=
        (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then (Sail.BitVec.updateSubrange fpcr 23 22 0b00#2)
    else fpcr
  let w__1 ← (( do (FPUnpack__1 op1 fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__2 ← (( do (FPUnpack__1 op2 fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__2 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__3 ← (( do (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc) ) : SailM
    (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__3 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPTwo 0#1 (Sail.BitVec.length result))))
      else
        (do
          if ((inf1 || inf2) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity (sign1 ^^^ sign2)
                (Sail.BitVec.length result))))
          else
            (do
              let result_value : real := (add_real (2) (mult_real value1_name value2_name))
              if ((eq_real result_value (0)) : Bool)
              then
                (do
                  let sign : (BitVec 1) :=
                    if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                    then 1#1
                    else 0#1
                  ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
              else
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPRound__2 result_value fpcr rounding fpexc
                    (Sail.BitVec.length result)))))))
  else (pure (result))


end ArmFull.Functions
