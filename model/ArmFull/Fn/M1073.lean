import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0047
import ArmFull.Fn.M0054
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0116
import ArmFull.Fn.M0117
import ArmFull.Fn.M0121
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0154
import ArmFull.Fn.M0167
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0196
import ArmFull.Fn.M0202
import ArmFull.Fn.M0216
import ArmFull.Fn.M0219
import ArmFull.Fn.M0237
import ArmFull.Fn.M0254
import ArmFull.Fn.M0260
import ArmFull.Fn.M0580
import ArmFull.Fn.M0840
import ArmFull.Fn.M0924
import ArmFull.Fn.M1002
import ArmFull.Fn.M1003
import ArmFull.Fn.M1040
import ArmFull.Fn.M1044
import ArmFull.Fn.M1046
import ArmFull.Fn.M1047

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

def AArch64_MemZero (regval : (BitVec 64)) (cachetype : CacheType) : SailM Unit := do
  let w__0 ← (( do readReg DCZID_EL0 ) : SailM (BitVec 64) )
  let size : Nat :=
    (Sail.Int.toNatChecked ((4 *i (2 ^i (BitVec.toNat (_get_DCZID_EL0_Type_BS w__0))))))
  ArmFull.assert (size ≤b MAX_ZERO_BLOCK_SIZE) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36724.38-36724.39"
  let w__1 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      ArmFull.assert (size ≥b TAG_GRANULE) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:36726.34-36726.35")
  else (pure (()))
  let vaddress : (BitVec 64) := (Align_bits regval size)
  let tagaccess : Bool :=
    ((BEq.beq cachetype CacheType_Tag) || (BEq.beq cachetype CacheType_Data_Tag))
  let tagchecked : Bool := (BEq.beq cachetype CacheType_Data)
  let accdesc ← (( do (CreateAccDescDCZero tagaccess tagchecked) ) : SailM AccessDescriptor )
  if (((BEq.beq cachetype CacheType_Tag) || (BEq.beq cachetype CacheType_Data_Tag)) : Bool)
  then
    (do
      (AArch64_TagMemZero regval vaddress accdesc size))
  else (pure (()))
  if (((BEq.beq cachetype CacheType_Data) || (BEq.beq cachetype CacheType_Data_Tag)) : Bool)
  then
    (do
      (AArch64_DataMemZero regval vaddress accdesc size))
  else (pure (()))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPHalvedSub (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 2721) ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool_at (← occLabel 2722) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 2723) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2724)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 2725) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 2726) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 2727) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 2728) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 2729) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 2730) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 2731) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 2732) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 2733) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 2734) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length result) == 16) || (((Sail.BitVec.length result) == 32) || ((Sail.BitVec.length
          result) == 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:41774.41-41774.42"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
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
      if (((inf1 && inf2) && (sign1 == sign2)) : Bool)
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
          if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 1#1))) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 (Sail.BitVec.length result))))
          else
            (do
              if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 0#1))) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 (Sail.BitVec.length result))))
              else
                (do
                  if (((zero1 && zero2) && (sign1 != sign2)) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPZero sign1 (Sail.BitVec.length result))))
                  else
                    (do
                      let result_value : real := (div_real (sub_real value1_name value2_name) (2))
                      if ((eq_real result_value (0)) : Bool)
                      then
                        (do
                          let result_sign : (BitVec 1) :=
                            if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                            then 1#1
                            else 0#1
                          ((Sail.BitVec.castWidth ) <$> (FPZero result_sign
                            (Sail.BitVec.length result))))
                      else
                        (do
                          ((Sail.BitVec.castWidth ) <$> (FPRound result_value fpcr
                            (Sail.BitVec.length result)))))))))
  else (pure (result))


/-- Type quantifiers: k_ispair : Bool, size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def Mem_with_type_read__1 (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) : SailM (BitVec (size * 8)) := do
  let c ← (( do (undefined_Constraint (← occLabel 2763) ()) ) : SailM Constraint )
  ArmFull.assert ((size == 1) || ((size == 2) || ((size == 4) || ((size == 8) || (size == 16))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:41981.69-41981.70"
  let halfsize : Nat := (Sail.Int.toNatChecked ((Int.ediv size 2)))
  let value_name ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2764)
      (Sail.Int.toNatChecked ((size *i 8))))) ) : SailM (BitVec (size * 8)) )
  let alignment : Int :=
    if (ispair : Bool)
    then halfsize
    else size
  let aligned : Bool := (IsAligned__1 address alignment)
  let w__1 ← (( do
    if (((! aligned) : Bool) : Bool)
    then
      (do
        (AArch32_UnalignedAccessFaults accdesc))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__2))
  else (pure (()))
  let value_name ← (( do
    if (aligned : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (AArch32_MemSingle_read__1 address size accdesc aligned ispair)))
    else
      (do
        ArmFull.assert (size >b 1) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:41992.23-41992.24"
        let w__4 ← (( do (AArch32_MemSingle_read address 1 accdesc aligned) ) : SailM
          (BitVec (1 * 8)) )
        let value_name := ((Sail.BitVec.updateSubrange value_name 7 0 w__4) : (BitVec (size * 8)))
        let c ← (( do (ConstrainUnpredictable Unpredictable_DEVPAGE2) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_FAULT) || (BEq.beq c Constraint_NONE)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:41995.59-41995.60"
        let aligned : Bool :=
          if ((BEq.beq c Constraint_NONE) : Bool)
          then true
          else aligned
        let loop_i_lower : Nat := 1
        let loop_i_upper : Nat := (Sail.Int.toNatChecked ((size -i 1)))
        (do
          let mut loop_vars := value_name
          for i in [loop_i_lower:loop_i_upper:1]i do
            let value_name := loop_vars
            loop_vars ← do
              let w__5 ← (( do
                (AArch32_MemSingle_read (BitVec.addInt address i) 1 accdesc aligned) ) : SailM
                (BitVec (1 * 8)) )
              let value_name :=
                ((Sail.BitVec.updateSubrange value_name (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                  (Sail.Int.toNatChecked ((8 *i i))) (Sail.BitVec.castWidth w__5)) : (BitVec (size * 8)))
              (pure (value_name))
          (pure loop_vars))) ) : SailM (BitVec (size * 8)) )
  let w__6 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let value_name : (BitVec (size * 8)) :=
    if (w__6 : Bool)
    then (reverse_endianness value_name)
    else value_name
  (pure ((Sail.BitVec.castWidth value_name)))


/-- Type quantifiers: k_ispair : Bool, size : Nat, (size * 8) ≥ 0 -/
def Mem_with_type_set__1 (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) (value_in_name : (BitVec (size * 8))) : SailM Unit := do
  let c ← (( do (undefined_Constraint (← occLabel 2765) ()) ) : SailM Constraint )
  let halfsize : Nat := (Sail.Int.toNatChecked ((Int.ediv size 2)))
  let value_name : (BitVec (size * 8)) := value_in_name
  let alignment : Int :=
    if (ispair : Bool)
    then halfsize
    else size
  let aligned : Bool := (IsAligned__1 address alignment)
  let w__1 ← (( do
    if (((! aligned) : Bool) : Bool)
    then
      (do
        (AArch32_UnalignedAccessFaults accdesc))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch32_Abort address w__2))
  else (pure (()))
  let w__3 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let value_name ← (( do
    if (w__3 : Bool)
    then
      (do
        ArmFull.assert (((size *i 8) == 8) || (((size *i 8) == 16) || (((size *i 8) == 32) || (((size *i 8) == 64) || ((size *i 8) == 128))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42031.116-42031.117"
        let value_name : (BitVec (size * 8)) := (reverse_endianness value_name)
        (pure (value_name)))
    else (pure (value_name)) ) : SailM (BitVec (size * 8)) )
  if (aligned : Bool)
  then
    (do
      ArmFull.assert (((((size == 1) || (size == 2)) || (size == 4)) || (size == 8)) || (size == 16)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42035.52-42035.53"
      (AArch32_MemSingle_set__1 address size accdesc aligned ispair
        (Sail.BitVec.castWidth value_name)))
  else
    (do
      ArmFull.assert (size >b 1) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42038.23-42038.24"
      (AArch32_MemSingle_set address 1 accdesc aligned (Sail.BitVec.extractLsb value_name 7 0))
      let c ← (( do (ConstrainUnpredictable Unpredictable_DEVPAGE2) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_FAULT) || (BEq.beq c Constraint_NONE)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:42041.59-42041.60"
      let aligned : Bool :=
        if ((BEq.beq c Constraint_NONE) : Bool)
        then true
        else aligned
      let loop_i_lower : Nat := 1
      let loop_i_upper : Int := (size -i 1)
      (do
        let mut loop_vars := ()
        for i in [loop_i_lower:loop_i_upper:1]i do
          let () := loop_vars
          loop_vars ← do
            (AArch32_MemSingle_set (BitVec.addInt address i) 1 accdesc aligned
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
                (Sail.Int.toNatChecked (((8 *i i) +i 7))) (Sail.Int.toNatChecked ((8 *i i))))))
        (pure loop_vars)))


def AArch32_CheckITEnabled (mask : (BitVec 4)) : SailM Unit := do
  let accdesc ← (( do (undefined_AccessDescriptor (← occLabel 2787) ()) ) : SailM
    AccessDescriptor )
  let aligned ← (( do (undefined_bool_at (← occLabel 2788) ()) ) : SailM Bool )
  let next_instr ← (( do (undefined_bitvector_at (← occLabel 2789) 16) ) : SailM (BitVec 16) )
  let it_disabled ← (( do (undefined_bitvector_at (← occLabel 2790) 1) ) : SailM (BitVec 1) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let it_disabled ← (( do
    if ((w__0.EL == EL2) : Bool)
    then
      (do
        let w__1 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
        let it_disabled := ((_get_HSCTLR_Type_ITD w__1) : (BitVec 1))
        (pure (it_disabled)))
    else
      (do
        let w__2 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
            (pure ((_get_SCTLR_Type_ITD w__3))))
        else
          (do
            let w__4 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
            (pure ((_get_SCTLRType_ITD w__4))))) ) : SailM (BitVec 1) )
  if ((it_disabled == 1#1) : Bool)
  then
    (do
      if ((mask != 0b1000#4) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let accdesc ← (( do (CreateAccDescIFetch ()) ) : SailM AccessDescriptor )
      let aligned : Bool := true
      let w__6 ← (( do (NextInstrAddr 32) ) : SailM (BitVec 32) )
      let next_instr ← (( do (AArch32_MemSingle_read w__6 2 accdesc aligned) ) : SailM (BitVec 16)
        )
      if ((let b__0 := next_instr
         (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 15 14)) == (0b11#2 : (BitVec 2))) : Bool)
         then true
         else
           (if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 15 12)) == (0xB#4 : (BitVec 4))) : Bool)
           then true
           else
             (if (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb b__0 15 11)) == (0b10100#5 : (BitVec 5))) : Bool)
             then true
             else
               (if (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb b__0 15 11)) == (0b01001#5 : (BitVec 5))) : Bool)
               then true
               else
                 (if ((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 15 10)) == (0b010001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                          b__0 6 3)) == (0xF#4 : (BitVec 4)))) : Bool)
                 then true
                 else
                   (if ((((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 15 10)) == (0b010001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                              b__0 7 7)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                              b__0 2 0)) == (0b111#3 : (BitVec 3))))) : Bool)
                   then true
                   else false))))) : Bool)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: t : Int -/
def ICIALLUIS_SysRegWrite32_33170c116ea45e36 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPU : (BitVec 1) := (_get_HCR_EL2_Type_TPU w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TICAB : (BitVec 1) := (_get_HCR_EL2_Type_TICAB w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TPU : (BitVec 1) := (_get_HCR_Type_TPU w__5)
  let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TICAB : (BitVec 1) := (_get_HCR2_Type_TICAB w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__8 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__8) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__16 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__16) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TPU == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__22 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__20 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__20) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TICAB == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__22 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__26 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TPU == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__26 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__30 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR2_TICAB == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__30 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  (AArch32_IC CacheOpScope_ALLUIS))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              (AArch32_IC CacheOpScope_ALLUIS))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch32_IC CacheOpScope_ALLUIS))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ICIALLU_SysRegWrite32_cbf11f5ea46a9ef3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T7 : (BitVec 1) := (_get_HSTR_EL2_Type_T7 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T7 : (BitVec 1) := (_get_HSTR_Type_T7 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TPU : (BitVec 1) := (_get_HCR_EL2_Type_TPU w__3)
  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TOCU : (BitVec 1) := (_get_HCR_EL2_Type_TOCU w__4)
  let w__5 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TPU : (BitVec 1) := (_get_HCR_Type_TPU w__5)
  let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TOCU : (BitVec 1) := (_get_HCR2_Type_TOCU w__6)
  let w__7 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_FB : (BitVec 1) := (_get_HCR_Type_FB w__7)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__11 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__9 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__9) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T7 == 1#1) : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__15 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T7 == 1#1) : Bool))) ) : SailM Bool )
              if (w__15 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__19 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__17 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__17) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TPU == 1#1) : Bool))) ) : SailM Bool )
                  if (w__19 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__23 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                  (pure (((! w__21) : Bool))))
                              else (pure false)) && ((__HCR_EL2_TOCU == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__23 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__27 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL2))
                                  else (pure false)) && ((__HCR_TPU == 1#1) : Bool))) ) : SailM Bool
                            )
                          if (w__27 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__31 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR2_TOCU == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__31 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__35 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (EL2Enabled ())) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL2))
                                          else (pure false)) && ((__HCR_FB == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__35 : Bool)
                                  then
                                    (do
                                      (AArch32_IC CacheOpScope_ALLUIS))
                                  else
                                    (do
                                      (AArch32_IC CacheOpScope_ALLU)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              (AArch32_IC CacheOpScope_ALLU))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch32_IC CacheOpScope_ALLU))
              else (pure (())))))


def decode_aarch32_instrs_MRC_A1enc_A_txt (cond : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "/home/doug/boss-scratch/sail-lean-fork/integ/model/instrs32.sail:7790.29-7790.30"
      let t : Int := (BitVec.toNat Rt)
      let cp : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access coproc 0)])) == 0#1) : Bool)
        then 14
        else 15
      (execute_aarch32_instrs_MRC_Op_A_txt (Sail.Int.toNatChecked (cp)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


def decode_aarch32_instrs_MRC_T1enc_A_txt (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (Rt : (BitVec 4)) (coproc : (BitVec 1)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let t : Int := (BitVec.toNat Rt)
      let cp : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access coproc 0)])) == 0#1) : Bool)
        then 14
        else 15
      (execute_aarch32_instrs_MRC_Op_A_txt (Sail.Int.toNatChecked (cp)) (Sail.Int.toNatChecked (t))))
  else (pure (()))


end ArmFull.Functions
