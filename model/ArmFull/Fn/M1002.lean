import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0048
import ArmFull.Fn.M0050
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0114
import ArmFull.Fn.M0116
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0152
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0172
import ArmFull.Fn.M0174
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0185
import ArmFull.Fn.M0216
import ArmFull.Fn.M0237
import ArmFull.Fn.M0238
import ArmFull.Fn.M0580
import ArmFull.Fn.M0840
import ArmFull.Fn.M0851
import ArmFull.Fn.M0923
import ArmFull.Fn.M0924
import ArmFull.Fn.M0925

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

/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPRound__1 (op : real) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (N : Nat) : SailM (BitVec N) := do
  let fpexc : Bool := true
  ((Sail.BitVec.castWidth ) <$> (FPRound__2 op fpcr_in rounding fpexc N))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPUnpack (fpval : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType (← occLabel 912) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 913) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 914) ()) ) : SailM real )
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let fpexc : Bool := true
  let w__0 ← (( do (FPUnpackBase fpval fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fp_type : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  (pure ((fp_type, sign, value_name)))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPUnpack__1 (fpval : (BitVec k_N)) (fpcr_in : (BitVec 64)) (fpexc : Bool) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType (← occLabel 915) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 916) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 917) ()) ) : SailM real )
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let w__0 ← (( do (FPUnpackBase fpval fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fp_type : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  (pure ((fp_type, sign, value_name)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPProcessNaNs (type1 : FPType) (type2 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (Bool × (BitVec k_N)) := do
  let fpexc : Bool := true
  (FPProcessNaNs__1 type1 type2 op1 op2 fpcr fpexc)


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPUnpackCV (fpval : (BitVec k_N)) (fpcr_in : (BitVec 64)) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType (← occLabel 965) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 966) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 967) ()) ) : SailM real )
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 19 19 0#1)
  let fpexc : Bool := true
  let w__0 ← (( do (FPUnpackBase fpval fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fp_type : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  (pure ((fp_type, sign, value_name)))


def AArch64_CheckTag (memaddrdesc : AddressDescriptor) (accdesc : AccessDescriptor) (ptag : (BitVec 4)) : SailM Bool := do
  if ((BEq.beq memaddrdesc.memattrs.tags MemTag_AllocationTagged) : Bool)
  then
    (do
      (AArch64_AllocationTagCheck memaddrdesc accdesc ptag))
  else
    (pure (if ((BEq.beq memaddrdesc.memattrs.tags MemTag_CanonicallyTagged) : Bool)
      then (AArch64_CanonicalTagCheck memaddrdesc ptag)
      else true))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_isbfloat16 : Bool, k_N = 32 -/
def FPDot__1 (op1_a : (BitVec (k_N / 2))) (op1_b : (BitVec (k_N / 2))) (op2_a : (BitVec (k_N / 2))) (op2_b : (BitVec (k_N / 2))) (fpcr_in : (BitVec 64)) (isbfloat16 : Bool) (fpexc : Bool) : SailM (BitVec k_N) := do
  let infPa ← (( do (undefined_bool_at (← occLabel 1801) ()) ) : SailM Bool )
  let infPb ← (( do (undefined_bool_at (← occLabel 1802) ()) ) : SailM Bool )
  let invalidop ← (( do (undefined_bool_at (← occLabel 1803) ()) ) : SailM Bool )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 1804) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 1805) ()) ) : SailM real )
  let sign1_a ← (( do (undefined_bitvector_at (← occLabel 1806) 1) ) : SailM (BitVec 1) )
  let sign1_b ← (( do (undefined_bitvector_at (← occLabel 1807) 1) ) : SailM (BitVec 1) )
  let sign2_a ← (( do (undefined_bitvector_at (← occLabel 1808) 1) ) : SailM (BitVec 1) )
  let sign2_b ← (( do (undefined_bitvector_at (← occLabel 1809) 1) ) : SailM (BitVec 1) )
  let signPa ← (( do (undefined_bitvector_at (← occLabel 1810) 1) ) : SailM (BitVec 1) )
  let signPb ← (( do (undefined_bitvector_at (← occLabel 1811) 1) ) : SailM (BitVec 1) )
  let type1_a ← (( do (undefined_FPType (← occLabel 1812) ()) ) : SailM FPType )
  let type1_b ← (( do (undefined_FPType (← occLabel 1813) ()) ) : SailM FPType )
  let type2_a ← (( do (undefined_FPType (← occLabel 1814) ()) ) : SailM FPType )
  let type2_b ← (( do (undefined_FPType (← occLabel 1815) ()) ) : SailM FPType )
  let value1_a_name ← (( do (undefined_real_at (← occLabel 1816) ()) ) : SailM real )
  let value1_b_name ← (( do (undefined_real_at (← occLabel 1817) ()) ) : SailM real )
  let value2_a_name ← (( do (undefined_real_at (← occLabel 1818) ()) ) : SailM real )
  let value2_b_name ← (( do (undefined_real_at (← occLabel 1819) ()) ) : SailM real )
  let zeroPa ← (( do (undefined_bool_at (← occLabel 1820) ()) ) : SailM Bool )
  let zeroPb ← (( do (undefined_bool_at (← occLabel 1821) ()) ) : SailM Bool )
  let fpcr : FPCRType := fpcr_in
  ArmFull.assert (SPEMaxCounters == 32) "sail-arm/v8_base.sail:32331.19-32331.20"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1822)
      (Sail.Int.toNatChecked (SPEMaxCounters)))) ) : SailM (BitVec k_N) )
  let done ← (( do (undefined_bool_at (← occLabel 1823) ()) ) : SailM Bool )
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let w__0 ← (( do (FPUnpackBase__1 op1_a fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1_a : FPType := tup__0
  let sign1_a : (BitVec 1) := tup__1
  let value1_a_name : real := tup__2
  let w__1 ← (( do (FPUnpackBase__1 op1_b fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type1_b : FPType := tup__0
  let sign1_b : (BitVec 1) := tup__1
  let value1_b_name : real := tup__2
  let w__2 ← (( do (FPUnpackBase__1 op2_a fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__2 : (FPType × (BitVec 1) × real))
  let type2_a : FPType := tup__0
  let sign2_a : (BitVec 1) := tup__1
  let value2_a_name : real := tup__2
  let w__3 ← (( do (FPUnpackBase__1 op2_b fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__3 : (FPType × (BitVec 1) × real))
  let type2_b : FPType := tup__0
  let sign2_b : (BitVec 1) := tup__1
  let value2_b_name : real := tup__2
  let inf1_a : Bool := (BEq.beq type1_a FPType_Infinity)
  let zero1_a : Bool := (BEq.beq type1_a FPType_Zero)
  let inf1_b : Bool := (BEq.beq type1_b FPType_Infinity)
  let zero1_b : Bool := (BEq.beq type1_b FPType_Zero)
  let inf2_a : Bool := (BEq.beq type2_a FPType_Infinity)
  let zero2_a : Bool := (BEq.beq type2_a FPType_Zero)
  let inf2_b : Bool := (BEq.beq type2_b FPType_Infinity)
  let zero2_b : Bool := (BEq.beq type2_b FPType_Zero)
  let w__4 ← (( do
    (FPProcessNaNs4 (k_N := 32) type1_a type1_b type2_a type2_b (Sail.BitVec.castWidth op1_a)
      (Sail.BitVec.castWidth op1_b) (Sail.BitVec.castWidth op2_a) (Sail.BitVec.castWidth op2_b) fpcr
      fpexc) ) : SailM (Bool × (BitVec 32)) )
  let (tup__0, tup__1) := (w__4 : (Bool × (BitVec 32)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := (Sail.BitVec.castWidth tup__1)
  let result ← (( do
    if ((((inf1_a && zero2_a) || (zero1_a && inf2_a)) && ((inf1_b && zero2_b) || (zero1_b && inf2_b))) : Bool)
    then
      (do
        let w__5 ← (( do
          ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))) ) :
          SailM (BitVec k_N) )
        let result := (w__5 : (BitVec k_N))
        if (fpexc : Bool)
        then
          (do
            (FPProcessException FPExc_InvalidOp fpcr))
        else (pure (()))
        (pure (result)))
    else (pure (result)) ) : SailM (BitVec k_N) )
  if ((! done) : Bool)
  then
    (do
      let signPa : (BitVec 1) := (sign1_a ^^^ sign2_a)
      let signPb : (BitVec 1) := (sign1_b ^^^ sign2_b)
      let infPa : Bool := (inf1_a || inf2_a)
      let infPb : Bool := (inf1_b || inf2_b)
      let zeroPa : Bool := (zero1_a || zero2_a)
      let zeroPb : Bool := (zero1_b || zero2_b)
      let invalidop : Bool :=
        (((((inf1_a && zero2_a) || (zero1_a && inf2_a)) || (inf1_b && zero2_b)) || (zero1_b && inf2_b)) || ((infPa && infPb) && (signPa != signPb)))
      if (invalidop : Bool)
      then
        (do
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))) ) :
            SailM (BitVec k_N) )
          let result := (w__6 : (BitVec k_N))
          if (fpexc : Bool)
          then
            (do
              (FPProcessException FPExc_InvalidOp fpcr))
          else (pure (()))
          (pure (result)))
      else
        (do
          if (((infPa && (signPa == 0#1)) || (infPb && (signPb == 0#1))) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 (Sail.BitVec.length result))))
          else
            (do
              if (((infPa && (signPa == 1#1)) || (infPb && (signPb == 1#1))) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 (Sail.BitVec.length result))))
              else
                (do
                  if (((zeroPa && zeroPb) && (signPa == signPb)) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPZero signPa (Sail.BitVec.length result))))
                  else
                    (do
                      let result_value : real :=
                        (add_real (mult_real value1_a_name value2_a_name)
                          (mult_real value1_b_name value2_b_name))
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
                          ((Sail.BitVec.castWidth ) <$> (FPRound__2 result_value fpcr rounding fpexc
                            (Sail.BitVec.length result)))))))))
  else (pure (result))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFNeg (op : (BitVec k_N)) : SailM (BitVec k_N) := do
  ArmFull.assert ((Sail.BitVec.length op) == 16) "sail-arm/v8_base.sail:32442.19-32442.20"
  let honor_altfp : Bool := true
  ((Sail.BitVec.castWidth ) <$> (BFNeg__1 (k_N := 16) (Sail.BitVec.castWidth op) honor_altfp))


def SPEWriteToBuffer (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ProfilingBufferEnabled ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-arm/v8_base.sail:35284.35-35284.36"
  let w__1 ← (( do readReg PMBPTR_EL1 ) : SailM (BitVec 64) )
  let w__2 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  let aligned : Bool :=
    (is_zero_subrange (_get_PMBPTR_EL1_Type_PTR w__1)
      ((BitVec.toNat (_get_PMBIDR_EL1_Type_Align w__2)) -i 1) 0)
  let ttw_fault_as_external_abort ← (( do (__IMPDEF_boolean "SPE TTW fault External abort") ) :
    SailM Bool )
  let fault ← (( do (undefined_FaultRecord (.site 2441) ()) ) : SailM FaultRecord )
  let memstatus ← (( do (undefined_PhysMemRetStatus (.site 2442) ()) ) : SailM PhysMemRetStatus )
  let addrdesc ← (( do (undefined_AddressDescriptor (.site 2443) ()) ) : SailM AddressDescriptor )
  let owning_ss ← (( do (undefined_SecurityState (.site 2444) ()) ) : SailM SecurityState )
  let owning_el ← (( do (undefined_bitvector_at (.site 2445) 2) ) : SailM (BitVec 2) )
  let w__3 ← (( do (ProfilingBufferOwner ()) ) : SailM (SecurityState × (BitVec 2)) )
  let (tup__0, tup__1) := (w__3 : (SecurityState × (BitVec 2)))
  let owning_ss : SecurityState := tup__0
  let owning_el : (BitVec 2) := tup__1
  let accdesc ← (( do (CreateAccDescSPE owning_ss owning_el) ) : SailM AccessDescriptor )
  let w__4 ← (( do readReg PMBPTR_EL1 ) : SailM (BitVec 64) )
  let start_vaddr : (BitVec 64) := (Sail.BitVec.extractLsb w__4 63 0)
  let w__5 ← (( do readReg SPERecordSize ) : SailM Int )
  let (addrdesc, fault, memstatus) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (w__5 -i 1)
    (do
      let mut loop_vars := (addrdesc, fault, memstatus)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (addrdesc, fault, memstatus) := loop_vars
        loop_vars ← do
          let w__6 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
          if (((_get_PMBSR_EL1_Type_S w__6) == 0#1) : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b i) && (i <b 64)) "sail-arm/v8_base.sail:35297.60-35297.61"
              let w__7 ← (( do readReg PMBPTR_EL1 ) : SailM (BitVec 64) )
              let w__8 ← (( do readReg SPERecordData ) : SailM (Vector (BitVec 8) 64) )
              let w__9 ← (( do
                (DebugMemWrite (Sail.BitVec.extractLsb w__7 63 0) accdesc aligned
                  (GetElem?.getElem! w__8 (Sail.Int.toNatChecked (i)))) ) : SailM
                (PhysMemRetStatus × AddressDescriptor) )
              let (tup__0, tup__1) := (w__9 : (PhysMemRetStatus × AddressDescriptor))
              let memstatus : PhysMemRetStatus := tup__0
              let addrdesc : AddressDescriptor := tup__1
              let fault : FaultRecord := addrdesc.fault
              let ttw_fault : Bool :=
                ((BEq.beq fault.statuscode Fault_SyncExternalOnWalk) || (BEq.beq fault.statuscode
                    Fault_SyncParityOnWalk))
              if (((IsFault__1 fault.statuscode) && (! (ttw_fault && ttw_fault_as_external_abort))) : Bool)
              then
                (do
                  let w__10 ← (( do readReg PMBPTR_EL1 ) : SailM (BitVec 64) )
                  (DebugWriteFault (Sail.BitVec.extractLsb w__10 63 0) fault))
              else
                (do
                  if (((IsFault__2 memstatus) || (ttw_fault && ttw_fault_as_external_abort)) : Bool)
                  then
                    (do
                      (DebugWriteExternalAbort memstatus addrdesc start_vaddr))
                  else (pure (())))
              let w__11 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
              if ((IsZero (_get_PMBSR_EL1_Type_S w__11)) : Bool)
              then
                (do
                  let w__12 ← (( do readReg PMBPTR_EL1 ) : SailM (BitVec 64) )
                  writeReg PMBPTR_EL1 (Mk_PMBPTR_EL1_Type (BitVec.addInt w__12 1)))
              else (pure (()))
              (pure ((addrdesc, fault, memstatus))))
          else (pure ((addrdesc, fault, memstatus)))
      (pure loop_vars)) ) : SailM (AddressDescriptor × FaultRecord × PhysMemRetStatus) )
  (pure (()))


def AArch64_IC (opscope : CacheOpScope) : SailM Unit := do
  let regval ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
  (AArch64_IC__1 regval opscope)


def AArch32_DC (regval : (BitVec 32)) (cacheop : CacheOp) (opscope : CacheOpScope) : SailM Unit := do
  let cache ← (( do (undefined_CacheRecord (← occLabel 2680) ()) ) : SailM CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_DC }
  let cache : CacheRecord := { cache with cacheop := cacheop }
  let cache : CacheRecord := { cache with opscope := opscope }
  let cache : CacheRecord := { cache with cachetype := CacheType_Data }
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (SecurityStateAtEL w__0.EL) ) : SailM SecurityState )
  let cache := ({ cache with security := w__1 } : CacheRecord)
  if ((BEq.beq opscope CacheOpScope_SetWay) : Bool)
  then
    (do
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let w__2 ← (( do (DecodeSW (Sail.BitVec.zeroExtend regval 64) CacheType_Data) ) : SailM
        (Int × Int × Int) )
      let (tup__0, tup__1, tup__2) := (w__2 : (Int × Int × Int))
      let cache : CacheRecord := { cache with setnum := tup__0 }
      let cache : CacheRecord := { cache with waynum := tup__1 }
      let cache : CacheRecord := { cache with level := tup__2 }
      let w__20 ← (( do
        if ((← do
             if ((← do
                  if (((BEq.beq cacheop CacheOp_Invalidate) : Bool) : Bool)
                  then
                    (do
                      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__3.EL == EL1) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            if ((← do
                 if ((← do
                      let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__7) : Bool)))) : Bool)
                 then
                   (do
                     if ((← do
                          let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_SWIO w__8) == 1#1) : Bool)))) : Bool)
                     then (pure true)
                     else
                       (do
                         let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                         (pure (((((_get_HCR_EL2_Type_DC w__9) +++ (_get_HCR_EL2_Type_VM w__10)) != 0b00#2) : Bool)))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     (ELUsingAArch32 EL2)) : Bool)
                then
                  (do
                    if ((← do
                         let w__14 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                         (pure ((((_get_HCR_Type_SWIO w__14) == 1#1) : Bool)))) : Bool)
                    then (pure true)
                    else
                      (do
                        let w__15 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                        let w__16 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                        (pure (((((_get_HCR_Type_DC w__15) +++ (_get_HCR_Type_VM w__16)) != 0b00#2) : Bool)))))
                else (pure false)))
        else (pure false) ) : SailM Bool )
      let cache : CacheRecord :=
        if (w__20 : Bool)
        then { cache with cacheop := CacheOp_CleanInvalidate }
        else cache
      (CACHE_OP cache))
  else
    (do
      let w__21 ← (( do (EL2Enabled ()) ) : SailM Bool )
      let cache ← (( do
        if (w__21 : Bool)
        then
          (do
            let w__24 ← (( do
              if ((← do
                   let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__22.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__23.EL == EL1) : Bool)))) ) : SailM Bool )
            if (w__24 : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                let w__25 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                let cache := ({ cache with vmid := w__25 } : CacheRecord)
                (pure (cache)))
            else
              (let cache : CacheRecord := { cache with is_vmid_valid := false }
              (pure (cache))))
        else
          (let cache : CacheRecord := { cache with is_vmid_valid := false }
          (pure (cache))) ) : SailM CacheRecord )
      let w__26 ← (( do readReg PSTATE ) : SailM ProcState )
      let cache ← (( do
        if ((w__26.EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            let w__27 ← (( do (ASID_read ()) ) : SailM (BitVec 16) )
            let cache := ({ cache with asid := w__27 } : CacheRecord)
            (pure (cache)))
        else
          (let cache : CacheRecord := { cache with is_asid_valid := false }
          (pure (cache))) ) : SailM CacheRecord )
      let need_translate ← (( do (DCInstNeedsTranslation opscope) ) : SailM Bool )
      let vaddress : (BitVec 32) := regval
      let size : Int := 0
      let (size, vaddress) ← (( do
        if ((BEq.beq cacheop CacheOp_Invalidate) : Bool)
        then
          (do
            let w__28 ← (( do (__IMPDEF_integer "Data Cache Invalidate Watchpoint Size") ) : SailM
              Int )
            let size : Int := (w__28 : Int)
            let w__30 ← (( do
              (pure ((← do
                    let w__29 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
                    (pure (((size ≥b (4 *i (2 ^i (BitVec.toNat (_get_CTR_EL0_Type_DminLine w__29))))) : Bool)))) && ((size ≤b 2048) : Bool)))
              ) : SailM Bool )
            ArmFull.assert w__30 "sail-arm/v8_base.sail:40907.71-40907.72"
            ArmFull.assert ((BitVec.toNat
                ((Sail.BitVec.castWidth (m := 33) (integer_subrange size 32 0)) &&& (Sail.BitVec.castWidth (m := 33) (integer_subrange
                    (size -i 1) 32 0)))) == 0) "sail-arm/v8_base.sail:40908.61-40908.62"
            let vaddress : (BitVec 32) := (Align_bits regval size)
            (pure ((size, vaddress))))
        else (pure ((size, vaddress))) ) : SailM (Int × (BitVec 32)) )
      let size : Int := size
      let cache : CacheRecord := { cache with translated := need_translate }
      let cache : CacheRecord := { cache with vaddress := (Sail.BitVec.zeroExtend vaddress 64) }
      let cache ← (( do
        if (need_translate : Bool)
        then
          (do
            let aligned : Bool := true
            let accdesc ← (( do (CreateAccDescDC cache) ) : SailM AccessDescriptor )
            let memaddrdesc ← (( do (AArch32_TranslateAddress vaddress accdesc aligned size) ) :
              SailM AddressDescriptor )
            if ((IsFault memaddrdesc) : Bool)
            then
              (do
                (AArch32_Abort regval memaddrdesc.fault))
            else (pure (()))
            let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
            let cache : CacheRecord :=
              if ((BEq.beq opscope CacheOpScope_PoC) : Bool)
              then { cache with shareability := memaddrdesc.memattrs.shareability }
              else { cache with shareability := Shareability_NSH }
            (pure (cache)))
        else
          (do
            let w__31 ← (( do (__UNKNOWN_Shareability ()) ) : SailM Shareability )
            let cache := ({ cache with shareability := w__31 } : CacheRecord)
            let w__32 ← (( do (__UNKNOWN_FullAddress ()) ) : SailM FullAddress )
            let cache := ({ cache with paddress := w__32 } : CacheRecord)
            (pure (cache))) ) : SailM CacheRecord )
      let w__46 ← (( do
        if ((← do
             if ((← do
                  if (((BEq.beq cacheop CacheOp_Invalidate) : Bool) : Bool)
                  then
                    (do
                      let w__33 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__33.EL == EL1) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            if ((← do
                 if ((← do
                      let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__37) : Bool)))) : Bool)
                 then
                   (do
                     let w__38 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                     (pure (((((_get_HCR_EL2_Type_DC w__38) +++ (_get_HCR_EL2_Type_VM w__39)) != 0b00#2) : Bool))))
                 else (pure false)) : Bool)
            then (pure true)
            else
              (do
                if ((← do
                     (ELUsingAArch32 EL2)) : Bool)
                then
                  (do
                    let w__42 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                    let w__43 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                    (pure (((((_get_HCR_Type_DC w__42) +++ (_get_HCR_Type_VM w__43)) != 0b00#2) : Bool))))
                else (pure false)))
        else (pure false) ) : SailM Bool )
      let cache : CacheRecord :=
        if (w__46 : Bool)
        then { cache with cacheop := CacheOp_CleanInvalidate }
        else cache
      (CACHE_OP cache))


def AArch32_IC__1 (regval : (BitVec 32)) (opscope : CacheOpScope) : SailM Unit := SailME.run do
  let need_translate ← (( do (undefined_bool_at (← occLabel 2681) ()) ) : SailME Unit Bool )
  let cache ← (( do (undefined_CacheRecord (← occLabel 2682) ()) ) : SailME Unit CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_IC }
  let cache : CacheRecord := { cache with cachetype := CacheType_Instruction }
  let cache : CacheRecord := { cache with cacheop := CacheOp_Invalidate }
  let cache : CacheRecord := { cache with opscope := opscope }
  let w__0 ← (( do readReg PSTATE ) : SailME Unit ProcState )
  let w__1 ← (( do (SecurityStateAtEL w__0.EL) ) : SailME Unit SecurityState )
  let cache := ({ cache with security := w__1 } : CacheRecord)
  if (((BEq.beq opscope CacheOpScope_ALLU) || (BEq.beq opscope CacheOpScope_ALLUIS)) : Bool)
  then
    (do
      let w__8 ← (( do
        if (((BEq.beq opscope CacheOpScope_ALLUIS) : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      if (((BEq.beq opscope CacheOpScope_ALLU) : Bool) : Bool)
                      then
                        (do
                          let w__2 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                          (pure (((w__2.EL == EL1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (EL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__6 ← (( do (HCR_read ()) ) : SailME Unit (BitVec 32) )
                (pure ((((_get_HCR_Type_FB w__6) == 1#1) : Bool))))
            else (pure false)) ) : SailME Unit Bool )
      let cache : CacheRecord :=
        if (w__8 : Bool)
        then { cache with shareability := Shareability_ISH }
        else { cache with shareability := Shareability_NSH }
      let cache : CacheRecord := { cache with regval := (Sail.BitVec.zeroExtend regval 64) }
      (CACHE_OP cache))
  else
    (do
      ArmFull.assert (BEq.beq opscope CacheOpScope_PoU) "sail-arm/v8_base.sail:40964.42-40964.43"
      let w__9 ← (( do (EL2Enabled ()) ) : SailME Unit Bool )
      let cache ← (( do
        if (w__9 : Bool)
        then
          (do
            let w__12 ← (( do
              if ((← do
                   let w__10 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                   (pure (((w__10.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__11 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                  (pure (((w__11.EL == EL1) : Bool)))) ) : SailME Unit Bool )
            if (w__12 : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                let w__13 ← (( do (VMID_read ()) ) : SailME Unit (BitVec 16) )
                let cache := ({ cache with vmid := w__13 } : CacheRecord)
                (pure (cache)))
            else
              (let cache : CacheRecord := { cache with is_vmid_valid := false }
              (pure (cache))))
        else
          (let cache : CacheRecord := { cache with is_vmid_valid := false }
          (pure (cache))) ) : SailME Unit CacheRecord )
      let w__14 ← (( do readReg PSTATE ) : SailME Unit ProcState )
      let cache ← (( do
        if ((w__14.EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            let w__15 ← (( do (ASID_read ()) ) : SailME Unit (BitVec 16) )
            let cache := ({ cache with asid := w__15 } : CacheRecord)
            (pure (cache)))
        else
          (let cache : CacheRecord := { cache with is_asid_valid := false }
          (pure (cache))) ) : SailME Unit CacheRecord )
      let need_translate ← (( do (ICInstNeedsTranslation opscope) ) : SailME Unit Bool )
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let cache : CacheRecord := { cache with vaddress := (Sail.BitVec.zeroExtend regval 64) }
      let cache : CacheRecord := { cache with translated := need_translate }
      if ((! need_translate) : Bool)
      then
        (do
          let w__16 ← (( do (__UNKNOWN_FullAddress ()) ) : SailME Unit FullAddress )
          let cache := ({ cache with paddress := w__16 } : CacheRecord)
          (CACHE_OP cache)
          SailME.throw (() : Unit))
      else
        (do
          let size : Nat := 0
          let aligned : Bool := true
          let accdesc ← (( do (CreateAccDescIC cache) ) : SailME Unit AccessDescriptor )
          let memaddrdesc ← (( do (AArch32_TranslateAddress regval accdesc aligned size) ) :
            SailME Unit AddressDescriptor )
          if ((IsFault memaddrdesc) : Bool)
          then
            (do
              (AArch32_Abort regval memaddrdesc.fault))
          else (pure (()))
          let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
          (CACHE_OP cache)))


end ArmFull.Functions
