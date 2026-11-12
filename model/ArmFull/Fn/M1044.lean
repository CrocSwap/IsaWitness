import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0018
import ArmFull.Fn.M0034
import ArmFull.Fn.M0041
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0115
import ArmFull.Fn.M0116
import ArmFull.Fn.M0117
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0168
import ArmFull.Fn.M0173
import ArmFull.Fn.M0204
import ArmFull.Fn.M0217
import ArmFull.Fn.M0244
import ArmFull.Fn.M0255
import ArmFull.Fn.M0257
import ArmFull.Fn.M0840
import ArmFull.Fn.M0851
import ArmFull.Fn.M0852
import ArmFull.Fn.M0923
import ArmFull.Fn.M0924
import ArmFull.Fn.M1002

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

def MemStore64BWithRet (address : (BitVec 64)) (value_name : (BitVec 512)) (accdesc_in : AccessDescriptor) : SailM (BitVec 64) := SailME.run do
  let size : Nat := 64
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address size)
  let w__1 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AArch64_UnalignedAccessFaults accdesc address size))
    else (pure false) ) : SailME (BitVec 64) Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (AlignmentFault accdesc) ) : SailME (BitVec 64) FaultRecord )
      (AArch64_Abort address w__2))
  else (pure (()))
  let w__4 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailME (BitVec 64) Bool )
  let accdesc ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (AArch64_AccessIsTagChecked address accdesc) ) : SailME (BitVec 64) Bool
          )
        let accdesc := ({ accdesc with tagchecked := w__5 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailME (BitVec 64) AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailME
    (BitVec 64) AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault)
      (pure ((Sail.BitVec.zeroExtend 1#1 64))))
  else
    (do
      let _ : Unit :=
        if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
        then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) 64)
        else ()
      let w__7 ← (( do
        (pure ((← do
              (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailME (BitVec 64) Bool )
      if (w__7 : Bool)
      then
        (do
          let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
          let w__8 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailME (BitVec 64) Bool
            )
          if ((! w__8) : Bool)
          then
            (do
              (AArch64_TagCheckFault address accdesc)
              SailME.throw ((Sail.BitVec.zeroExtend 1#1 64) : (BitVec 64)))
          else (pure (())))
      else (pure (()))
      let memstatus ← (( do
        (PhysMemWrite memaddrdesc size accdesc none (Sail.BitVec.castWidth value_name)) ) : SailME
        (BitVec 64) PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalWriteAbort memstatus memaddrdesc size accdesc))
      else (pure (()))
      (pure (memstatus.store64bstatus)))


def MemLoad64B (address : (BitVec 64)) (accdesc_in : AccessDescriptor) : SailM (BitVec 512) := do
  let c ← (( do (undefined_Constraint (← occLabel 1672) ()) ) : SailM Constraint )
  let data ← (( do (undefined_bitvector_at (← occLabel 1673) 512) ) : SailM (BitVec 512) )
  let size : Nat := 64
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address size)
  let w__1 ← (( do
    if ((! aligned) : Bool)
    then
      (do
        (AArch64_UnalignedAccessFaults accdesc address size))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort address w__2))
  else (pure (()))
  let w__4 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  let accdesc ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (AArch64_AccessIsTagChecked address accdesc) ) : SailM Bool )
        let accdesc := ({ accdesc with tagchecked := w__5 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault))
  else (pure (()))
  let _ : Unit :=
    if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
    then (ClearExclusiveByAddress memaddrdesc.paddress (ProcessorID ()) size)
    else ()
  let w__7 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
      let w__8 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
      if ((! w__8) : Bool)
      then
        (do
          (AArch64_TagCheckFault address accdesc))
      else (pure (())))
  else (pure (()))
  let w__9 ← (( do (AddressSupportsLS64 memaddrdesc.paddress.address) ) : SailM Bool )
  if ((! w__9) : Bool)
  then
    (do
      let c ← (( do (ConstrainUnpredictable Unpredictable_LS64UNSUPPORTED) ) : SailM Constraint )
      ArmFull.assert ((BEq.beq c Constraint_LIMITED_ATOMICITY) || (BEq.beq c Constraint_FAULT)) "sail-arm/v8_base.sail:28910.72-28910.73"
      if ((BEq.beq c Constraint_FAULT) : Bool)
      then
        (do
          let w__10 ← (( do (ExclusiveFault accdesc) ) : SailM FaultRecord )
          (AArch64_Abort address w__10)
          (pure (data)))
      else
        (do
          let (data, memaddrdesc) ← (( do
            let loop_i_lower : Nat := 0
            let loop_i_upper : Int := (size -i 1)
            (do
              let mut loop_vars := (data, memaddrdesc)
              for i in [loop_i_lower:loop_i_upper:1]i do
                let (data, memaddrdesc) := loop_vars
                loop_vars ← do
                  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1675) ()) ) :
                    SailM PhysMemRetStatus )
                  let w__11 ← (( do (PhysMemRead memaddrdesc 1 accdesc none) ) : SailM
                    (PhysMemRetStatus × (BitVec (8 * 1))) )
                  let (tup__0, tup__1) := (w__11 : (PhysMemRetStatus × (BitVec (8 * 1))))
                  let memstatus : PhysMemRetStatus := tup__0
                  let data : (BitVec 512) :=
                    (Sail.BitVec.updateSubrange data (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                      (Sail.Int.toNatChecked ((8 *i i))) (Sail.BitVec.castWidth tup__1))
                  if ((IsFault__2 memstatus) : Bool)
                  then
                    (do
                      (HandleExternalReadAbort memstatus memaddrdesc 1 accdesc))
                  else (pure (()))
                  let memaddrdesc : AddressDescriptor :=
                    { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt
                          memaddrdesc.paddress.address 1) } }
                  (pure ((data, memaddrdesc)))
              (pure loop_vars)) ) : SailM ((BitVec 512) × AddressDescriptor) )
          (pure (data))))
  else
    (do
      let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1674) ()) ) : SailM
        PhysMemRetStatus )
      let w__12 ← (( do
        ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead memaddrdesc size
          accdesc none)) ) : SailM (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked size))))
        )
      let (tup__0, tup__1) :=
        (w__12 : (PhysMemRetStatus × (BitVec (8 * (Sail.Int.toNatChecked size)))))
      let memstatus : PhysMemRetStatus := tup__0
      let data : (BitVec 512) := (Sail.BitVec.castWidth tup__1)
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalReadAbort memstatus memaddrdesc size accdesc))
      else (pure (()))
      (pure (data)))


/-- Type quantifiers: size : Int -/
def AArch64_DataMemZero (regval : (BitVec 64)) (vaddress : (BitVec 64)) (accdesc_in : AccessDescriptor) (size : Int) : SailM Unit := do
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1677) ()) ) : SailM
    PhysMemRetStatus )
  let accdesc : AccessDescriptor := accdesc_in
  let w__1 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagaccess : Bool))) ) : SailM Bool )
  let accdesc ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_AllocationTagAccessIsEnabled accdesc.el) ) : SailM Bool )
        let accdesc := ({ accdesc with tagaccess := w__2 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let w__4 ← (( do
    (pure ((← do
          (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
  let accdesc ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (AArch64_AccessIsTagChecked vaddress accdesc) ) : SailM Bool )
        let accdesc := ({ accdesc with tagchecked := w__5 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let aligned : Bool := true
  let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      let w__6 ← (( do (IsDebugException memaddrdesc.fault) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          (AArch64_Abort vaddress memaddrdesc.fault))
      else
        (do
          (AArch64_Abort regval memaddrdesc.fault)))
  else (pure (()))
  let w__7 ← (( do (HaveTME ()) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      let w__9 ← (( do
        if ((accdesc.transactional : Bool) : Bool)
        then
          (do
            let w__8 ← (( do (MemHasTransactionalAccess memaddrdesc.memattrs) ) : SailM Bool )
            (pure (((! w__8) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          (FailTransaction TMFailure_IMP false))
      else (pure (())))
  else (pure (()))
  let (memaddrdesc, memstatus) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (size -i 1)
    (do
      let mut loop_vars := (memaddrdesc, memstatus)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (memaddrdesc, memstatus) := loop_vars
        loop_vars ← do
          let w__11 ← (( do
            (pure ((← do
                  (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailM Bool )
          if (w__11 : Bool)
          then
            (do
              let ptag : (BitVec 4) := (AArch64_PhysicalTag vaddress)
              let w__12 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailM Bool )
              if ((! w__12) : Bool)
              then
                (do
                  let w__13 ← (( do
                    (__IMPDEF_boolean "DC_ZVA tag fault reported with lowest faulting address") ) :
                    SailM Bool )
                  if (w__13 : Bool)
                  then
                    (do
                      (AArch64_TagCheckFault vaddress accdesc))
                  else
                    (do
                      (AArch64_TagCheckFault regval accdesc)))
              else (pure (())))
          else (pure (()))
          let w__14 ← (( do (PhysMemWrite memaddrdesc 1 accdesc none (Zeros (n := 8))) ) : SailM
            PhysMemRetStatus )
          let memstatus := (w__14 : PhysMemRetStatus)
          if ((IsFault__2 memstatus) : Bool)
          then
            (do
              (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc))
          else (pure (()))
          let memaddrdesc : AddressDescriptor :=
            { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt
                  memaddrdesc.paddress.address 1) } }
          (pure ((memaddrdesc, memstatus)))
      (pure loop_vars)) ) : SailM (AddressDescriptor × PhysMemRetStatus) )
  (pure (()))


/-- Type quantifiers: k_aligned : Bool, size : Nat, size > 0 -/
def MemSingleNF_read (address : (BitVec 64)) (size : Nat) (accdesc_in : AccessDescriptor) (aligned : Bool) : SailM ((BitVec (8 * size)) × Bool) := SailME.run do
  ArmFull.assert (BEq.beq accdesc_in.acctype AccessType_SVE) "sail-arm/v8_base.sail:29674.47-29674.48"
  ArmFull.assert (accdesc_in.nonfault || (accdesc_in.firstfault && (! accdesc_in.first))) "sail-arm/v8_base.sail:29675.83-29675.84"
  let value_name ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1713)
      (Sail.Int.toNatChecked ((8 *i size))))) ) : SailME ((BitVec (8 * size)) × Bool)
    (BitVec (8 * size)) )
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1714) ()) ) : SailME
    ((BitVec (8 * size)) × Bool) PhysMemRetStatus )
  let accdesc : AccessDescriptor := accdesc_in
  let fault ← (( do (NoFault__1 accdesc) ) : SailME ((BitVec (8 * size)) × Bool) FaultRecord )
  let w__0 ← (( do (ConstrainUnpredictableBool Unpredictable_NONFAULT) ) : SailME
    ((BitVec (8 * size)) × Bool) Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do
        ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits (Sail.Int.toNatChecked ((8 *i size))))) ) :
        SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
      (pure ((w__1, true))))
  else
    (do
      let w__3 ← (( do
        (pure ((← do
              (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailME
        ((BitVec (8 * size)) × Bool) Bool )
      let accdesc ← (( do
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do (AArch64_AccessIsTagChecked address accdesc) ) : SailME
              ((BitVec (8 * size)) × Bool) Bool )
            let accdesc := ({ accdesc with tagchecked := w__4 } : AccessDescriptor)
            (pure (accdesc)))
        else (pure (accdesc)) ) : SailME ((BitVec (8 * size)) × Bool) AccessDescriptor )
      let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailME
        ((BitVec (8 * size)) × Bool) AddressDescriptor )
      if ((BEq.beq memaddrdesc.memattrs.memtype MemType_Device) : Bool)
      then
        (do
          let w__5 ← (( do
            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits (Sail.Int.toNatChecked ((8 *i size))))) )
            : SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
          (pure ((w__5, true))))
      else
        (do
          if ((IsFault memaddrdesc) : Bool)
          then
            (do
              let w__6 ← (( do
                ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits (Sail.Int.toNatChecked ((8 *i size)))))
                ) : SailME ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
              (pure ((w__6, true))))
          else
            (do
              let w__8 ← (( do
                (pure ((← do
                      (HaveMTE2Ext ())) && (accdesc.tagchecked : Bool))) ) : SailME
                ((BitVec (8 * size)) × Bool) Bool )
              if (w__8 : Bool)
              then
                (do
                  let ptag : (BitVec 4) := (AArch64_PhysicalTag address)
                  let w__9 ← (( do (AArch64_CheckTag memaddrdesc accdesc ptag) ) : SailME
                    ((BitVec (8 * size)) × Bool) Bool )
                  if ((! w__9) : Bool)
                  then
                    (do
                      let w__10 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits
                          (Sail.Int.toNatChecked ((8 *i size))))) ) : SailME
                        ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
                      SailME.throw ((w__10, true) : ((BitVec (8 * size)) × Bool)))
                  else (pure (())))
              else (pure (()))
              let w__11 ← (( do
                ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead memaddrdesc
                  size accdesc none)) ) : SailME ((BitVec (8 * size)) × Bool)
                (PhysMemRetStatus × (BitVec (8 * size))) )
              let (tup__0, tup__1) := (w__11 : (PhysMemRetStatus × (BitVec (8 * size))))
              let memstatus : PhysMemRetStatus := tup__0
              let value_name : (BitVec (8 * size)) := tup__1
              if ((IsFault__2 memstatus) : Bool)
              then
                (do
                  let iswrite : Bool := false
                  let w__12 ← (( do
                    (IsExternalAbortTakenSynchronously memstatus iswrite memaddrdesc size accdesc) )
                    : SailME ((BitVec (8 * size)) × Bool) Bool )
                  if (w__12 : Bool)
                  then
                    (do
                      let w__13 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits
                          (Sail.Int.toNatChecked ((8 *i size))))) ) : SailME
                        ((BitVec (8 * size)) × Bool) (BitVec (8 * size)) )
                      SailME.throw ((w__13, true) : ((BitVec (8 * size)) × Bool)))
                  else
                    (let fault : FaultRecord := { fault with merrorstate := memstatus.merrorstate }
                    let fault : FaultRecord := { fault with extflag := memstatus.extflag }
                    let fault : FaultRecord := { fault with statuscode := memstatus.statuscode }
                    (pure ((PendSErrorInterrupt fault)))))
              else (pure (()))
              (pure ((value_name, false))))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareUN (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1718) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1719) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1720) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1721) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1722) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1723) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-arm/v8_base.sail:29873.41-29873.42"
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
  if (((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) : Bool)
  then
    (do
      (FPProcessException FPExc_InvalidOp fpcr))
  else (pure (()))
  let result : Bool :=
    (((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN)) || ((BEq.beq type2 FPType_SNaN) || (BEq.beq
          type2 FPType_QNaN)))
  if ((! result) : Bool)
  then
    (do
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr))
  else (pure (()))
  (pure (result))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPCompareNE (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM Bool := do
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1724) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1725) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1726) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1727) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1728) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1729) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-arm/v8_base.sail:29896.41-29896.42"
  let result ← (( do (undefined_bool_at (← occLabel 1730) ()) ) : SailM Bool )
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
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  if ((op1_nan || op2_nan) : Bool)
  then
    (do
      let result : Bool := true
      if (((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) : Bool)
      then
        (do
          (FPProcessException FPExc_InvalidOp fpcr))
      else (pure (()))
      (pure (result)))
  else
    (do
      let result : Bool := (bne value1_name value2_name)
      (FPProcessDenorms type1 type2 (Sail.BitVec.length op2) fpcr)
      (pure (result)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPLogB (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType (← occLabel 1747) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1748) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1749) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "sail-arm/v8_base.sail:31092.41-31092.42"
  let result ← (( do (undefined_int_at (← occLabel 1750) ()) ) : SailM Int )
  let w__0 ← (( do (FPUnpack op fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let result ← (( do
    if ((((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) || (BEq.beq fptype
           FPType_Zero)) : Bool)
    then
      (do
        (FPProcessException FPExc_InvalidOp fpcr)
        let result : Int := (Neg.neg (2 ^i ((Sail.BitVec.length op) -i 1)))
        (pure (result)))
    else
      (do
        if ((BEq.beq fptype FPType_Infinity) : Bool)
        then
          (let result : Int := ((2 ^i ((Sail.BitVec.length op) -i 1)) -i 1)
          (pure (result)))
        else
          (do
            let value_name : real := (abs_real value_name)
            let result : Int := 0
            let (result, value_name) ← (( do
              let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (result, value_name) => (pure (lt_real
                  value_name (1)))) (result, value_name)
                fun (result, value_name) => do
                  (pure (let value_name : real := (mult_real value_name (2))
                    let result : Int := (result -i 1)
                    (result, value_name) : (Int × real)))
              (pure loop_vars) ) : SailM (Int × real) )
            let (result, value_name) ← (( do
              let loop_vars_1 ← sailWhileFuelM (fuel := 1048576) (fun (result, value_name) => (pure (gteq_real
                  value_name (2)))) (result, value_name)
                fun (result, value_name) => do
                  (pure (let value_name : real := (div_real value_name (2))
                    let result : Int := (result +i 1)
                    (result, value_name) : (Int × real)))
              (pure loop_vars_1) ) : SailM (Int × real) )
            (FPProcessDenorm fptype (Sail.BitVec.length op) fpcr)
            (pure (result)))) ) : SailM Int )
  let result : Int := result
  (pure ((Sail.BitVec.castWidth (integer_subrange result ((Sail.BitVec.length op) -i 1) 0))))


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPConvertBF (op : (BitVec k_N)) (fpcr_in : (BitVec 64)) (rounding_in : FPRounding) : SailM (BitVec (k_N / 2)) := do
  let fptype ← (( do (undefined_FPType (← occLabel 1795) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1796) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1797) ()) ) : SailM real )
  ArmFull.assert ((Sail.BitVec.length op) == 32) "sail-arm/v8_base.sail:32225.19-32225.20"
  let halfsize : Nat := (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length op) 2)))
  let fpcr : FPCRType := fpcr_in
  let rounding : FPRounding := rounding_in
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1798)
      (Sail.BitVec.length op))) ) : SailM (BitVec k_N) )
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let fpexc : Bool := (! altfp)
  let fpcr : (BitVec 64) :=
    if (altfp : Bool)
    then
      (let fpcr : FPCRType :=
        (Sail.BitVec.updateSubrange fpcr 0 0 (Sail.BitVec.extractLsb 0b11#2 1 1))
      (Sail.BitVec.updateSubrange fpcr 24 24 (Sail.BitVec.extractLsb 0b11#2 0 0)))
    else fpcr
  let rounding : FPRounding :=
    if (altfp : Bool)
    then FPRounding_TIEEVEN
    else rounding
  let w__3 ← (( do (FPUnpack__1 op fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__3 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let result ← (( do
    if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
    then
      (do
        let result ← (( do
          if (((_get_FPCRType_DN fpcr) == 1#1) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))))
          else
            (do
              ((Sail.BitVec.castWidth ) <$> (FPConvertNaN op (Sail.BitVec.length result)))) ) :
          SailM (BitVec k_N) )
        if ((BEq.beq fptype FPType_SNaN) : Bool)
        then
          (do
            if (fpexc : Bool)
            then
              (do
                (FPProcessException FPExc_InvalidOp fpcr))
            else (pure (())))
        else (pure (()))
        (pure (result)))
    else
      (do
        if ((BEq.beq fptype FPType_Infinity) : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (FPInfinity sign (Sail.BitVec.length result))))
        else
          (do
            if ((BEq.beq fptype FPType_Zero) : Bool)
            then
              (do
                ((Sail.BitVec.castWidth ) <$> (FPZero sign (Sail.BitVec.length result))))
            else
              (do
                ((Sail.BitVec.castWidth ) <$> (FPRoundBF value_name fpcr rounding fpexc
                  (Sail.BitVec.length result)))))) ) : SailM (BitVec k_N) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
      (Sail.Int.toNatChecked (((2 *i halfsize) -i 1))) halfsize))))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 16 -/
def BFAdd__1 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool_at (← occLabel 1829) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1830) ()) ) : SailM Bool )
  let result_sign ← (( do (undefined_bitvector_at (← occLabel 1831) 1) ) : SailM (BitVec 1) )
  let result_value ← (( do (undefined_real_at (← occLabel 1832) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1833) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1834) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1835) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1836) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1837) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1838) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1839) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1840) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length op2) == 16) "sail-arm/v8_base.sail:32512.19-32512.20"
  let rounding ← (( do (FPRoundingMode fpcr) ) : SailM FPRounding )
  let done ← (( do (undefined_bool_at (← occLabel 1841) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1842)
      (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM (BitVec (2 * k_N)) )
  let op1_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op1 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let op2_s : (BitVec (2 * k_N)) :=
    (Sail.BitVec.castWidth (op2 +++ (Zeros (n := (Sail.BitVec.length op2)))))
  let w__0 ← (( do (FPUnpack__1 op1_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack__1 op2_s fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs__1 type1 type2 op1_s op2_s fpcr fpexc) ) : SailM
    (Bool × (BitVec (2 * k_N))) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec (2 * k_N))))
  let done : Bool := tup__0
  let result : (BitVec (2 * k_N)) := tup__1
  let result ← (( do
    if ((! done) : Bool)
    then
      (do
        let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
        let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
        let zero1 : Bool := (BEq.beq type1 FPType_Zero)
        let zero2 : Bool := (BEq.beq type2 FPType_Zero)
        let result ← (( do
          if (((inf1 && inf2) && (sign1 == (Complement.complement sign2))) : Bool)
          then
            (do
              let w__3 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr
                  (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM
                (BitVec (2 * k_N)) )
              let result := (w__3 : (BitVec (2 * k_N)))
              if (fpexc : Bool)
              then
                (do
                  (FPProcessException FPExc_InvalidOp fpcr))
              else (pure (()))
              (pure (result)))
          else
            (do
              if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 0#1))) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1
                    (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
              else
                (do
                  if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 1#1))) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1
                        (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
                  else
                    (do
                      if (((zero1 && zero2) && (sign1 == sign2)) : Bool)
                      then
                        (do
                          ((Sail.BitVec.castWidth ) <$> (FPZero sign1
                            (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
                      else
                        (do
                          let result_value : real := (add_real value1_name value2_name)
                          if ((eq_real result_value (0)) : Bool)
                          then
                            (do
                              let result_sign : (BitVec 1) :=
                                if ((BEq.beq rounding FPRounding_NEGINF) : Bool)
                                then 1#1
                                else 0#1
                              ((Sail.BitVec.castWidth ) <$> (FPZero result_sign
                                (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
                          else
                            (do
                              ((Sail.BitVec.castWidth ) <$> (FPRoundBF result_value fpcr rounding
                                fpexc (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))))))
          ) : SailM (BitVec (2 * k_N)) )
        if (fpexc : Bool)
        then
          (do
            (FPProcessDenorms type1 type2 (2 *i (Sail.BitVec.length op2)) fpcr))
        else (pure (()))
        (pure (result)))
    else (pure (result)) ) : SailM (BitVec (2 * k_N)) )
  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb result
      (Sail.Int.toNatChecked (((2 *i (Sail.BitVec.length op2)) -i 1))) (Sail.BitVec.length op2)))))


end ArmFull.Functions
