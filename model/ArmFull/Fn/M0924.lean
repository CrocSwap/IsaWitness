import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0041
import ArmFull.Fn.M0044
import ArmFull.Fn.M0045
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0051
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0114
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0168
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0185
import ArmFull.Fn.M0186
import ArmFull.Fn.M0204
import ArmFull.Fn.M0216
import ArmFull.Fn.M0217
import ArmFull.Fn.M0237
import ArmFull.Fn.M0246
import ArmFull.Fn.M0255
import ArmFull.Fn.M0851
import ArmFull.Fn.M0852

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

def AArch64_AllocationTagCheck (memaddrdesc : AddressDescriptor) (accdesc : AccessDescriptor) (ptag : (BitVec 4)) : SailM Bool := do
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1356) ()) ) : SailM
    PhysMemRetStatus )
  let readtag ← (( do (undefined_bitvector_at (← occLabel 1357) 4) ) : SailM (BitVec 4) )
  if ((BEq.beq memaddrdesc.memattrs.tags MemTag_AllocationTagged) : Bool)
  then
    (do
      let w__0 ← (( do (PhysMemTagRead memaddrdesc accdesc) ) : SailM
        (PhysMemRetStatus × (BitVec 4)) )
      let (tup__0, tup__1) := (w__0 : (PhysMemRetStatus × (BitVec 4)))
      let memstatus : PhysMemRetStatus := tup__0
      let readtag : (BitVec 4) := tup__1
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalReadAbort memstatus memaddrdesc 1 accdesc))
      else (pure (()))
      (pure ((ptag == readtag))))
  else (pure (true))


def AArch64_MemTag_read (address : (BitVec 64)) (accdesc_in : AccessDescriptor) : SailM (BitVec 4) := do
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1665) ()) ) : SailM
    PhysMemRetStatus )
  let tag ← (( do (undefined_bitvector_at (← occLabel 1666) 4) ) : SailM (BitVec 4) )
  ArmFull.assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "sail-arm/v8_base.sail:28695.65-28695.66"
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := true
  let w__0 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  let accdesc ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (AArch64_AllocationTagAccessIsEnabled accdesc.el) ) : SailM Bool )
        let accdesc := ({ accdesc with tagaccess := w__1 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned TAG_GRANULE) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault))
  else (pure (()))
  if ((accdesc.tagaccess && (BEq.beq memaddrdesc.memattrs.tags MemTag_AllocationTagged)) : Bool)
  then
    (do
      let w__2 ← (( do (PhysMemTagRead memaddrdesc accdesc) ) : SailM
        (PhysMemRetStatus × (BitVec 4)) )
      let (tup__0, tup__1) := (w__2 : (PhysMemRetStatus × (BitVec 4)))
      let memstatus : PhysMemRetStatus := tup__0
      let tag : (BitVec 4) := tup__1
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalReadAbort memstatus memaddrdesc 1 accdesc))
      else (pure (()))
      (pure (tag)))
  else
    (do
      let w__5 ← (( do
        (pure ((← do
              (pure ((← do
                    (HaveMTECanonicalTagCheckingExt ())) && (accdesc.tagaccess : Bool)))) && ((BEq.beq
              memaddrdesc.memattrs.tags MemTag_CanonicallyTagged) : Bool))) ) : SailM Bool )
      let w__6 : (BitVec 4) :=
        if (w__5 : Bool)
        then
          (if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access address 55)])) == 0#1) : Bool)
          then 0b0000#4
          else 0b1111#4)
        else 0b0000#4
      (pure (w__6)))


def AArch64_MemTag_set (address : (BitVec 64)) (accdesc_in : AccessDescriptor) (value_name : (BitVec 4)) : SailM Unit := do
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1668) ()) ) : SailM
    PhysMemRetStatus )
  ArmFull.assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "sail-arm/v8_base.sail:28724.65-28724.66"
  let accdesc : AccessDescriptor := accdesc_in
  let aligned : Bool := (IsAligned__1 address TAG_GRANULE)
  if ((! aligned) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort address w__0))
  else (pure (()))
  let w__1 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  let accdesc ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_AllocationTagAccessIsEnabled accdesc.el) ) : SailM Bool )
        let accdesc := ({ accdesc with tagaccess := w__2 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned TAG_GRANULE) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      (AArch64_Abort address memaddrdesc.fault))
  else (pure (()))
  if ((accdesc.tagaccess && (BEq.beq memaddrdesc.memattrs.tags MemTag_AllocationTagged)) : Bool)
  then
    (do
      let memstatus ← (( do (PhysMemTagWrite memaddrdesc accdesc value_name) ) : SailM
        PhysMemRetStatus )
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: size : Int -/
def AArch64_TagMemZero (regval : (BitVec 64)) (vaddress : (BitVec 64)) (accdesc_in : AccessDescriptor) (size : Int) : SailM Unit := do
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1678) ()) ) : SailM
    PhysMemRetStatus )
  ArmFull.assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "sail-arm/v8_base.sail:29013.65-29013.66"
  let accdesc : AccessDescriptor := accdesc_in
  let count : Int := (Int.shiftr size LOG2_TAG_GRANULE)
  let tag : (BitVec 4) := (AArch64_AllocationTagFromAddress vaddress)
  let aligned : Bool := (IsAligned__1 vaddress TAG_GRANULE)
  if ((! aligned) : Bool)
  then
    (do
      let w__0 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort vaddress w__0))
  else (pure (()))
  let w__1 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  let accdesc ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_AllocationTagAccessIsEnabled accdesc.el) ) : SailM Bool )
        let accdesc := ({ accdesc with tagaccess := w__2 } : AccessDescriptor)
        (pure (accdesc)))
    else (pure (accdesc)) ) : SailM AccessDescriptor )
  let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault memaddrdesc) : Bool)
  then
    (do
      let w__3 ← (( do (IsDebugException memaddrdesc.fault) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (AArch64_Abort vaddress memaddrdesc.fault))
      else
        (do
          (AArch64_Abort regval memaddrdesc.fault)))
  else (pure (()))
  if (((! accdesc.tagaccess) || (bne memaddrdesc.memattrs.tags MemTag_AllocationTagged)) : Bool)
  then (pure (()))
  else
    (do
      let (memaddrdesc, memstatus) ← (( do
        let loop_i_lower : Nat := 0
        let loop_i_upper : Int := (count -i 1)
        (do
          let mut loop_vars := (memaddrdesc, memstatus)
          for i in [loop_i_lower:loop_i_upper:1]i do
            let (memaddrdesc, memstatus) := loop_vars
            loop_vars ← do
              let w__4 ← (( do (PhysMemTagWrite memaddrdesc accdesc tag) ) : SailM
                PhysMemRetStatus )
              let memstatus := (w__4 : PhysMemRetStatus)
              if ((IsFault__2 memstatus) : Bool)
              then
                (do
                  (HandleExternalWriteAbort memstatus memaddrdesc 1 accdesc))
              else (pure (()))
              let memaddrdesc : AddressDescriptor :=
                { memaddrdesc with paddress := { memaddrdesc.paddress with address := (BitVec.addInt
                      memaddrdesc.paddress.address TAG_GRANULE) } }
              (pure ((memaddrdesc, memstatus)))
          (pure loop_vars)) ) : SailM (AddressDescriptor × PhysMemRetStatus) )
      (pure (())))


/-- Type quantifiers: size : Int -/
def AArch64_SetExclusiveMonitors (address : (BitVec 64)) (size : Int) : SailM Unit := do
  writeReg __ExclusiveMonitorSet true
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_LOAD acqrel tagchecked) ) : SailM
    AccessDescriptor )
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
  let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM
    AddressDescriptor )
  (pure (if ((IsFault memaddrdesc) : Bool)
    then ()
    else
      (let _ : Unit :=
        if ((bne memaddrdesc.memattrs.shareability Shareability_NSH) : Bool)
        then (MarkExclusiveGlobal memaddrdesc.paddress (ProcessorID ()) size)
        else ()
      let _ : Unit := (MarkExclusiveLocal memaddrdesc.paddress (ProcessorID ()) size)
      (AArch64_MarkExclusiveVA address (ProcessorID ()) size))))


/-- Type quantifiers: size : Int -/
def AArch64_ExclusiveMonitorsPass (address : (BitVec 64)) (size : Int) : SailM Bool := do
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_STORE acqrel tagchecked) ) : SailM
    AccessDescriptor )
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
  if ((! (AArch64_IsExclusiveVA address (ProcessorID ()) size)) : Bool)
  then (pure (false))
  else
    (do
      let memaddrdesc ← (( do (AArch64_TranslateAddress address accdesc aligned size) ) : SailM
        AddressDescriptor )
      if ((IsFault memaddrdesc) : Bool)
      then
        (do
          (AArch64_Abort address memaddrdesc.fault))
      else (pure (()))
      let passed ← (( do (IsExclusiveLocal memaddrdesc.paddress (ProcessorID ()) size) ) : SailM
        Bool )
      let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
      if ((passed && (bne memaddrdesc.memattrs.shareability Shareability_NSH)) : Bool)
      then
        (do
          (IsExclusiveGlobal memaddrdesc.paddress (ProcessorID ()) size))
      else (pure (passed)))


/-- Type quantifiers: N : Nat, k_fpexc : Bool, N = 32 -/
def FPRoundBF (op : real) (fpcr : (BitVec 64)) (rounding : FPRounding) (fpexc : Bool) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert (N == 32) "sail-arm/v8_base.sail:32210.18-32210.19"
  let isbfloat16 : Bool := true
  ((Sail.BitVec.castWidth ) <$> (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 32 -/
def FPProcessNaNs4 (type1 : FPType) (type2 : FPType) (type3 : FPType) (type4 : FPType) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (op3 : (BitVec (k_N / 2))) (op4 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  ArmFull.assert (SPEMaxCounters == 32) "sail-arm/v8_base.sail:32270.19-32270.20"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1799)
      (Sail.Int.toNatChecked (SPEMaxCounters)))) ) : SailM (BitVec k_N) )
  let done ← (( do (undefined_bool_at (← occLabel 1800) ()) ) : SailM Bool )
  if ((BEq.beq type1 FPType_SNaN) : Bool)
  then
    (do
      let done : Bool := true
      let w__0 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec (k_N / 2)) )
      let w__1 ← (( do
        ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__0 (Sail.BitVec.length result))) ) : SailM
        (BitVec k_N) )
      let result := (w__1 : (BitVec k_N))
      (pure ((done, result))))
  else
    (do
      if ((BEq.beq type2 FPType_SNaN) : Bool)
      then
        (do
          let done : Bool := true
          let w__2 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM (BitVec (k_N / 2)) )
          let w__3 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__2 (Sail.BitVec.length result))) ) : SailM
            (BitVec k_N) )
          let result := (w__3 : (BitVec k_N))
          (pure ((done, result))))
      else
        (do
          if ((BEq.beq type3 FPType_SNaN) : Bool)
          then
            (do
              let done : Bool := true
              let w__4 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) : SailM (BitVec (k_N / 2))
                )
              let w__5 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__4 (Sail.BitVec.length result))) ) :
                SailM (BitVec k_N) )
              let result := (w__5 : (BitVec k_N))
              (pure ((done, result))))
          else
            (do
              if ((BEq.beq type4 FPType_SNaN) : Bool)
              then
                (do
                  let done : Bool := true
                  let w__6 ← (( do (FPProcessNaN__1 type4 op4 fpcr fpexc) ) : SailM
                    (BitVec (k_N / 2)) )
                  let w__7 ← (( do
                    ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__6 (Sail.BitVec.length result))) )
                    : SailM (BitVec k_N) )
                  let result := (w__7 : (BitVec k_N))
                  (pure ((done, result))))
              else
                (do
                  if ((BEq.beq type1 FPType_QNaN) : Bool)
                  then
                    (do
                      let done : Bool := true
                      let w__8 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM
                        (BitVec (k_N / 2)) )
                      let w__9 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__8 (Sail.BitVec.length result)))
                        ) : SailM (BitVec k_N) )
                      let result := (w__9 : (BitVec k_N))
                      (pure ((done, result))))
                  else
                    (do
                      if ((BEq.beq type2 FPType_QNaN) : Bool)
                      then
                        (do
                          let done : Bool := true
                          let w__10 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM
                            (BitVec (k_N / 2)) )
                          let w__11 ← (( do
                            ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__10
                              (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                          let result := (w__11 : (BitVec k_N))
                          (pure ((done, result))))
                      else
                        (do
                          if ((BEq.beq type3 FPType_QNaN) : Bool)
                          then
                            (do
                              let done : Bool := true
                              let w__12 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) : SailM
                                (BitVec (k_N / 2)) )
                              let w__13 ← (( do
                                ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__12
                                  (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                              let result := (w__13 : (BitVec k_N))
                              (pure ((done, result))))
                          else
                            (do
                              if ((BEq.beq type4 FPType_QNaN) : Bool)
                              then
                                (do
                                  let done : Bool := true
                                  let w__14 ← (( do (FPProcessNaN__1 type4 op4 fpcr fpexc) ) :
                                    SailM (BitVec (k_N / 2)) )
                                  let w__15 ← (( do
                                    ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__14
                                      (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                                  let result := (w__15 : (BitVec k_N))
                                  (pure ((done, result))))
                              else
                                (let done : Bool := false
                                let result : (BitVec k_N) :=
                                  (Sail.BitVec.castWidth (Zeros (n := (Sail.BitVec.length result))))
                                (pure ((done, result)))))))))))


/-- Type quantifiers: k_N : Nat, k_honor_altfp : Bool, k_N = 16 -/
def BFNeg__1 (op : (BitVec k_N)) (honor_altfp : Bool) : SailM (BitVec k_N) := SailME.run do
  let fptype ← (( do (undefined_FPType (← occLabel 1828) ()) ) : SailME (BitVec k_N) FPType )
  ArmFull.assert ((Sail.BitVec.length op) == 16) "sail-arm/v8_base.sail:32449.19-32449.20"
  let w__3 ← (( do
    if ((← do
         if ((honor_altfp : Bool) : Bool)
         then
           (do
             let w__0 ← (( do (UsingAArch32 ()) ) : SailME (BitVec k_N) Bool )
             (pure (((! w__0) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (HaveAltFP ()))
    else (pure false) ) : SailME (BitVec k_N) Bool )
  if (w__3 : Bool)
  then
    (do
      let fpcr ← (( do (FPCR_read ()) ) : SailME (BitVec k_N) FPCRType )
      if (((_get_FPCRType_AH fpcr) == 1#1) : Bool)
      then
        (do
          let fpexc : Bool := false
          let isbfloat16 : Bool := true
          let (__tup_0, _, _) ← (( do (FPUnpackBase__1 op fpcr fpexc isbfloat16) ) : SailME
            (BitVec k_N) (FPType × (BitVec 1) × real) )
          let fptype : FPType := __tup_0
          if (((BEq.beq fptype FPType_SNaN) || (BEq.beq fptype FPType_QNaN)) : Bool)
          then
            (do
              SailME.throw (op : (BitVec k_N)))
          else (pure (())))
      else (pure (())))
  else (pure (()))
  (pure ((Sail.BitVec.castWidth ((Complement.complement
        (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op
            (Sail.Int.toNatChecked (((Sail.BitVec.length op) -i 1))))]))) +++ (Sail.BitVec.extractLsb
        op (Sail.Int.toNatChecked (((Sail.BitVec.length op) -i 2))) 0)))))


/-- Type quantifiers: k_aligned : Bool -/
def DebugMemWrite (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) (aligned : Bool) (data : (BitVec 8)) : SailM (PhysMemRetStatus × AddressDescriptor) := do
  let memstatus ← (( do (__UNKNOWN_PhysMemRetStatus ()) ) : SailM PhysMemRetStatus )
  let size : Nat := 1
  let addrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) : SailM
    AddressDescriptor )
  if ((IsFault addrdesc) : Bool)
  then (pure ((memstatus, addrdesc)))
  else
    (do
      let memstatus ← (( do (PhysMemWrite addrdesc 1 accdesc none data) ) : SailM PhysMemRetStatus
        )
      (pure ((memstatus, addrdesc))))


def AArch64_DC (regval : (BitVec 64)) (cachetype : CacheType) (cacheop : CacheOp) (opscope_in : CacheOpScope) : SailM Unit := do
  let ss ← (( do (undefined_SecurityState (← occLabel 2487) ()) ) : SailM SecurityState )
  let opscope : CacheOpScope := opscope_in
  let cache ← (( do (undefined_CacheRecord (← occLabel 2488) ()) ) : SailM CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_DC }
  let cache : CacheRecord := { cache with cachetype := cachetype }
  let cache : CacheRecord := { cache with cacheop := cacheop }
  let cache : CacheRecord := { cache with opscope := opscope }
  if ((BEq.beq opscope CacheOpScope_SetWay) : Bool)
  then
    (do
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      let ss ← (( do (SecurityStateAtEL w__0.EL) ) : SailM SecurityState )
      let cache : CacheRecord := { cache with cpas := (CPASAtSecurityState ss) }
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let w__1 ← (( do (DecodeSW regval cachetype) ) : SailM (Int × Int × Int) )
      let (tup__0, tup__1, tup__2) := (w__1 : (Int × Int × Int))
      let cache : CacheRecord := { cache with setnum := tup__0 }
      let cache : CacheRecord := { cache with waynum := tup__1 }
      let cache : CacheRecord := { cache with level := tup__2 }
      let w__10 ← (( do
        if ((← do
             if ((← do
                  if (((BEq.beq cacheop CacheOp_Invalidate) : Bool) : Bool)
                  then
                    (do
                      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__2.EL == EL1) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            if ((← do
                 let w__6 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_SWIO w__6) == 1#1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure (((((_get_HCR_EL2_Type_DC w__7) +++ (_get_HCR_EL2_Type_VM w__8)) != 0b00#2) : Bool)))))
        else (pure false) ) : SailM Bool )
      let cache : CacheRecord :=
        if (w__10 : Bool)
        then { cache with cacheop := CacheOp_CleanInvalidate }
        else cache
      (CACHE_OP cache))
  else
    (do
      let w__13 ← (( do
        if ((← do
             (EL2Enabled ())) : Bool)
        then
          (do
            let w__12 ← (( do (IsInHost ()) ) : SailM Bool )
            (pure (((! w__12) : Bool))))
        else (pure false) ) : SailM Bool )
      let cache ← (( do
        if (w__13 : Bool)
        then
          (do
            let w__16 ← (( do
              if ((← do
                   let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
                   (pure (((w__14.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__15.EL == EL1) : Bool)))) ) : SailM Bool )
            if (w__16 : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                let w__17 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                let cache := ({ cache with vmid := w__17 } : CacheRecord)
                (pure (cache)))
            else
              (let cache : CacheRecord := { cache with is_vmid_valid := false }
              (pure (cache))))
        else
          (let cache : CacheRecord := { cache with is_vmid_valid := false }
          (pure (cache))) ) : SailM CacheRecord )
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      let cache ← (( do
        if ((w__18.EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            let w__19 ← (( do (ASID_read ()) ) : SailM (BitVec 16) )
            let cache := ({ cache with asid := w__19 } : CacheRecord)
            (pure (cache)))
        else
          (let cache : CacheRecord := { cache with is_asid_valid := false }
          (pure (cache))) ) : SailM CacheRecord )
      let w__21 ← (( do
        if (((BEq.beq opscope CacheOpScope_PoDP) : Bool) : Bool)
        then
          (do
            (__IMPDEF_boolean "Memory system does not supports PoDP"))
        else (pure false) ) : SailM Bool )
      let opscope : CacheOpScope :=
        if (w__21 : Bool)
        then CacheOpScope_PoP
        else opscope
      let w__23 ← (( do
        if (((BEq.beq opscope CacheOpScope_PoP) : Bool) : Bool)
        then
          (do
            (__IMPDEF_boolean "Memory system does not supports PoP"))
        else (pure false) ) : SailM Bool )
      let opscope : CacheOpScope :=
        if (w__23 : Bool)
        then CacheOpScope_PoC
        else opscope
      let vaddress : (BitVec 64) := regval
      let size : Int := 0
      let (size, vaddress) ← (( do
        if ((BEq.beq cacheop CacheOp_Invalidate) : Bool)
        then
          (do
            let w__24 ← (( do (__IMPDEF_integer "Data Cache Invalidate Watchpoint Size") ) : SailM
              Int )
            let size : Int := (w__24 : Int)
            let w__26 ← (( do
              (pure ((← do
                    let w__25 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
                    (pure (((size ≥b (4 *i (2 ^i (BitVec.toNat (_get_CTR_EL0_Type_DminLine w__25))))) : Bool)))) && ((size ≤b 2048) : Bool)))
              ) : SailM Bool )
            ArmFull.assert w__26 "sail-arm/v8_base.sail:36651.71-36651.72"
            ArmFull.assert ((BitVec.toNat
                ((Sail.BitVec.castWidth (m := 33) (integer_subrange size 32 0)) &&& (Sail.BitVec.castWidth (m := 33) (integer_subrange
                    (size -i 1) 32 0)))) == 0) "sail-arm/v8_base.sail:36652.61-36652.62"
            let vaddress : (BitVec 64) := (Align_bits regval size)
            (pure ((size, vaddress))))
        else (pure ((size, vaddress))) ) : SailM (Int × (BitVec 64)) )
      let size : Int := size
      let w__27 ← (( do (DCInstNeedsTranslation opscope) ) : SailM Bool )
      let cache ← (( do
        if (w__27 : Bool)
        then
          (do
            let cache : CacheRecord := { cache with vaddress := vaddress }
            let aligned : Bool := true
            let accdesc ← (( do (CreateAccDescDC cache) ) : SailM AccessDescriptor )
            let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) :
              SailM AddressDescriptor )
            if ((IsFault memaddrdesc) : Bool)
            then
              (do
                (AArch64_Abort regval memaddrdesc.fault))
            else (pure (()))
            let cache : CacheRecord := { cache with translated := true }
            let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
            let cache : CacheRecord :=
              { cache with cpas := (CPASAtPAS memaddrdesc.paddress.paspace) }
            let cache : CacheRecord :=
              if (((BEq.beq opscope CacheOpScope_PoC) || ((BEq.beq opscope CacheOpScope_PoP) || (BEq.beq
                       opscope CacheOpScope_PoDP))) : Bool)
              then { cache with shareability := memaddrdesc.memattrs.shareability }
              else { cache with shareability := Shareability_NSH }
            (pure (cache)))
        else
          (do
            if ((BEq.beq opscope CacheOpScope_PoE) : Bool)
            then
              (do
                let cache : CacheRecord := { cache with translated := true }
                let cache : CacheRecord := { cache with shareability := Shareability_OSH }
                let cache : CacheRecord :=
                  { cache with paddress := { cache.paddress with address := (Sail.BitVec.extractLsb
                        regval 55 0) } }
                let w__28 ← (( do
                  (DecodePASpace (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access regval 62)]))
                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access regval 63)]))) ) : SailM
                  PASpace )
                let cache :=
                  ({ cache with paddress := { cache.paddress with paspace := w__28 } } : CacheRecord)
                let cache : CacheRecord := { cache with cpas := (CPASAtPAS cache.paddress.paspace) }
                if ((bne cache.paddress.paspace PAS_Realm) : Bool)
                then
                  (do
                    (EndOfInstruction ()))
                else (pure (()))
                let w__29 ← (( do (__IMPDEF_boolean "Apply granule protection check on DC to PoE")
                  ) : SailM Bool )
                if (w__29 : Bool)
                then
                  (do
                    let memaddrdesc ← (( do (undefined_AddressDescriptor (← occLabel 2489) ()) )
                      : SailM AddressDescriptor )
                    let accdesc ← (( do (CreateAccDescDC cache) ) : SailM AccessDescriptor )
                    let memaddrdesc : AddressDescriptor :=
                      { memaddrdesc with paddress := cache.paddress }
                    let w__30 ← (( do (GranuleProtectionCheck memaddrdesc accdesc) ) : SailM
                      GPCFRecord )
                    let memaddrdesc :=
                      ({ memaddrdesc with fault := { memaddrdesc.fault with gpcf := w__30 } } : AddressDescriptor)
                    if ((bne memaddrdesc.fault.gpcf.gpf GPCF_None) : Bool)
                    then
                      (do
                        let memaddrdesc : AddressDescriptor :=
                          { memaddrdesc with fault := { memaddrdesc.fault with statuscode := Fault_GPCFOnOutput } }
                        let memaddrdesc : AddressDescriptor :=
                          { memaddrdesc with fault := { memaddrdesc.fault with paddress := memaddrdesc.paddress } }
                        let w__31 ← (( do (__UNKNOWN_bits 64) ) : SailM (BitVec 64) )
                        (AArch64_Abort w__31 memaddrdesc.fault))
                    else (pure (())))
                else (pure (()))
                (pure (cache)))
            else
              (do
                if ((BEq.beq opscope CacheOpScope_PoPA) : Bool)
                then
                  (do
                    let cache : CacheRecord := { cache with translated := true }
                    let cache : CacheRecord := { cache with shareability := Shareability_OSH }
                    let cache : CacheRecord :=
                      { cache with paddress := { cache.paddress with address := (Sail.BitVec.extractLsb
                            regval 55 0) } }
                    let w__32 ← (( do
                      (DecodePASpace (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access regval 62)]))
                        (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access regval 63)]))) ) : SailM
                      PASpace )
                    let cache :=
                      ({ cache with paddress := { cache.paddress with paspace := w__32 } } : CacheRecord)
                    let cache : CacheRecord :=
                      { cache with cpas := (CPASAtPAS cache.paddress.paspace) }
                    (pure (cache)))
                else
                  (do
                    let cache : CacheRecord := { cache with vaddress := vaddress }
                    let cache : CacheRecord := { cache with translated := false }
                    let w__33 ← (( do (__UNKNOWN_Shareability ()) ) : SailM Shareability )
                    let cache := ({ cache with shareability := w__33 } : CacheRecord)
                    let w__34 ← (( do (__UNKNOWN_FullAddress ()) ) : SailM FullAddress )
                    let cache := ({ cache with paddress := w__34 } : CacheRecord)
                    (pure (cache))))) ) : SailM CacheRecord )
      let w__41 ← (( do
        if ((← do
             if ((← do
                  if (((BEq.beq cacheop CacheOp_Invalidate) : Bool) : Bool)
                  then
                    (do
                      let w__35 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure (((w__35.EL == EL1) : Bool))))
                  else (pure false)) : Bool)
             then
               (do
                 (EL2Enabled ()))
             else (pure false)) : Bool)
        then
          (do
            let w__39 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            let w__40 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure (((((_get_HCR_EL2_Type_DC w__39) +++ (_get_HCR_EL2_Type_VM w__40)) != 0b00#2) : Bool))))
        else (pure false) ) : SailM Bool )
      let cache : CacheRecord :=
        if (w__41 : Bool)
        then { cache with cacheop := CacheOp_CleanInvalidate }
        else cache
      let w__43 ← (( do
        if (((cache.translated && (BEq.beq cache.cpas CPAS_Secure)) : Bool) : Bool)
        then
          (do
            let w__42 ← (( do (HaveSecureState ()) ) : SailM Bool )
            (pure (((! w__42) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__43 : Bool)
      then (pure (()))
      else
        (do
          (CACHE_OP cache)))


end ArmFull.Functions
