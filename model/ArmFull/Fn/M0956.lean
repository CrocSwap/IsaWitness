module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0216
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0881
public import ArmFull.Fn.M0882 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: N : Nat, k_fpexc : Bool, List.elem N [16, 32, 64] -/
def FPRound__2 (op : real) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (fpexc : Bool) (N : Nat) : SailM (BitVec N) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 26 26 0#1)
  let isbfloat16 : Bool := false
  ((Sail.BitVec.castWidth ) <$> (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPUnpackBase (fpval : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (FPType × (BitVec 1) × real) := do
  let fp_type ← (( do (undefined_FPType (← occLabel 909) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 910) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 911) ()) ) : SailM real )
  let isbfloat16 : Bool := false
  let w__0 ← (( do (FPUnpackBase__1 fpval fpcr fpexc isbfloat16) ) : SailM
    (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fp_type : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  (pure ((fp_type, sign, value_name)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPProcessNaN (fptype : FPType) (op : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fpexc : Bool := true
  (FPProcessNaN__1 fptype op fpcr fpexc)


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPProcessNaNs__1 (type1 : FPType) (type2 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-inputs/03-v8_base.sail:16219.41-16219.42"
  let done ← (( do (undefined_bool_at (← occLabel 919) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 920)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let any_snan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN))
  let type_nan : FPType :=
    if (any_snan : Bool)
    then FPType_SNaN
    else FPType_QNaN
  if (((altfp && op1_nan) && op2_nan) : Bool)
  then
    (do
      let done : Bool := true
      let w__3 ← (( do (FPProcessNaN__1 type_nan op1 fpcr fpexc) ) : SailM (BitVec k_N) )
      let result := (w__3 : (BitVec k_N))
      (pure ((done, result))))
  else
    (do
      if ((BEq.beq type1 FPType_SNaN) : Bool)
      then
        (do
          let done : Bool := true
          let w__4 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec k_N) )
          let result := (w__4 : (BitVec k_N))
          (pure ((done, result))))
      else
        (do
          if ((BEq.beq type2 FPType_SNaN) : Bool)
          then
            (do
              let done : Bool := true
              let w__5 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM (BitVec k_N) )
              let result := (w__5 : (BitVec k_N))
              (pure ((done, result))))
          else
            (do
              if ((BEq.beq type1 FPType_QNaN) : Bool)
              then
                (do
                  let done : Bool := true
                  let w__6 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec k_N) )
                  let result := (w__6 : (BitVec k_N))
                  (pure ((done, result))))
              else
                (do
                  if ((BEq.beq type2 FPType_QNaN) : Bool)
                  then
                    (do
                      let done : Bool := true
                      let w__7 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM
                        (BitVec k_N) )
                      let result := (w__7 : (BitVec k_N))
                      (pure ((done, result))))
                  else
                    (let done : Bool := false
                    let result : (BitVec k_N) :=
                      (Sail.BitVec.castWidth (Zeros (n := (Sail.BitVec.length result))))
                    (pure ((done, result))))))))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPRoundCV (op : real) (fpcr_in : (BitVec 64)) (rounding : FPRounding) (N : Nat) : SailM (BitVec N) := do
  let fpcr : FPCRType := fpcr_in
  let fpcr : FPCRType := (Sail.BitVec.updateSubrange fpcr 19 19 0#1)
  let fpexc : Bool := true
  let isbfloat16 : Bool := false
  ((Sail.BitVec.castWidth ) <$> (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [16, 32, 64] -/
def FPProcessNaNs3__1 (type1 : FPType) (type2 : FPType) (type3 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (op3 : (BitVec k_N)) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  ArmFull.assert (((Sail.BitVec.length op3) == 16) || (((Sail.BitVec.length op3) == 32) || ((Sail.BitVec.length
          op3) == 64))) "sail-inputs/03-v8_base.sail:16877.41-16877.42"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1025)
      (Sail.BitVec.length op3))) ) : SailM (BitVec k_N) )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let op3_nan : Bool := ((BEq.beq type3 FPType_SNaN) || (BEq.beq type3 FPType_QNaN))
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let type_nan ← (( do (undefined_FPType (← occLabel 1026) ()) ) : SailM FPType )
  let type_nan : FPType :=
    if (altfp : Bool)
    then
      (if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) || (BEq.beq type3
             FPType_SNaN)) : Bool)
      then FPType_SNaN
      else FPType_QNaN)
    else type_nan
  let done ← (( do (undefined_bool_at (← occLabel 1027) ()) ) : SailM Bool )
  if ((((altfp && op1_nan) && op2_nan) && op3_nan) : Bool)
  then
    (do
      let done : Bool := true
      let w__3 ← (( do (FPProcessNaN__1 type_nan op2 fpcr fpexc) ) : SailM (BitVec k_N) )
      let result := (w__3 : (BitVec k_N))
      (pure ((done, result))))
  else
    (do
      if (((altfp && op2_nan) && (op1_nan || op3_nan)) : Bool)
      then
        (do
          let done : Bool := true
          let w__4 ← (( do (FPProcessNaN__1 type_nan op2 fpcr fpexc) ) : SailM (BitVec k_N) )
          let result := (w__4 : (BitVec k_N))
          (pure ((done, result))))
      else
        (do
          if (((altfp && op3_nan) && op1_nan) : Bool)
          then
            (do
              let done : Bool := true
              let w__5 ← (( do (FPProcessNaN__1 type_nan op3 fpcr fpexc) ) : SailM (BitVec k_N) )
              let result := (w__5 : (BitVec k_N))
              (pure ((done, result))))
          else
            (do
              if ((BEq.beq type1 FPType_SNaN) : Bool)
              then
                (do
                  let done : Bool := true
                  let w__6 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec k_N) )
                  let result := (w__6 : (BitVec k_N))
                  (pure ((done, result))))
              else
                (do
                  if ((BEq.beq type2 FPType_SNaN) : Bool)
                  then
                    (do
                      let done : Bool := true
                      let w__7 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) : SailM
                        (BitVec k_N) )
                      let result := (w__7 : (BitVec k_N))
                      (pure ((done, result))))
                  else
                    (do
                      if ((BEq.beq type3 FPType_SNaN) : Bool)
                      then
                        (do
                          let done : Bool := true
                          let w__8 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) : SailM
                            (BitVec k_N) )
                          let result := (w__8 : (BitVec k_N))
                          (pure ((done, result))))
                      else
                        (do
                          if ((BEq.beq type1 FPType_QNaN) : Bool)
                          then
                            (do
                              let done : Bool := true
                              let w__9 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM
                                (BitVec k_N) )
                              let result := (w__9 : (BitVec k_N))
                              (pure ((done, result))))
                          else
                            (do
                              if ((BEq.beq type2 FPType_QNaN) : Bool)
                              then
                                (do
                                  let done : Bool := true
                                  let w__10 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) :
                                    SailM (BitVec k_N) )
                                  let result := (w__10 : (BitVec k_N))
                                  (pure ((done, result))))
                              else
                                (do
                                  if ((BEq.beq type3 FPType_QNaN) : Bool)
                                  then
                                    (do
                                      let done : Bool := true
                                      let w__11 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) :
                                        SailM (BitVec k_N) )
                                      let result := (w__11 : (BitVec k_N))
                                      (pure ((done, result))))
                                  else
                                    (let done : Bool := false
                                    let result : (BitVec k_N) :=
                                      (Sail.BitVec.castWidth (Zeros
                                        (n := (Sail.BitVec.length result))))
                                    (pure ((done, result))))))))))))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, List.elem k_N [32, 64] -/
def FPProcessNaNs3H (type1 : FPType) (type2 : FPType) (type3 : FPType) (op1 : (BitVec k_N)) (op2 : (BitVec (k_N / 2))) (op3 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  ArmFull.assert (((Sail.BitVec.length op1) == 32) || ((Sail.BitVec.length op1) == 64)) "sail-inputs/03-v8_base.sail:17082.30-17082.31"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1059)
      (Sail.BitVec.length op1))) ) : SailM (BitVec k_N) )
  let type_nan ← (( do (undefined_FPType (← occLabel 1060) ()) ) : SailM FPType )
  let altfp ← (( do
    (pure ((← do
          if ((← do
               (HaveAltFP ())) : Bool)
          then
            (do
              let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              (pure (((! w__1) : Bool))))
          else (pure false)) && (((_get_FPCRType_AH fpcr) == 1#1) : Bool))) ) : SailM Bool )
  let op1_nan : Bool := ((BEq.beq type1 FPType_SNaN) || (BEq.beq type1 FPType_QNaN))
  let op2_nan : Bool := ((BEq.beq type2 FPType_SNaN) || (BEq.beq type2 FPType_QNaN))
  let op3_nan : Bool := ((BEq.beq type3 FPType_SNaN) || (BEq.beq type3 FPType_QNaN))
  let type_nan : FPType :=
    if (altfp : Bool)
    then
      (if ((((BEq.beq type1 FPType_SNaN) || (BEq.beq type2 FPType_SNaN)) || (BEq.beq type3
             FPType_SNaN)) : Bool)
      then FPType_SNaN
      else FPType_QNaN)
    else type_nan
  let done ← (( do (undefined_bool_at (← occLabel 1061) ()) ) : SailM Bool )
  if ((((altfp && op1_nan) && op2_nan) && op3_nan) : Bool)
  then
    (do
      let done : Bool := true
      let w__3 ← (( do (FPProcessNaN__1 type_nan op2 fpcr fpexc) ) : SailM (BitVec (k_N / 2)) )
      let w__4 ← (( do
        ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__3 (Sail.BitVec.length result))) ) : SailM
        (BitVec k_N) )
      let result := (w__4 : (BitVec k_N))
      (pure ((done, result))))
  else
    (do
      if (((altfp && op2_nan) && (op1_nan || op3_nan)) : Bool)
      then
        (do
          let done : Bool := true
          let w__5 ← (( do (FPProcessNaN__1 type_nan op2 fpcr fpexc) ) : SailM (BitVec (k_N / 2))
            )
          let w__6 ← (( do
            ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__5 (Sail.BitVec.length result))) ) : SailM
            (BitVec k_N) )
          let result := (w__6 : (BitVec k_N))
          (pure ((done, result))))
      else
        (do
          if (((altfp && op3_nan) && op1_nan) : Bool)
          then
            (do
              let done : Bool := true
              let w__7 ← (( do (FPProcessNaN__1 type_nan op3 fpcr fpexc) ) : SailM
                (BitVec (k_N / 2)) )
              let w__8 ← (( do
                ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__7 (Sail.BitVec.length result))) ) :
                SailM (BitVec k_N) )
              let result := (w__8 : (BitVec k_N))
              (pure ((done, result))))
          else
            (do
              if ((BEq.beq type1 FPType_SNaN) : Bool)
              then
                (do
                  let done : Bool := true
                  let w__9 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM (BitVec k_N) )
                  let result := (w__9 : (BitVec k_N))
                  (pure ((done, result))))
              else
                (do
                  if ((BEq.beq type2 FPType_SNaN) : Bool)
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
                      if ((BEq.beq type3 FPType_SNaN) : Bool)
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
                          if ((BEq.beq type1 FPType_QNaN) : Bool)
                          then
                            (do
                              let done : Bool := true
                              let w__14 ← (( do (FPProcessNaN__1 type1 op1 fpcr fpexc) ) : SailM
                                (BitVec k_N) )
                              let result := (w__14 : (BitVec k_N))
                              (pure ((done, result))))
                          else
                            (do
                              if ((BEq.beq type2 FPType_QNaN) : Bool)
                              then
                                (do
                                  let done : Bool := true
                                  let w__15 ← (( do (FPProcessNaN__1 type2 op2 fpcr fpexc) ) :
                                    SailM (BitVec (k_N / 2)) )
                                  let w__16 ← (( do
                                    ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__15
                                      (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                                  let result := (w__16 : (BitVec k_N))
                                  (pure ((done, result))))
                              else
                                (do
                                  if ((BEq.beq type3 FPType_QNaN) : Bool)
                                  then
                                    (do
                                      let done : Bool := true
                                      let w__17 ← (( do (FPProcessNaN__1 type3 op3 fpcr fpexc) ) :
                                        SailM (BitVec (k_N / 2)) )
                                      let w__18 ← (( do
                                        ((Sail.BitVec.castWidth ) <$> (FPConvertNaN w__17
                                          (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
                                      let result := (w__18 : (BitVec k_N))
                                      (pure ((done, result))))
                                  else
                                    (let done : Bool := false
                                    let result : (BitVec k_N) :=
                                      (Sail.BitVec.castWidth (Zeros
                                        (n := (Sail.BitVec.length result))))
                                    (pure ((done, result))))))))))))


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
  ArmFull.assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "sail-inputs/03-v8_base.sail:28705.65-28705.66"
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
  ArmFull.assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "sail-inputs/03-v8_base.sail:28734.65-28734.66"
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
  ArmFull.assert (accdesc_in.tagaccess && (! accdesc_in.tagchecked)) "sail-inputs/03-v8_base.sail:29023.65-29023.66"
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


end ArmFull.Functions
