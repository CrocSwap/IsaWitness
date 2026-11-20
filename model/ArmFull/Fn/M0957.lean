module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0045
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0114
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0166
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0173
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0215
public import ArmFull.Fn.M0227
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0244
public import ArmFull.Fn.M0248
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0881
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M0883 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: N : Nat, k_fpexc : Bool, N = 32 -/
def FPRoundBF (op : real) (fpcr : (BitVec 64)) (rounding : FPRounding) (fpexc : Bool) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert (N == 32) "sail-inputs/03-v8_base.sail:32220.18-32220.19"
  let isbfloat16 : Bool := true
  ((Sail.BitVec.castWidth ) <$> (FPRoundBase__1 op fpcr rounding isbfloat16 fpexc N))


/-- Type quantifiers: k_N : Nat, k_fpexc : Bool, k_N = 32 -/
def FPProcessNaNs4 (type1 : FPType) (type2 : FPType) (type3 : FPType) (type4 : FPType) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (op3 : (BitVec (k_N / 2))) (op4 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) (fpexc : Bool) : SailM (Bool × (BitVec k_N)) := do
  ArmFull.assert (SPEMaxCounters == 32) "sail-inputs/03-v8_base.sail:32280.19-32280.20"
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
  ArmFull.assert ((Sail.BitVec.length op) == 16) "sail-inputs/03-v8_base.sail:32459.19-32459.20"
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
            ArmFull.assert w__26 "sail-inputs/03-v8_base.sail:36661.71-36661.72"
            ArmFull.assert ((BitVec.toNat
                ((Sail.BitVec.castWidth (m := 33) (integer_subrange size 32 0)) &&& (Sail.BitVec.castWidth (m := 33) (integer_subrange
                    (size -i 1) 32 0)))) == 0) "sail-inputs/03-v8_base.sail:36662.61-36662.62"
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


def AArch64_IC__1 (regval : (BitVec 64)) (opscope : CacheOpScope) : SailM Unit := SailME.run do
  let ss ← (( do (undefined_SecurityState (← occLabel 2490) ()) ) : SailME Unit SecurityState )
  let cache ← (( do (undefined_CacheRecord (← occLabel 2491) ()) ) : SailME Unit CacheRecord )
  let cache : CacheRecord := { cache with acctype := AccessType_IC }
  let cache : CacheRecord := { cache with cachetype := CacheType_Instruction }
  let cache : CacheRecord := { cache with cacheop := CacheOp_Invalidate }
  let cache : CacheRecord := { cache with opscope := opscope }
  if (((BEq.beq opscope CacheOpScope_ALLU) || (BEq.beq opscope CacheOpScope_ALLUIS)) : Bool)
  then
    (do
      let w__0 ← (( do readReg PSTATE ) : SailME Unit ProcState )
      let ss ← (( do (SecurityStateAtEL w__0.EL) ) : SailME Unit SecurityState )
      let cache : CacheRecord := { cache with cpas := (CPASAtSecurityState ss) }
      let w__7 ← (( do
        if (((BEq.beq opscope CacheOpScope_ALLUIS) : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      if (((BEq.beq opscope CacheOpScope_ALLU) : Bool) : Bool)
                      then
                        (do
                          let w__1 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                          (pure (((w__1.EL == EL1) : Bool))))
                      else (pure false)) : Bool)
                 then
                   (do
                     (EL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__5 ← (( do readReg HCR_EL2 ) : SailME Unit (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_FB w__5) == 1#1) : Bool))))
            else (pure false)) ) : SailME Unit Bool )
      let cache : CacheRecord :=
        if (w__7 : Bool)
        then { cache with shareability := Shareability_ISH }
        else { cache with shareability := Shareability_NSH }
      let cache : CacheRecord := { cache with regval := regval }
      (CACHE_OP cache))
  else
    (do
      ArmFull.assert (BEq.beq opscope CacheOpScope_PoU) "sail-inputs/03-v8_base.sail:36778.42-36778.43"
      let w__10 ← (( do
        if ((← do
             (EL2Enabled ())) : Bool)
        then
          (do
            let w__9 ← (( do (IsInHost ()) ) : SailME Unit Bool )
            (pure (((! w__9) : Bool))))
        else (pure false) ) : SailME Unit Bool )
      let cache ← (( do
        if (w__10 : Bool)
        then
          (do
            let w__13 ← (( do
              if ((← do
                   let w__11 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                   (pure (((w__11.EL == EL0) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  let w__12 ← (( do readReg PSTATE ) : SailME Unit ProcState )
                  (pure (((w__12.EL == EL1) : Bool)))) ) : SailME Unit Bool )
            if (w__13 : Bool)
            then
              (do
                let cache : CacheRecord := { cache with is_vmid_valid := true }
                let w__14 ← (( do (VMID_read ()) ) : SailME Unit (BitVec 16) )
                let cache := ({ cache with vmid := w__14 } : CacheRecord)
                (pure (cache)))
            else
              (let cache : CacheRecord := { cache with is_vmid_valid := false }
              (pure (cache))))
        else
          (let cache : CacheRecord := { cache with is_vmid_valid := false }
          (pure (cache))) ) : SailME Unit CacheRecord )
      let w__15 ← (( do readReg PSTATE ) : SailME Unit ProcState )
      let cache ← (( do
        if ((w__15.EL == EL0) : Bool)
        then
          (do
            let cache : CacheRecord := { cache with is_asid_valid := true }
            let w__16 ← (( do (ASID_read ()) ) : SailME Unit (BitVec 16) )
            let cache := ({ cache with asid := w__16 } : CacheRecord)
            (pure (cache)))
        else
          (let cache : CacheRecord := { cache with is_asid_valid := false }
          (pure (cache))) ) : SailME Unit CacheRecord )
      let vaddress : (BitVec 64) := regval
      let need_translate ← (( do (ICInstNeedsTranslation opscope) ) : SailME Unit Bool )
      let cache : CacheRecord := { cache with vaddress := regval }
      let cache : CacheRecord := { cache with shareability := Shareability_NSH }
      let cache : CacheRecord := { cache with translated := need_translate }
      if ((! need_translate) : Bool)
      then
        (do
          let w__17 ← (( do (__UNKNOWN_FullAddress ()) ) : SailME Unit FullAddress )
          let cache := ({ cache with paddress := w__17 } : CacheRecord)
          (CACHE_OP cache)
          SailME.throw (() : Unit))
      else
        (do
          let accdesc ← (( do (CreateAccDescIC cache) ) : SailME Unit AccessDescriptor )
          let aligned : Bool := true
          let size : Nat := 0
          let memaddrdesc ← (( do (AArch64_TranslateAddress vaddress accdesc aligned size) ) :
            SailME Unit AddressDescriptor )
          if ((IsFault memaddrdesc) : Bool)
          then
            (do
              (AArch64_Abort regval memaddrdesc.fault))
          else (pure (()))
          let cache : CacheRecord := { cache with cpas := (CPASAtPAS memaddrdesc.paddress.paspace) }
          let cache : CacheRecord := { cache with paddress := memaddrdesc.paddress }
          (CACHE_OP cache)))


/-- Type quantifiers: k_aligned : Bool, size : Int -/
def AArch32_TranslateAddress (va : (BitVec 32)) (accdesc : AccessDescriptor) (aligned : Bool) (size : Int) : SailM AddressDescriptor := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let regime ← (( do (TranslationRegime w__0.EL) ) : SailM Regime )
  let w__1 ← (( do (RegimeUsingAArch32 regime) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      (AArch64_TranslateAddress (Sail.BitVec.zeroExtend va 64) accdesc aligned size))
  else
    (do
      let regime ← (( do (TranslationRegime accdesc.el) ) : SailM Regime )
      let tsi ← (( do (AArch32_GetTranslationStartInfo regime accdesc.ss accdesc va size) ) :
        SailM TranslationStartInfo )
      (start_translation tsi)
      let result ← (( do (AArch32_FullTranslate va accdesc aligned) ) : SailM AddressDescriptor )
      let result ← (( do
        if ((! (IsFault result)) : Bool)
        then
          (do
            let w__3 ← (( do (AArch32_CheckDebug va accdesc size) ) : SailM FaultRecord )
            let result := ({ result with fault := w__3 } : AddressDescriptor)
            (pure (result)))
        else (pure (result)) ) : SailM AddressDescriptor )
      let result : AddressDescriptor := { result with vaddress := (Sail.BitVec.zeroExtend va 64) }
      (end_translation result)
      (pure (result)))


def CheckAdvSIMDEnabled (_ : Unit) : SailM Unit := do
  let fpexc_check : Bool := true
  let advsimd : Bool := true
  (AArch32_CheckAdvSIMDOrFPEnabled fpexc_check advsimd)
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 31
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do readReg _Dclone ) : SailM (Vector (BitVec 64) 32) )
        let w__1 ← (( do (D_read i) ) : SailM (BitVec 64) )
        writeReg _Dclone (vectorUpdate w__0 (Sail.Int.toNatChecked (i)) w__1)
    (pure loop_vars))


end ArmFull.Functions
