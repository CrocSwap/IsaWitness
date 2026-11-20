module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0119
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0180
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0194
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0227
public import ArmFull.Fn.M0235
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0237
public import ArmFull.Fn.M0238
public import ArmFull.Fn.M0239
public import ArmFull.Fn.M0240 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_cold_reset : Bool -/
def AArch64_ResetControlRegisters (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with ZA := 0#1 }
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__1 with SM := 0#1 }
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__2 with ALLINT := 0#1 }
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__3 with EXLOCK := 0#1 }
  (ResetControlRegisters cold_reset)
  (pure ((_TLBInvalidate ())))


def SPEToCollectSample (_ : Unit) : SailM Bool := SailME.run do
  let w__0 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
  if ((IsZero (_get_PMSICR_EL1_Type_COUNT w__0)) : Bool)
  then
    (do
      (SPEResetSampleCounter ()))
  else
    (do
      let w__1 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      let w__2 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__1 31 0
        (BitVec.subInt (_get_PMSICR_EL1_Type_COUNT w__2) 1))
      let w__3 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      if ((IsZero (_get_PMSICR_EL1_Type_COUNT w__3)) : Bool)
      then
        (do
          let w__6 ← (( do
            if ((← do
                 let w__4 ← (( do readReg PMSIRR_EL1 ) : SailME Bool (BitVec 64) )
                 (pure ((((_get_PMSIRR_EL1_Type_RND w__4) == 1#1) : Bool)))) : Bool)
            then
              (do
                let w__5 ← (( do readReg PMSIDR_EL1 ) : SailME Bool (BitVec 64) )
                (pure ((((_get_PMSIDR_EL1_Type_ERnd w__5) == 1#1) : Bool))))
            else (pure false) ) : SailME Bool Bool )
          if (w__6 : Bool)
          then
            (do
              let w__7 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
              let w__8 ← (( do (SPEGetRandomInterval ()) ) : SailME Bool (BitVec 8) )
              writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__7 63 56 w__8))
          else
            (do
              SailME.throw (true : Bool)))
      else (pure (())))
  let w__9 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
  if (((BitVec.toNat (_get_PMSICR_EL1_Type_ECOUNT w__9)) != 0) : Bool)
  then
    (do
      let w__10 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      let w__11 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__10 63 56
        (BitVec.subInt (_get_PMSICR_EL1_Type_ECOUNT w__11) 1))
      let w__12 ← (( do readReg PMSICR_EL1 ) : SailME Bool (BitVec 64) )
      if ((IsZero (_get_PMSICR_EL1_Type_ECOUNT w__12)) : Bool)
      then
        (do
          SailME.throw (true : Bool))
      else (pure (())))
  else (pure (()))
  (pure (false))


def SPESampleMemCopy (_ : Unit) : SailM Unit := do
  let loads_pass_filter ← (( do
    if ((← do
         let w__0 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_PMSFCR_EL1_Type_FT w__0) == 1#1) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_PMSFCR_EL1_Type_LD w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let stores_pass_filter ← (( do
    if ((← do
         let w__2 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_PMSFCR_EL1_Type_FT w__2) == 1#1) : Bool)))) : Bool)
    then
      (do
        let w__3 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_PMSFCR_EL1_Type_ST w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let record_load ← (( do (undefined_bool_at (← occLabel 2449) ()) ) : SailM Bool )
  let record_load ← (( do
    if ((loads_pass_filter && (! stores_pass_filter)) : Bool)
    then (pure (true))
    else
      (do
        if (((! loads_pass_filter) && stores_pass_filter) : Bool)
        then (pure (false))
        else
          (do
            (SPEGetRandomBoolean ()))) ) : SailM Bool )
  writeReg SPESampleClass 0b01#2
  let ldst : (BitVec 1) :=
    if (record_load : Bool)
    then 0#1
    else 1#1
  let w__5 ← (( do readReg SPESampleSubclass ) : SailM (BitVec 8) )
  writeReg SPESampleSubclass (Sail.BitVec.updateSubrange w__5 7 0 (0b0010000#7 +++ ldst))
  writeReg SPESampleSubclassValid true
  writeReg SPESampleOpType (if (record_load : Bool)
  then OpType_Load
  else OpType_Store)


def BRBEISB (_ : Unit) : SailM Unit := do
  let branch_conditional : Bool := false
  let w__0 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
  (BRBEBranch BranchType_DIR branch_conditional (BitVec.addInt w__0 4))


def DRPSInstruction (_ : Unit) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let sync_errors ← (( do
    if ((← do
         (HaveIESB ())) : Bool)
    then
      (do
        let w__1 ← (( do (SCTLR_read__1 ()) ) : SailM (BitVec 64) )
        (pure ((((_get_SCTLRType_IESB w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__4 ← (( do
    if ((← do
         (HaveDoubleFaultExt ())) : Bool)
    then
      (do
        let w__3 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  let sync_errors ← (( do
    if (w__4 : Bool)
    then
      (do
        if ((sync_errors : Bool) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      let w__5 ← (( do (EffectiveEA ()) ) : SailM (BitVec 1) )
                      (pure (((w__5 == 1#1) : Bool)))) : Bool)
                 then
                   (do
                     let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                     (pure ((((_get_SCR_EL3_Type_NMEA w__6) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
                (pure (((w__8.EL == EL3) : Bool))))
            else (pure false)))
    else (pure (sync_errors)) ) : SailM Bool )
  let w__11 ← (( do (ConstrainUnpredictableBool Unpredictable_IESBinDebug) ) : SailM Bool )
  let sync_errors : Bool :=
    if ((! w__11) : Bool)
    then false
    else sync_errors
  let _ : Unit :=
    if (sync_errors : Bool)
    then (SynchronizeErrors ())
    else ()
  (DebugRestorePSR ())


/-- Type quantifiers: k_linked_to : Bool, n_in : Int -/
def AArch32_BreakpointValueMatch (n_in : Int) (vaddress : (BitVec 32)) (linked_to : Bool) : SailM (Bool × Bool) := SailME.run do
  let n : Int := n_in
  let c ← (( do (undefined_Constraint (← occLabel 2649) ()) ) : SailME (Bool × Bool) Constraint
    )
  let w__0 ← (( do (NumBreakpointsImplemented ()) ) : SailME (Bool × Bool) Int )
  let (c, n) ← (( do
    if ((n ≥b w__0) : Bool)
    then
      (do
        let w__1 ← (( do (NumBreakpointsImplemented ()) ) : SailME (Bool × Bool) Int )
        let w__2 ← (( do (ConstrainUnpredictableInteger 0 (w__1 -i 1) Unpredictable_BPNOTIMPL) ) :
          SailME (Bool × Bool) (Constraint × Int) )
        let (tup__0, tup__1) := (w__2 : (Constraint × Int))
        let c : Constraint := tup__0
        let n : Int := tup__1
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || (BEq.beq c Constraint_UNKNOWN)) "sail-inputs/03-v8_base.sail:40271.65-40271.66"
        if ((BEq.beq c Constraint_DISABLED) : Bool)
        then
          (do
            SailME.throw ((false, false) : (Bool × Bool)))
        else (pure (()))
        (pure ((c, n))))
    else (pure ((c, n))) ) : SailME (Bool × Bool) (Constraint × Int) )
  let n : Int := n
  ArmFull.assert ((0 ≤b n) && (n <b 16)) "sail-inputs/03-v8_base.sail:40278.42-40278.43"
  let w__3 ← (( do (DBGBCR_read (Sail.Int.toNatChecked (n))) ) : SailME (Bool × Bool) (BitVec 32)
    )
  if (((_get_DBGBCR_Type_E w__3) == 0#1) : Bool)
  then (pure ((false, false)))
  else
    (do
      let w__4 ← (( do (DBGBCR_read (Sail.Int.toNatChecked (n))) ) : SailME (Bool × Bool)
        (BitVec 32) )
      let dbgtype : (BitVec 4) := (_get_DBGBCR_Type_BT w__4)
      let w__5 ← (( do (AArch32_ReservedBreakpointType n dbgtype) ) : SailME (Bool × Bool)
        (Constraint × (BitVec 4)) )
      let (tup__0, tup__1) := (w__5 : (Constraint × (BitVec 4)))
      let c : Constraint := tup__0
      let dbgtype : (BitVec 4) := tup__1
      if ((BEq.beq c Constraint_DISABLED) : Bool)
      then (pure ((false, false)))
      else
        (do
          let b__5 := dbgtype
          let match_addr : Bool :=
            (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__5 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__5 1 1)) == (0#1 : (BitVec 1)))) : Bool)
            then true
            else false : Bool)
          let b__4 := dbgtype
          let mismatch : Bool :=
            (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__4 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
            then true
            else false : Bool)
          let b__3 := dbgtype
          let match_vmid : Bool :=
            (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__3 3 2)) == (0b10#2 : (BitVec 2))) : Bool)
            then true
            else false : Bool)
          let b__2 := dbgtype
          let match_cid1 : Bool :=
            (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 1 1)) == (1#1 : (BitVec 1))) : Bool)
            then true
            else false : Bool)
          let b__1 := dbgtype
          let match_cid2 : Bool :=
            (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 3 2)) == (0b11#2 : (BitVec 2))) : Bool)
            then true
            else false : Bool)
          let b__0 := dbgtype
          let linking_enabled : Bool :=
            (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (1#1 : (BitVec 1))) : Bool)
            then true
            else false : Bool)
          if ((linked_to && (! linking_enabled)) : Bool)
          then
            (do
              let w__6 ← (( do (ConstrainUnpredictableBool Unpredictable_BPLINKINGDISABLED) ) :
                SailME (Bool × Bool) Bool )
              if ((! w__6) : Bool)
              then
                (do
                  SailME.throw ((false, false) : (Bool × Bool)))
              else (pure (())))
          else (pure (()))
          if ((((! linked_to) && linking_enabled) && (! match_addr)) : Bool)
          then (pure ((false, false)))
          else
            (do
              let bvr_match : Bool := false
              let bxvr_match : Bool := false
              let bvr_match ← (( do
                if (match_addr : Bool)
                then
                  (do
                    let byte : Int := (BitVec.toNat (Sail.BitVec.extractLsb vaddress 1 0))
                    ArmFull.assert ((byte == 0) || (byte == 2)) "sail-inputs/03-v8_base.sail:40324.36-40324.37"
                    let w__7 ← (( do (DBGBCR_read (Sail.Int.toNatChecked (n))) ) : SailME
                      (Bool × Bool) (BitVec 32) )
                    let byte_select_match : Bool :=
                      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access (_get_DBGBCR_Type_BAS w__7)
                            (Sail.Int.toNatChecked (byte)))])) == 1#1)
                    let top : Nat := 31
                    (pure ((← do
                          let w__8 ← (( do (DBGBVR_read (Sail.Int.toNatChecked (n))) ) : SailME
                            (Bool × Bool) (BitVec 32) )
                          (pure ((((Sail.BitVec.castWidth (m := ((Sail.Int.toNatChecked top) - 1)) (Sail.BitVec.extractLsb
                                vaddress top 2)) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                                w__8 top 2))) : Bool)))) && byte_select_match)))
                else
                  (do
                    if (match_cid1 : Bool)
                    then
                      (do
                        if ((← do
                             let w__10 ← (( do readReg PSTATE ) : SailME (Bool × Bool) ProcState
                               )
                             (pure (((w__10.EL != EL2) : Bool)))) : Bool)
                        then
                          (do
                            let w__11 ← (( do (CONTEXTIDR_read ()) ) : SailME (Bool × Bool)
                              (BitVec 32) )
                            let w__12 ← (( do (DBGBVR_read (Sail.Int.toNatChecked (n))) ) : SailME
                              (Bool × Bool) (BitVec 32) )
                            (pure (((w__11 == (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                  w__12 31 0))) : Bool))))
                        else (pure false))
                    else (pure (bvr_match))) ) : SailME (Bool × Bool) Bool )
              let bxvr_match ← (( do
                if (match_vmid : Bool)
                then
                  (do
                    let vmid ← (( do (undefined_bitvector_at (← occLabel 2650) 16) ) : SailME
                      (Bool × Bool) (BitVec 16) )
                    let bvr_vmid ← (( do (undefined_bitvector_at (← occLabel 2651) 16) ) :
                      SailME (Bool × Bool) (BitVec 16) )
                    let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailME (Bool × Bool) Bool )
                    let (bvr_vmid, vmid) ← (( do
                      if (w__14 : Bool)
                      then
                        (do
                          let w__15 ← (( do readReg VTTBR ) : SailME (Bool × Bool) (BitVec 64) )
                          let vmid :=
                            ((Sail.BitVec.zeroExtend (_get_VTTBR_Type_VMID w__15) 16) : (BitVec 16))
                          let w__16 ← (( do (DBGBXVR_read (Sail.Int.toNatChecked (n))) ) : SailME
                            (Bool × Bool) (BitVec 32) )
                          let bvr_vmid :=
                            ((Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb w__16 7 0) 16) : (BitVec 16))
                          (pure ((bvr_vmid, vmid))))
                      else
                        (do
                          let w__19 ← (( do
                            if ((← do
                                 let w__17 ← (( do (Have16bitVMID ()) ) : SailME (Bool × Bool)
                                   Bool )
                                 (pure (((! w__17) : Bool)))) : Bool)
                            then (pure true)
                            else
                              (do
                                let w__18 ← (( do readReg VTCR_EL2 ) : SailME (Bool × Bool)
                                  (BitVec 64) )
                                (pure ((((_get_VTCR_EL2_Type_VS w__18) == 0#1) : Bool)))) ) : SailME
                            (Bool × Bool) Bool )
                          if (w__19 : Bool)
                          then
                            (do
                              let w__20 ← (( do (VTTBR_EL2_read ()) ) : SailME (Bool × Bool)
                                (BitVec 128) )
                              let vmid :=
                                ((Sail.BitVec.zeroExtend
                                  (Sail.BitVec.extractLsb (_get_VTTBR_EL2_Type_VMID w__20) 7 0) 16) : (BitVec 16))
                              let w__21 ← (( do (DBGBXVR_read (Sail.Int.toNatChecked (n))) ) :
                                SailME (Bool × Bool) (BitVec 32) )
                              let bvr_vmid :=
                                ((Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb w__21 7 0) 16) : (BitVec 16))
                              (pure ((bvr_vmid, vmid))))
                          else
                            (do
                              let w__22 ← (( do (VTTBR_EL2_read ()) ) : SailME (Bool × Bool)
                                (BitVec 128) )
                              let vmid := ((_get_VTTBR_EL2_Type_VMID w__22) : (BitVec 16))
                              let w__23 ← (( do (DBGBXVR_read (Sail.Int.toNatChecked (n))) ) :
                                SailME (Bool × Bool) (BitVec 32) )
                              let bvr_vmid := ((Sail.BitVec.extractLsb w__23 15 0) : (BitVec 16))
                              (pure ((bvr_vmid, vmid))))) ) : SailME (Bool × Bool)
                      ((BitVec 16) × (BitVec 16)) )
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    let w__24 ← (( do readReg PSTATE ) : SailME (Bool × Bool)
                                      ProcState )
                                    (pure (((w__24.EL == EL0) : Bool)))) : Bool)
                               then (pure true)
                               else
                                 (do
                                   let w__25 ← (( do readReg PSTATE ) : SailME (Bool × Bool)
                                     ProcState )
                                   (pure (((w__25.EL == EL1) : Bool))))) : Bool)
                          then
                            (do
                              (EL2Enabled ()))
                          else (pure false)) && ((vmid == bvr_vmid) : Bool))))
                else
                  (do
                    if (match_cid2 : Bool)
                    then
                      (do
                        if ((← do
                             if ((← do
                                  if ((← do
                                       let w__30 ← (( do readReg PSTATE ) : SailME (Bool × Bool)
                                         ProcState )
                                       (pure (((w__30.EL != EL3) : Bool)))) : Bool)
                                  then
                                    (do
                                      (EL2Enabled ()))
                                  else (pure false)) : Bool)
                             then
                               (do
                                 let w__33 ← (( do (ELUsingAArch32 EL2) ) : SailME (Bool × Bool)
                                   Bool )
                                 (pure (((! w__33) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__35 ← (( do (DBGBXVR_read (Sail.Int.toNatChecked (n))) ) :
                              SailME (Bool × Bool) (BitVec 32) )
                            let w__36 ← (( do readReg CONTEXTIDR_EL2 ) : SailME (Bool × Bool)
                              (BitVec 64) )
                            (pure ((((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb w__35
                                  31 0)) == (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                  w__36 31 0))) : Bool))))
                        else (pure false))
                    else (pure (bxvr_match))) ) : SailME (Bool × Bool) Bool )
              let bvr_match_valid : Bool := (match_addr || match_cid1)
              let bxvr_match_valid : Bool := (match_vmid || match_cid2)
              let val_match : Bool :=
                (((! bxvr_match_valid) || bxvr_match) && ((! bvr_match_valid) || bvr_match))
              (pure (((val_match && (! mismatch)), ((! val_match) && mismatch)))))))


/-- Type quantifiers: k_cold_reset : Bool -/
def AArch32_ResetControlRegisters (cold_reset : Bool) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__0 with SS := 0#1 }
  (ResetControlRegisters cold_reset)
  (pure ((_TLBInvalidate ())))


def gic_write_ram (offset : (BitVec 16)) (data : (BitVec 32)) : SailM Unit := do
  let accdesc ← (( do (CreateAccDescGPR MemOp_STORE false true false) ) : SailM AccessDescriptor )
  let pa := (Sail.BitVec.zeroExtend (GIC_BASE +++ offset) 56)
  let w__0 ← (( do
    (sail_mem_write (write_request accdesc none 4 (Sail.BitVec.zeroExtend pa 64) pa data)) ) : SailM
    (Result (Option Bool) Fault) )
  match w__0 with
  | .Ok _ => (pure (()))
  | .Err _ =>
    (do
      ArmFull.assert false "sail-inputs/08-devices.sail:145.26-145.27"
      throw Error.Exit)


def decode_aarch32_instrs_DCPS1_T1enc_A_txt (_ : Unit) : SailM Unit := do
  (execute_aarch32_instrs_DCPS1_Op_A_txt ())


def decode_aarch32_instrs_DCPS2_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveEL EL2) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch32_instrs_DCPS2_Op_A_txt ())


def decode_aarch32_instrs_DCPS3_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  (execute_aarch32_instrs_DCPS3_Op_A_txt ())


def execute_aarch64_instrs_system_exceptions_debug_exception (target_level : (BitVec 2)) : SailM Unit := do
  (DCPSInstruction target_level)


/-- Type quantifiers: k_interrupt : Bool, k_retry : Bool -/
def FailTransaction__1 (cause : TMFailure) (retry : Bool) (interrupt : Bool) (reason : (BitVec 15)) : SailM Unit := do
  ArmFull.assert ((! retry) || (! interrupt)) "sail-inputs/03-v8_base.sail:7584.48-7584.49"
  let w__3 ← (( do
    if ((← do
         (HaveBRBExt ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (BranchRecordAllowed w__1.EL))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      let w__4 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__4 6 6 1#1))
  else (pure (()))
  let _ : Unit := (DiscardTransactionalWrites ())
  if ((bne cause TMFailure_TRIVIAL) : Bool)
  then
    (do
      (RestoreTransactionCheckpoint ()))
  else (pure (()))
  let _ : Unit := (ClearExclusiveLocal (ProcessorID ()))
  let result : (BitVec 64) := (Zeros (n := 64))
  let result : (BitVec 64) :=
    (BitVec.update result 23
      (Bit
        (if (interrupt : Bool)
        then 1#1
        else 0#1)))
  let result : (BitVec 64) :=
    (BitVec.update result 15
      (Bit
        (if ((retry && (! interrupt)) : Bool)
        then 1#1
        else 0#1)))
  let result : (BitVec 64) :=
    match cause with
    | .TMFailure_TRIVIAL => (BitVec.update result 24 (Bit 1#1))
    | .TMFailure_DBG => (BitVec.update result 22 (Bit 1#1))
    | .TMFailure_NEST => (BitVec.update result 21 (Bit 1#1))
    | .TMFailure_SIZE => (BitVec.update result 20 (Bit 1#1))
    | .TMFailure_ERR => (BitVec.update result 19 (Bit 1#1))
    | .TMFailure_IMP => (BitVec.update result 18 (Bit 1#1))
    | .TMFailure_MEM => (BitVec.update result 17 (Bit 1#1))
    | .TMFailure_CNCL =>
      (let result : (BitVec 64) := (BitVec.update result 16 (Bit 1#1))
      (Sail.BitVec.updateSubrange result 14 0 reason))
  let w__5 ← (( do readReg TSTATE ) : SailM TMState )
  writeReg TSTATE { w__5 with depth := 0 }
  let w__6 ← (( do readReg TSTATE ) : SailM TMState )
  (X_set w__6.Rt 64 result)
  let branch_conditional : Bool := false
  let w__7 ← (( do readReg TSTATE ) : SailM TMState )
  (BranchTo w__7.nPC BranchType_TMFAIL branch_conditional)
  (EndOfInstruction ())


def __ReadGIC (offset : (BitVec 16)) : SailM (BitVec 32) := do
  match offset with
  | 0x1004 => (pure (__GICD_TYPER))
  | 0x1800 => (pure (0xFFFFFFFF#32))
  | 0x1C04 =>
    (do
      let w__0 ← (( do (gic_read_ram 0x1C04#16) ) : SailM (BitVec 32) )
      let _ : Unit := (prerr_bits "[GIC] Read 1C04: " w__0)
      (gic_read_ram 0x1C04#16))
  | 0x2000 =>
    (do
      let w__2 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
      let _ : Unit := (prerr_bits "[GIC] Read GICC_CTLR " w__2)
      readReg GICC_CTLR)
  | 0x200C =>
    (do
      let intid ← (( do (__GIC_AcknowledgeInterrupt ()) ) : SailM (BitVec 32) )
      let _ : Unit := (prerr_bits "[GIC] Acknowledged interrupt " intid)
      (pure (intid)))
  | 0x20FC => (pure (__GICC_IIDR))
  | _ =>
    (let _ : Unit := (prerr_bits "[GIC] Read offset: " offset)
    (pure ((Zeros (n := 32)))))


/-- Type quantifiers: k_isbreakpnt : Bool, k_linked_in : Bool, linked_n_in : Int -/
def AArch64_StateMatch (ssc_in : (BitVec 2)) (ssce_in : (BitVec 1)) (hmc_in : (BitVec 1)) (pxc_in : (BitVec 2)) (linked_in : Bool) (linked_n_in : Int) (isbreakpnt : Bool) (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) : SailM Bool := SailME.run do
  let first_ctx_cmp ← (( do (undefined_int_at (← occLabel 1383) ()) ) : SailME Bool Int )
  let last_ctx_cmp ← (( do (undefined_int_at (← occLabel 1384) ()) ) : SailME Bool Int )
  let linked_to ← (( do (undefined_bool_at (← occLabel 1385) ()) ) : SailME Bool Bool )
  let w__0 ← (( do (HaveRME ()) ) : SailME Bool Bool )
  if ((! w__0) : Bool)
  then
    (do
      ArmFull.assert (ssce_in == 0#1) "sail-inputs/03-v8_base.sail:23525.29-23525.30")
  else (pure (()))
  let ssc : (BitVec 2) := ssc_in
  let ssce : (BitVec 1) := ssce_in
  let hmc : (BitVec 1) := hmc_in
  let pxc : (BitVec 2) := pxc_in
  let linked : Bool := linked_in
  let linked_n : Int := linked_n_in
  let c ← (( do (undefined_Constraint (← occLabel 1386) ()) ) : SailME Bool Constraint )
  let w__1 ← (( do (CheckValidStateMatch ssc ssce hmc pxc isbreakpnt) ) : SailME Bool
    (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)) )
  let (tup__0, tup__1, tup__2, tup__3, tup__4) :=
    (w__1 : (Constraint × (BitVec 2) × (BitVec 1) × (BitVec 1) × (BitVec 2)))
  let c : Constraint := tup__0
  let ssc : (BitVec 2) := tup__1
  let ssce : (BitVec 1) := tup__2
  let hmc : (BitVec 1) := tup__3
  let pxc : (BitVec 2) := tup__4
  if ((BEq.beq c Constraint_DISABLED) : Bool)
  then (pure (false))
  else
    (do
      let EL3_match ← (( do
        (pure ((← do
              (pure ((← do
                    (HaveEL EL3)) && ((hmc == 1#1) : Bool)))) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                  ssc 0)])) == 0#1) : Bool))) ) : SailME Bool Bool )
      let EL2_match ← (( do
        (pure ((← do
              (HaveEL EL2)) && ((((hmc == 1#1) && ((ssc +++ pxc) != 0b1000#4)) || (ssc == 0b11#2)) : Bool)))
        ) : SailME Bool Bool )
      let EL1_match : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pxc 0)])) == 1#1)
      let EL0_match : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access pxc 1)])) == 1#1)
      let priv_match ← (( do (undefined_bool_at (← occLabel 1387) ()) ) : SailME Bool Bool )
      let questionMark := accdesc.el
      let priv_match : Bool :=
        if ((questionMark == EL3) : Bool)
        then EL3_match
        else
          (if ((questionMark == EL2) : Bool)
          then EL2_match
          else
            (if ((questionMark == EL1) : Bool)
            then EL1_match
            else
              (if ((questionMark == EL0) : Bool)
              then EL0_match
              else priv_match)))
      let ss_match ← (( do (undefined_bool_at (← occLabel 1388) ()) ) : SailME Bool Bool )
      let ss_match : Bool :=
        match (BitVec.setWidth 3 (ssce +++ ssc)) with
        | 0b000 => ((hmc == 1#1) || (bne accdesc.ss SS_Root))
        | 0b001 => (BEq.beq accdesc.ss SS_NonSecure)
        | 0b010 =>
          (((hmc == 1#1) && (BEq.beq accdesc.ss SS_Root)) || (BEq.beq accdesc.ss SS_Secure))
        | 0b011 => (((hmc == 1#1) && (bne accdesc.ss SS_Root)) || (BEq.beq accdesc.ss SS_Secure))
        | 0b101 => (BEq.beq accdesc.ss SS_Realm)
        | _ => ss_match
      let linked_match : Bool := false
      let is_linked_mismatch : Bool := false
      let (linked, linked_n) ← (( do
        if (linked : Bool)
        then
          (do
            let w__5 ← (( do (IsContextMatchingBreakpoint linked_n) ) : SailME Bool Bool )
            if ((! w__5) : Bool)
            then
              (do
                let w__6 ← (( do (ContextMatchingBreakpointRange ()) ) : SailME Bool (Int × Int)
                  )
                let (tup__0, tup__1) := (w__6 : (Int × Int))
                let first_ctx_cmp : Int := tup__0
                let last_ctx_cmp : Int := tup__1
                let last_ctx_cmp : Int := last_ctx_cmp
                let first_ctx_cmp : Int := first_ctx_cmp
                let w__7 ← (( do
                  (ConstrainUnpredictableInteger first_ctx_cmp last_ctx_cmp
                    Unpredictable_BPNOTCTXCMP) ) : SailME Bool (Constraint × Int) )
                let (tup__0, tup__1) := (w__7 : (Constraint × Int))
                let c : Constraint := tup__0
                let linked_n : Int := tup__1
                ArmFull.assert ((BEq.beq c Constraint_DISABLED) || ((BEq.beq c Constraint_NONE) || (BEq.beq
                      c Constraint_UNKNOWN))) "sail-inputs/03-v8_base.sail:23585.92-23585.93"
                let linked ← (( do
                  match c with
                  | .Constraint_DISABLED =>
                    (do
                      SailME.throw (false : Bool)
                      (pure (linked)))
                  | .Constraint_NONE => (pure (false))
                  | _ => (pure (linked)) ) : SailME Bool Bool )
                (pure ((linked, linked_n))))
            else (pure ((linked, linked_n))))
        else (pure ((linked, linked_n))) ) : SailME Bool (Bool × Int) )
      let linked_n : Int := linked_n
      let (is_linked_mismatch, linked_match) ← (( do
        if (linked : Bool)
        then
          (do
            let linked_to : Bool := true
            let w__8 ← (( do (AArch64_BreakpointValueMatch linked_n vaddress linked_to isbreakpnt)
              ) : SailME Bool (Bool × Bool) )
            let (tup__0, tup__1) := (w__8 : (Bool × Bool))
            let linked_match : Bool := tup__0
            let is_linked_mismatch : Bool := tup__1
            (pure ((is_linked_mismatch, linked_match))))
        else (pure ((is_linked_mismatch, linked_match))) ) : SailME Bool (Bool × Bool) )
      (pure (((priv_match && ss_match) && (((! linked) || ((! is_linked_mismatch) && linked_match)) || (is_linked_mismatch && (! linked_match)))))))


end ArmFull.Functions
