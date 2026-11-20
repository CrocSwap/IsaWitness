module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0154
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0194
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0216
public import ArmFull.Fn.M0235
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0237 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_N : Nat, k_branch_conditional : Bool, k_N ≥ 0 -/
def BranchTo (target : (BitVec k_N)) (branch_type : BranchType) (branch_conditional : Bool) : SailM Unit := do
  (Hint_Branch branch_type)
  if (((Sail.BitVec.length target) == 32) : Bool)
  then
    (do
      let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:6804.29-6804.30"
      writeReg _PC (Sail.BitVec.zeroExtend target 64))
  else
    (do
      let w__2 ← (( do
        if ((((Sail.BitVec.length target) == 64) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
            (pure (((! w__1) : Bool))))
        else (pure false) ) : SailM Bool )
      ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:6807.50-6807.51"
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      let target_vaddress ← (( do
        (AArch64_BranchAddr (Sail.BitVec.extractLsb target 63 0) w__3.EL) ) : SailM (BitVec 64) )
      let w__5 ← (( do
        (pure ((← do
              (HaveBRBExt ())) && (((BEq.beq branch_type BranchType_DIR) || ((BEq.beq branch_type
                  BranchType_INDIR) || ((BEq.beq branch_type BranchType_DIRCALL) || ((BEq.beq
                      branch_type BranchType_INDCALL) || (BEq.beq branch_type BranchType_RET))))) : Bool)))
        ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          (BRBEBranch branch_type branch_conditional target_vaddress))
      else (pure (()))
      let branch_taken : Bool := true
      let w__6 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          (SPEBranch target branch_type branch_conditional branch_taken))
      else (pure (()))
      let _ : Unit := (sail_branch_announce 64 target_vaddress)
      writeReg _PC target_vaddress)
  writeReg __BranchTaken true


def gic_read_ram (offset : (BitVec 16)) : SailM (BitVec 32) := do
  let accdesc ← (( do (CreateAccDescGPR MemOp_LOAD false true false) ) : SailM AccessDescriptor )
  let pa := (Sail.BitVec.zeroExtend (GIC_BASE +++ offset) 56)
  let w__0 ← (( do (sail_mem_read (read_request accdesc none 4 (Sail.BitVec.zeroExtend pa 64) pa))
    ) : SailM (Result ((BitVec (8 * 4)) × (Option Bool)) Fault) )
  match w__0 with
  | .Ok (value, _) => (pure (value))
  | .Err _ =>
    (do
      ArmFull.assert false "sail-inputs/08-devices.sail:134.18-134.19"
      throw Error.Exit)


/-- Type quantifiers: k_data : Bool -/
def Strip (A : (BitVec 64)) (data : Bool) : SailM (BitVec 64) := do
  let original_ptr ← (( do (undefined_bitvector_at (← occLabel 1292) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (EffectiveTBI A (! data) w__0.EL) ) : SailM (BitVec 1) )
  let tbi : Bool := (w__1 == 1#1)
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (EffectiveMTX A (! data) w__2.EL) ) : SailM (BitVec 1) )
  let mtx : Bool := (w__3 == 1#1)
  let bottom_PAC_bit ← (( do
    (CalculateBottomPACBit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access A 55)]))) ) : SailM Int
    )
  let extfield : (BitVec 64) :=
    (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access A 55)])) 64)
  if ((tbi && (bottom_PAC_bit ≥b 55)) : Bool)
  then (pure (A))
  else
    (do
      if (tbi : Bool)
      then
        (do
          ArmFull.assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21580.90-21580.91"
          ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21581.80-21581.81"
          let original_ptr : (BitVec 64) :=
            (Sail.BitVec.castWidth (((Sail.BitVec.extractLsb A 63 56) +++ (Sail.BitVec.extractLsb
                  extfield (Sail.Int.toNatChecked (((56 -i bottom_PAC_bit) -i 1))) 0)) +++ (Sail.BitVec.extractLsb
                A (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
          (pure (original_ptr)))
      else
        (do
          if (mtx : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21584.90-21584.91"
              ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21585.80-21585.81"
              let original_ptr : (BitVec 64) :=
                (Sail.BitVec.castWidth ((((Sail.BitVec.extractLsb extfield 63 60) +++ (Sail.BitVec.extractLsb
                        A 59 56)) +++ (Sail.BitVec.extractLsb extfield
                      (Sail.Int.toNatChecked (((56 -i bottom_PAC_bit) -i 1))) 0)) +++ (Sail.BitVec.extractLsb
                    A (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
              (pure (original_ptr)))
          else
            (do
              ArmFull.assert ((0 ≤b ((64 -i bottom_PAC_bit) -i 1)) && (((64 -i bottom_PAC_bit) -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21588.90-21588.91"
              ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21589.80-21589.81"
              let original_ptr : (BitVec 64) :=
                (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb extfield
                    (Sail.Int.toNatChecked (((64 -i bottom_PAC_bit) -i 1))) 0) +++ (Sail.BitVec.extractLsb
                    A (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
              (pure (original_ptr)))))


/-- Type quantifiers: k_data : Bool -/
def AddPAC (ptr : (BitVec 64)) (modifier : (BitVec 64)) (K : (BitVec 128)) (data : Bool) : SailM (BitVec 64) := do
  let result ← (( do (undefined_bitvector_at (← occLabel 1296) 64) ) : SailM (BitVec 64) )
  let ext_ptr ← (( do (undefined_bitvector_at (← occLabel 1297) 64) ) : SailM (BitVec 64) )
  let selbit ← (( do (undefined_bitvector_at (← occLabel 1298) 1) ) : SailM (BitVec 1) )
  let isgeneric : Bool := false
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (EffectiveTBI ptr (! data) w__0.EL) ) : SailM (BitVec 1) )
  let tbi : Bool := (w__1 == 1#1)
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (EffectiveMTX ptr (! data) w__2.EL) ) : SailM (BitVec 1) )
  let mtx : Bool := (w__3 == 1#1)
  let top_bit : Nat :=
    if (tbi : Bool)
    then 55
    else 63
  let w__4 ← (( do (PtrHasUpperAndLowerAddRanges ()) ) : SailM Bool )
  let selbit ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__7 ← (( do
          if ((← do
               let w__5 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
               (pure (((w__5 == EL1) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__6 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
              (pure (((w__6 == EL2) : Bool)))) ) : SailM Bool )
        ArmFull.assert w__7 "sail-inputs/03-v8_base.sail:21727.80-21727.81"
        let w__8 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
        if ((w__8 == EL1) : Bool)
        then
          (do
            if (data : Bool)
            then
              (do
                let w__11 ← (( do
                  if ((← do
                       let w__9 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                       (pure ((((_get_TCR_EL1_Type_TBI1 w__9) == 1#1) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__10 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                      (pure ((((_get_TCR_EL1_Type_TBI0 w__10) == 1#1) : Bool)))) ) : SailM Bool )
                let selbit : (BitVec 1) :=
                  if (w__11 : Bool)
                  then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 55)]))
                  else (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 63)]))
                (pure (selbit)))
            else
              (do
                let w__18 ← (( do
                  if ((← do
                       if ((← do
                            let w__12 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                            (pure ((((_get_TCR_EL1_Type_TBI1 w__12) == 1#1) : Bool)))) : Bool)
                       then
                         (do
                           let w__13 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                           (pure ((((_get_TCR_EL1_Type_TBID1 w__13) == 0#1) : Bool))))
                       else (pure false)) : Bool)
                  then (pure true)
                  else
                    (do
                      if ((← do
                           let w__15 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                           (pure ((((_get_TCR_EL1_Type_TBI0 w__15) == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          let w__16 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
                          (pure ((((_get_TCR_EL1_Type_TBID0 w__16) == 0#1) : Bool))))
                      else (pure false)) ) : SailM Bool )
                let selbit : (BitVec 1) :=
                  if (w__18 : Bool)
                  then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 55)]))
                  else (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 63)]))
                (pure (selbit))))
        else
          (do
            if (data : Bool)
            then
              (do
                let w__21 ← (( do
                  if ((← do
                       let w__19 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                       (pure ((((_get_TCR_EL2_Type_TBI1 w__19) == 1#1) : Bool)))) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__20 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_TCR_EL2_Type_TBI0 w__20) == 1#1) : Bool)))) ) : SailM Bool )
                let selbit : (BitVec 1) :=
                  if (w__21 : Bool)
                  then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 55)]))
                  else (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 63)]))
                (pure (selbit)))
            else
              (do
                let w__28 ← (( do
                  if ((← do
                       if ((← do
                            let w__22 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                            (pure ((((_get_TCR_EL2_Type_TBI1 w__22) == 1#1) : Bool)))) : Bool)
                       then
                         (do
                           let w__23 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_TCR_EL2_Type_TBID1 w__23) == 0#1) : Bool))))
                       else (pure false)) : Bool)
                  then (pure true)
                  else
                    (do
                      if ((← do
                           let w__25 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                           (pure ((((_get_TCR_EL2_Type_TBI0 w__25) == 1#1) : Bool)))) : Bool)
                      then
                        (do
                          let w__26 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_TCR_EL2_Type_TBID0 w__26) == 0#1) : Bool))))
                      else (pure false)) ) : SailM Bool )
                let selbit : (BitVec 1) :=
                  if (w__28 : Bool)
                  then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 55)]))
                  else (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 63)]))
                (pure (selbit)))))
    else
      (let selbit : (BitVec 1) :=
        if (tbi : Bool)
        then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 55)]))
        else (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 63)]))
      (pure (selbit))) ) : SailM (BitVec 1) )
  let w__31 ← (( do
    if ((← do
         (HaveEnhancedPAC2 ())) : Bool)
    then
      (do
        (ConstPACField ()))
    else (pure false) ) : SailM Bool )
  let selbit : (BitVec 1) :=
    if (w__31 : Bool)
    then (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ptr 55)]))
    else selbit
  let selbit := selbit
  let bottom_PAC_bit ← (( do (CalculateBottomPACBit selbit) ) : SailM Int )
  if ((tbi && (bottom_PAC_bit ≥b 55)) : Bool)
  then (pure (ptr))
  else
    (do
      let extfield : (BitVec 64) := (BitVec.replicateBits selbit 64)
      let ext_ptr ← (( do
        if (tbi : Bool)
        then
          (do
            ArmFull.assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21770.90-21770.91"
            ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21771.80-21771.81"
            let ext_ptr : (BitVec 64) :=
              (Sail.BitVec.castWidth (((Sail.BitVec.extractLsb ptr 63 56) +++ (Sail.BitVec.extractLsb
                    extfield (Sail.Int.toNatChecked (((56 -i bottom_PAC_bit) -i 1))) 0)) +++ (Sail.BitVec.extractLsb
                  ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
            (pure (ext_ptr)))
        else
          (do
            if (mtx : Bool)
            then
              (do
                ArmFull.assert ((0 ≤b ((56 -i bottom_PAC_bit) -i 1)) && (((56 -i bottom_PAC_bit) -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21774.90-21774.91"
                ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21775.80-21775.81"
                let ext_ptr : (BitVec 64) :=
                  (Sail.BitVec.castWidth ((((Sail.BitVec.extractLsb extfield 63 60) +++ (Sail.BitVec.extractLsb
                          ptr 59 56)) +++ (Sail.BitVec.extractLsb extfield
                        (Sail.Int.toNatChecked (((56 -i bottom_PAC_bit) -i 1))) 0)) +++ (Sail.BitVec.extractLsb
                      ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
                (pure (ext_ptr)))
            else
              (do
                ArmFull.assert ((0 ≤b ((64 -i bottom_PAC_bit) -i 1)) && (((64 -i bottom_PAC_bit) -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21778.90-21778.91"
                ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21779.80-21779.81"
                let ext_ptr : (BitVec 64) :=
                  (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb extfield
                      (Sail.Int.toNatChecked (((64 -i bottom_PAC_bit) -i 1))) 0) +++ (Sail.BitVec.extractLsb
                      ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
                (pure (ext_ptr)))) ) : SailM (BitVec 64) )
      let PAC ← (( do
        (ComputePAC ext_ptr modifier (Sail.BitVec.extractLsb K 127 64)
          (Sail.BitVec.extractLsb K 63 0) isgeneric) ) : SailM (BitVec 64) )
      let unusedbits_mask : (BitVec 64) := (Zeros (n := 64))
      ArmFull.assert ((0 ≤b bottom_PAC_bit) && (bottom_PAC_bit ≤b 54)) "sail-inputs/03-v8_base.sail:21784.69-21784.70"
      let unusedbits_mask : (BitVec 64) :=
        (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange unusedbits_mask 54
          (Sail.Int.toNatChecked (bottom_PAC_bit))
          (Sail.BitVec.castWidth (Ones
            (n := (Sail.Int.toNatChecked (((54 -i bottom_PAC_bit) +i 1))))))))
      let unusedbits_mask : (BitVec 64) :=
        if (tbi : Bool)
        then (Sail.BitVec.updateSubrange unusedbits_mask 63 56 (Ones (n := 8)))
        else
          (if (mtx : Bool)
          then (Sail.BitVec.updateSubrange unusedbits_mask 63 60 (Ones (n := 4)))
          else unusedbits_mask)
      let PAC ← (( do
        if (((! (IsZero (ptr &&& unusedbits_mask))) && ((ptr &&& unusedbits_mask) != unusedbits_mask)) : Bool)
        then
          (do
            let w__32 ← (( do (HaveEnhancedPAC ()) ) : SailM Bool )
            if (w__32 : Bool)
            then (pure (0x0000000000000000#64))
            else
              (do
                let w__33 ← (( do (HaveEnhancedPAC2 ()) ) : SailM Bool )
                let PAC : (BitVec 64) :=
                  if ((! w__33) : Bool)
                  then
                    (BitVec.update PAC (Sail.Int.toNatChecked ((top_bit -i 1)))
                      (Bit
                        (Complement.complement
                          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access PAC
                              (Sail.Int.toNatChecked ((top_bit -i 1))))])))))
                  else PAC
                (pure (PAC))))
        else (pure (PAC)) ) : SailM (BitVec 64) )
      let w__34 ← (( do (HaveEnhancedPAC2 ()) ) : SailM Bool )
      if ((! w__34) : Bool)
      then
        (do
          if (tbi : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21800.84-21800.85"
              let result : (BitVec 64) :=
                (Sail.BitVec.castWidth ((((Sail.BitVec.extractLsb ptr 63 56) +++ selbit) +++ (Sail.BitVec.extractLsb
                      PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) +++ (Sail.BitVec.extractLsb
                    ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
              (pure (result)))
          else
            (do
              ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21803.84-21803.85"
              let result : (BitVec 64) :=
                (Sail.BitVec.castWidth ((((Sail.BitVec.extractLsb PAC 63 56) +++ selbit) +++ (Sail.BitVec.extractLsb
                      PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) +++ (Sail.BitVec.extractLsb
                    ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
              ArmFull.assert (! mtx) "sail-inputs/03-v8_base.sail:21805.32-21805.33"
              (pure (result))))
      else
        (do
          if (tbi : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21809.84-21809.85"
              let result : (BitVec 64) :=
                (Sail.BitVec.castWidth ((((Sail.BitVec.extractLsb ptr 63 56) +++ selbit) +++ ((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                        ptr 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) ^^^ (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                        PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))))) +++ (Sail.BitVec.extractLsb
                    ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
              (pure (result)))
          else
            (do
              if (mtx : Bool)
              then
                (do
                  ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21812.84-21812.85"
                  let result : (BitVec 64) :=
                    (Sail.BitVec.castWidth ((((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                ptr 63 60)) ^^^ (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                PAC 63 60))) +++ (Sail.BitVec.extractLsb ptr 59 56)) +++ selbit) +++ ((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                            ptr 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) ^^^ (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                            PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))))) +++ (Sail.BitVec.extractLsb
                        ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
                  (pure (result)))
              else
                (do
                  ArmFull.assert ((0 ≤b (bottom_PAC_bit -i 1)) && ((bottom_PAC_bit -i 1) <b 64)) "sail-inputs/03-v8_base.sail:21815.84-21815.85"
                  let result : (BitVec 64) :=
                    (Sail.BitVec.castWidth (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                              ptr 63 56)) ^^^ (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                              PAC 63 56))) +++ selbit) +++ ((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((54 : Int) -i (bottom_PAC_bit : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                            ptr 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))) ^^^ (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                            PAC 54 (Sail.Int.toNatChecked (bottom_PAC_bit)))))) +++ (Sail.BitVec.extractLsb
                        ptr (Sail.Int.toNatChecked ((bottom_PAC_bit -i 1))) 0)))
                  (pure (result))))))


/-- Type quantifiers: k_isbreakpnt : Bool, k_linked_to : Bool, n_in : Int -/
def AArch64_BreakpointValueMatch (n_in : Int) (vaddress : (BitVec 64)) (linked_to : Bool) (isbreakpnt : Bool) : SailM (Bool × Bool) := SailME.run do
  let n : Int := n_in
  let c ← (( do (undefined_Constraint (← occLabel 1373) ()) ) : SailME (Bool × Bool) Constraint
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
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || (BEq.beq c Constraint_UNKNOWN)) "sail-inputs/03-v8_base.sail:23268.65-23268.66"
        if ((BEq.beq c Constraint_DISABLED) : Bool)
        then
          (do
            SailME.throw ((false, false) : (Bool × Bool)))
        else (pure (()))
        (pure ((c, n))))
    else (pure ((c, n))) ) : SailME (Bool × Bool) (Constraint × Int) )
  let n : Int := n
  ArmFull.assert ((0 ≤b n) && (n <b 64)) "sail-inputs/03-v8_base.sail:23275.42-23275.43"
  let w__3 ← (( do (IsBreakpointEnabled (Sail.Int.toNatChecked (n))) ) : SailME (Bool × Bool)
    Bool )
  if ((! w__3) : Bool)
  then (pure ((false, false)))
  else
    (do
      let w__4 ← (( do readReg DBGBCR_EL1 ) : SailME (Bool × Bool) (Vector (BitVec 64) 64) )
      let dbgtype : (BitVec 4) :=
        (_get_DBGBCR_EL1_Type_BT (GetElem?.getElem! w__4 (Sail.Int.toNatChecked (n))))
      let w__5 ← (( do (HaveFeatABLE ()) ) : SailME (Bool × Bool) Bool )
      let bt2 ← (( do
        if (w__5 : Bool)
        then
          (do
            let w__6 ← (( do readReg DBGBCR_EL1 ) : SailME (Bool × Bool) (Vector (BitVec 64) 64)
              )
            (pure ((_get_DBGBCR_EL1_Type_BT2 (GetElem?.getElem! w__6 (Sail.Int.toNatChecked (n)))))))
        else (pure (0#1)) ) : SailME (Bool × Bool) (BitVec 1) )
      let w__7 ← (( do (AArch64_ReservedBreakpointType n bt2 dbgtype) ) : SailME (Bool × Bool)
        (Constraint × (BitVec 1) × (BitVec 4)) )
      let (tup__0, tup__1, tup__2) := (w__7 : (Constraint × (BitVec 1) × (BitVec 4)))
      let c : Constraint := tup__0
      let bt2 : (BitVec 1) := tup__1
      let dbgtype : (BitVec 4) := tup__2
      if ((BEq.beq c Constraint_DISABLED) : Bool)
      then (pure ((false, false)))
      else
        (do
          let b__8 := dbgtype
          let match_addr : Bool :=
            (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__8 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__8 1 1)) == (0#1 : (BitVec 1)))) : Bool)
            then true
            else false : Bool)
          let b__7 := dbgtype
          let mismatch : Bool :=
            (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__7 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
            then true
            else false : Bool)
          let b__6 := dbgtype
          let match_vmid : Bool :=
            (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__6 3 2)) == (0b10#2 : (BitVec 2))) : Bool)
            then true
            else false : Bool)
          let b__5 := dbgtype
          let match_cid : Bool :=
            (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__5 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
            then true
            else false : Bool)
          let b__3 := dbgtype
          let match_cid1 : Bool :=
            (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b101#3 : (BitVec 3))) : Bool)
            then true
            else
              (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__3 2 1)) == (0b11#2 : (BitVec 2))) : Bool)
              then true
              else false) : Bool)
          let b__2 := dbgtype
          let match_cid2 : Bool :=
            (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 3 2)) == (0b11#2 : (BitVec 2))) : Bool)
            then true
            else false : Bool)
          let linking_enabled : Bool :=
            ((let b__0 := dbgtype
              (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 1 0)) == (0b11#2 : (BitVec 2))) : Bool)
              then true
              else
                (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                         b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
                then true
                else false) : Bool)) || (bt2 == 1#1))
          if ((linked_to && (! linking_enabled)) : Bool)
          then (pure ((false, false)))
          else
            (do
              if ((((! linked_to) && linking_enabled) && (! match_addr)) : Bool)
              then (pure ((false, false)))
              else
                (do
                  if (((linked_to && match_addr) && isbreakpnt) : Bool)
                  then
                    (do
                      let w__8 ← (( do
                        (ConstrainUnpredictableBool Unpredictable_BPLINKEDADDRMATCH) ) : SailME
                        (Bool × Bool) Bool )
                      if ((! w__8) : Bool)
                      then
                        (do
                          SailME.throw ((false, false) : (Bool × Bool)))
                      else (pure (())))
                  else (pure (()))
                  let w__10 ← (( do
                    if (mismatch : Bool)
                    then
                      (do
                        (UsingAArch32 ()))
                    else (pure false) ) : SailME (Bool × Bool) Bool )
                  if (w__10 : Bool)
                  then (pure ((false, false)))
                  else
                    (do
                      let bvr_match : Bool := false
                      let bxvr_match : Bool := false
                      let mask ← (( do (undefined_int_at (← occLabel 1374) ()) ) : SailME
                        (Bool × Bool) Int )
                      let w__11 ← (( do (HaveFeatABLE ()) ) : SailME (Bool × Bool) Bool )
                      let mask ← (( do
                        if (w__11 : Bool)
                        then
                          (do
                            let w__12 ← (( do readReg DBGBCR_EL1 ) : SailME (Bool × Bool)
                              (Vector (BitVec 64) 64) )
                            let mask : Int :=
                              ((BitVec.toNat
                                (_get_DBGBCR_EL1_Type_MASK
                                  (GetElem?.getElem! w__12 (Sail.Int.toNatChecked (n))))) : Int)
                            let mask ← (( do
                              if (((mask == 1) || (mask == 2)) : Bool)
                              then
                                (do
                                  let w__13 ← (( do
                                    (ConstrainUnpredictableInteger 3 31 Unpredictable_RESBPMASK) ) :
                                    SailME (Bool × Bool) (Constraint × Int) )
                                  let (tup__0, tup__1) := (w__13 : (Constraint × Int))
                                  let c : Constraint := tup__0
                                  let mask : Int := tup__1
                                  ArmFull.assert ((BEq.beq c Constraint_DISABLED) || ((BEq.beq c
                                        Constraint_NONE) || (BEq.beq c Constraint_UNKNOWN))) "sail-inputs/03-v8_base.sail:23337.92-23337.93"
                                  match c with
                                  | .Constraint_DISABLED =>
                                    (do
                                      SailME.throw ((false, false) : (Bool × Bool))
                                      (pure (mask)))
                                  | .Constraint_NONE => (pure (0))
                                  | _ => (pure (mask)))
                              else (pure (mask)) ) : SailME (Bool × Bool) Int )
                            if ((mask != 0) : Bool)
                            then
                              (do
                                let w__17 ← (( do
                                  if (((match_cid || match_cid1) || match_cid2) : Bool)
                                  then (pure true)
                                  else
                                    (do
                                      if ((← do
                                           let w__14 ← (( do readReg DBGBCR_EL1 ) : SailME
                                             (Bool × Bool) (Vector (BitVec 64) 64) )
                                           (pure ((((_get_DBGBCR_EL1_Type_BAS
                                                 (GetElem?.getElem! w__14
                                                   (Sail.Int.toNatChecked (n)))) != 0b1111#4) : Bool)))) : Bool)
                                      then
                                        (do
                                          (HaveAArch32 ()))
                                      else (pure false)) ) : SailME (Bool × Bool) Bool )
                                if (w__17 : Bool)
                                then
                                  (do
                                    let w__18 ← (( do
                                      (ConstrainUnpredictableBool Unpredictable_BPMASK) ) : SailME
                                      (Bool × Bool) Bool )
                                    if ((! w__18) : Bool)
                                    then
                                      (do
                                        SailME.throw ((false, false) : (Bool × Bool)))
                                    else (pure (())))
                                else (pure (())))
                            else
                              (do
                                if (mismatch : Bool)
                                then
                                  (do
                                    SailME.throw ((false, false) : (Bool × Bool)))
                                else (pure (())))
                            (pure (mask)))
                        else (pure (0)) ) : SailME (Bool × Bool) Int )
                      let mask : Int := mask
                      let bvr_match ← (( do
                        if (match_addr : Bool)
                        then
                          (do
                            let byte_select_match ← (( do
                              (undefined_bool_at (← occLabel 1375) ()) ) : SailME (Bool × Bool)
                              Bool )
                            let byte : Int := (BitVec.toNat (Sail.BitVec.extractLsb vaddress 1 0))
                            let w__19 ← (( do (HaveAArch32 ()) ) : SailME (Bool × Bool) Bool )
                            let byte_select_match ← (( do
                              if (w__19 : Bool)
                              then
                                (do
                                  ArmFull.assert ((byte == 0) || (byte == 2)) "sail-inputs/03-v8_base.sail:23370.40-23370.41"
                                  let w__20 ← (( do readReg DBGBCR_EL1 ) : SailME (Bool × Bool)
                                    (Vector (BitVec 64) 64) )
                                  let byte_select_match :=
                                    (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                          (_get_DBGBCR_EL1_Type_BAS
                                            (GetElem?.getElem! w__20 (Sail.Int.toNatChecked (n))))
                                          (Sail.Int.toNatChecked (byte)))])) == 1#1) : Bool)
                                  (pure (byte_select_match)))
                              else
                                (do
                                  ArmFull.assert (byte == 0) "sail-inputs/03-v8_base.sail:23373.28-23373.29"
                                  (pure (true))) ) : SailME (Bool × Bool) Bool )
                            let top ← (( do (DebugAddrTop ()) ) : SailME (Bool × Bool) Int )
                            let bottom : Nat := 2
                            let w__26 ← (( do
                              if ((← do
                                   if ((← do
                                        if (((top <b 55) : Bool) : Bool)
                                        then
                                          (do
                                            let w__21 ← (( do readReg DBGBVR_EL1 ) : SailME
                                              (Bool × Bool) (Vector (BitVec 64) 64) )
                                            (pure (((! (is_ones_subrange
                                                  (GetElem?.getElem! w__21
                                                    (Sail.Int.toNatChecked (n))) 63 top)) : Bool))))
                                        else (pure false)) : Bool)
                                   then
                                     (do
                                       let w__23 ← (( do readReg DBGBVR_EL1 ) : SailME
                                         (Bool × Bool) (Vector (BitVec 64) 64) )
                                       (pure (((! (is_zero_subrange
                                             (GetElem?.getElem! w__23 (Sail.Int.toNatChecked (n)))
                                             63 top)) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  (ConstrainUnpredictableBool Unpredictable_DBGxVR_RESS))
                              else (pure false) ) : SailME (Bool × Bool) Bool )
                            let top : Int :=
                              if (w__26 : Bool)
                              then 63
                              else top
                            let top : Int := top
                            if ((mask >b bottom) : Bool)
                            then
                              (do
                                ArmFull.assert ((0 ≤b mask) && ((mask ≤b top) && (top <b 64))) "sail-inputs/03-v8_base.sail:23383.71-23383.72"
                                let w__28 ← (( do
                                  (pure ((← do
                                        let w__27 ← (( do readReg DBGBVR_EL1 ) : SailME
                                          (Bool × Bool) (Vector (BitVec 64) 64) )
                                        (pure ((((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((top : Int) -i (mask : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                                              vaddress (Sail.Int.toNatChecked (top))
                                              (Sail.Int.toNatChecked (mask)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                                              (GetElem?.getElem! w__27 (Sail.Int.toNatChecked (n)))
                                              (Sail.Int.toNatChecked (top))
                                              (Sail.Int.toNatChecked (mask))))) : Bool)))) && (byte_select_match : Bool)))
                                  ) : SailME (Bool × Bool) Bool )
                                let bvr_match := (w__28 : Bool)
                                let w__30 ← (( do
                                  if ((bvr_match : Bool) : Bool)
                                  then
                                    (do
                                      let w__29 ← (( do readReg DBGBVR_EL1 ) : SailME
                                        (Bool × Bool) (Vector (BitVec 64) 64) )
                                      (pure (((! (is_zero_subrange
                                            (GetElem?.getElem! w__29 (Sail.Int.toNatChecked (n)))
                                            (mask -i 1) bottom)) : Bool))))
                                  else (pure false) ) : SailME (Bool × Bool) Bool )
                                if (w__30 : Bool)
                                then
                                  (do
                                    (ConstrainUnpredictableBool Unpredictable_BPMASKEDBITS))
                                else (pure (bvr_match)))
                            else
                              (do
                                ArmFull.assert ((0 ≤b bottom) && ((bottom ≤b top) && (top <b 64))) "sail-inputs/03-v8_base.sail:23390.75-23390.76"
                                (pure ((← do
                                      let w__32 ← (( do readReg DBGBVR_EL1 ) : SailME
                                        (Bool × Bool) (Vector (BitVec 64) 64) )
                                      (pure ((((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((top : Int) -i (bottom : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
                                            vaddress (Sail.Int.toNatChecked (top)) bottom)) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                                            (GetElem?.getElem! w__32 (Sail.Int.toNatChecked (n)))
                                            (Sail.Int.toNatChecked (top)) bottom))) : Bool)))) && (byte_select_match : Bool)))))
                        else
                          (do
                            if (match_cid : Bool)
                            then
                              (do
                                let w__34 ← (( do (IsInHost ()) ) : SailME (Bool × Bool) Bool )
                                if (w__34 : Bool)
                                then
                                  (do
                                    let w__35 ← (( do readReg CONTEXTIDR_EL2 ) : SailME
                                      (Bool × Bool) (BitVec 64) )
                                    let w__36 ← (( do readReg DBGBVR_EL1 ) : SailME (Bool × Bool)
                                      (Vector (BitVec 64) 64) )
                                    let bvr_match :=
                                      (((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                          w__35 31 0)) == (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                          (GetElem?.getElem! w__36 (Sail.Int.toNatChecked (n))) 31 0))) : Bool)
                                    (pure (bvr_match)))
                                else
                                  (do
                                    if ((← do
                                         if ((← do
                                              let w__37 ← (( do readReg PSTATE ) : SailME
                                                (Bool × Bool) ProcState )
                                              (pure (((w__37.EL == EL0) : Bool)))) : Bool)
                                         then (pure true)
                                         else
                                           (do
                                             let w__38 ← (( do readReg PSTATE ) : SailME
                                               (Bool × Bool) ProcState )
                                             (pure (((w__38.EL == EL1) : Bool))))) : Bool)
                                    then
                                      (do
                                        let w__40 ← (( do readReg CONTEXTIDR_EL1 ) : SailME
                                          (Bool × Bool) (BitVec 64) )
                                        let w__41 ← (( do readReg DBGBVR_EL1 ) : SailME
                                          (Bool × Bool) (Vector (BitVec 64) 64) )
                                        (pure ((((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                              w__40 31 0)) == (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                              (GetElem?.getElem! w__41 (Sail.Int.toNatChecked (n)))
                                              31 0))) : Bool))))
                                    else (pure false)))
                            else
                              (do
                                if (match_cid1 : Bool)
                                then
                                  (do
                                    if ((← do
                                         if ((← do
                                              if ((← do
                                                   let w__43 ← (( do readReg PSTATE ) : SailME
                                                     (Bool × Bool) ProcState )
                                                   (pure (((w__43.EL == EL0) : Bool)))) : Bool)
                                              then (pure true)
                                              else
                                                (do
                                                  let w__44 ← (( do readReg PSTATE ) : SailME
                                                    (Bool × Bool) ProcState )
                                                  (pure (((w__44.EL == EL1) : Bool))))) : Bool)
                                         then
                                           (do
                                             let w__46 ← (( do (IsInHost ()) ) : SailME
                                               (Bool × Bool) Bool )
                                             (pure (((! w__46) : Bool))))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__48 ← (( do readReg CONTEXTIDR_EL1 ) : SailME
                                          (Bool × Bool) (BitVec 64) )
                                        let w__49 ← (( do readReg DBGBVR_EL1 ) : SailME
                                          (Bool × Bool) (Vector (BitVec 64) 64) )
                                        (pure ((((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                              w__48 31 0)) == (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                              (GetElem?.getElem! w__49 (Sail.Int.toNatChecked (n)))
                                              31 0))) : Bool))))
                                    else (pure false))
                                else (pure (bvr_match)))) ) : SailME (Bool × Bool) Bool )
                      let bxvr_match ← (( do
                        if (match_vmid : Bool)
                        then
                          (do
                            let vmid ← (( do (undefined_bitvector_at (← occLabel 1376) 16) ) :
                              SailME (Bool × Bool) (BitVec 16) )
                            let bvr_vmid ← (( do (undefined_bitvector_at (← occLabel 1377) 16) )
                              : SailME (Bool × Bool) (BitVec 16) )
                            let w__53 ← (( do
                              if ((← do
                                   let w__51 ← (( do (Have16bitVMID ()) ) : SailME (Bool × Bool)
                                     Bool )
                                   (pure (((! w__51) : Bool)))) : Bool)
                              then (pure true)
                              else
                                (do
                                  let w__52 ← (( do readReg VTCR_EL2 ) : SailME (Bool × Bool)
                                    (BitVec 64) )
                                  (pure ((((_get_VTCR_EL2_Type_VS w__52) == 0#1) : Bool)))) ) :
                              SailME (Bool × Bool) Bool )
                            let (bvr_vmid, vmid) ← (( do
                              if (w__53 : Bool)
                              then
                                (do
                                  let w__54 ← (( do (VTTBR_EL2_read ()) ) : SailME (Bool × Bool)
                                    (BitVec 128) )
                                  let vmid :=
                                    ((Sail.BitVec.zeroExtend
                                      (Sail.BitVec.extractLsb (_get_VTTBR_EL2_Type_VMID w__54) 7 0)
                                      16) : (BitVec 16))
                                  let w__55 ← (( do readReg DBGBVR_EL1 ) : SailME (Bool × Bool)
                                    (Vector (BitVec 64) 64) )
                                  let bvr_vmid :=
                                    ((Sail.BitVec.zeroExtend
                                      (Sail.BitVec.extractLsb
                                        (GetElem?.getElem! w__55 (Sail.Int.toNatChecked (n))) 39 32)
                                      16) : (BitVec 16))
                                  (pure ((bvr_vmid, vmid))))
                              else
                                (do
                                  let w__56 ← (( do (VTTBR_EL2_read ()) ) : SailME (Bool × Bool)
                                    (BitVec 128) )
                                  let vmid := ((_get_VTTBR_EL2_Type_VMID w__56) : (BitVec 16))
                                  let w__57 ← (( do readReg DBGBVR_EL1 ) : SailME (Bool × Bool)
                                    (Vector (BitVec 64) 64) )
                                  let bvr_vmid :=
                                    ((Sail.BitVec.extractLsb
                                      (GetElem?.getElem! w__57 (Sail.Int.toNatChecked (n))) 47 32) : (BitVec 16))
                                  (pure ((bvr_vmid, vmid)))) ) : SailME (Bool × Bool)
                              ((BitVec 16) × (BitVec 16)) )
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 let w__58 ← (( do readReg PSTATE ) : SailME
                                                   (Bool × Bool) ProcState )
                                                 (pure (((w__58.EL == EL0) : Bool)))) : Bool)
                                            then (pure true)
                                            else
                                              (do
                                                let w__59 ← (( do readReg PSTATE ) : SailME
                                                  (Bool × Bool) ProcState )
                                                (pure (((w__59.EL == EL1) : Bool))))) : Bool)
                                       then
                                         (do
                                           (EL2Enabled ()))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__63 ← (( do (IsInHost ()) ) : SailME (Bool × Bool)
                                        Bool )
                                      (pure (((! w__63) : Bool))))
                                  else (pure false)) && ((vmid == bvr_vmid) : Bool))))
                        else
                          (do
                            if (match_cid2 : Bool)
                            then
                              (do
                                if ((← do
                                     if ((← do
                                          let w__66 ← (( do readReg PSTATE ) : SailME
                                            (Bool × Bool) ProcState )
                                          (pure (((w__66.EL != EL3) : Bool)))) : Bool)
                                     then
                                       (do
                                         (EL2Enabled ()))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__69 ← (( do readReg DBGBVR_EL1 ) : SailME (Bool × Bool)
                                      (Vector (BitVec 64) 64) )
                                    let w__70 ← (( do readReg CONTEXTIDR_EL2 ) : SailME
                                      (Bool × Bool) (BitVec 64) )
                                    (pure ((((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                          (GetElem?.getElem! w__69 (Sail.Int.toNatChecked (n))) 63
                                          32)) == (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                                          w__70 31 0))) : Bool))))
                                else (pure false))
                            else (pure (bxvr_match))) ) : SailME (Bool × Bool) Bool )
                      let bvr_match_valid : Bool := ((match_addr || match_cid) || match_cid1)
                      let bxvr_match_valid : Bool := (match_vmid || match_cid2)
                      let value_match_name : Bool :=
                        (((! bxvr_match_valid) || bxvr_match) && ((! bvr_match_valid) || bvr_match))
                      (pure ((value_match_name, mismatch))))))))


end ArmFull.Functions
