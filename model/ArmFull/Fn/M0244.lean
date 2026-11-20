module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0153
public import ArmFull.Fn.M0166
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M0174
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0237
public import ArmFull.Fn.M0242
public import ArmFull.Fn.M0243 set_option backward.proofsInPublic true @[expose] public section

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

def GPTWalk (pa : (BitVec 56)) (accdesc : AccessDescriptor) : SailM (GPCFRecord × GPTEntry) := SailME.run do
  let gpi_index ← (( do (undefined_int_at (← occLabel 1233) ()) ) : SailME
    (GPCFRecord × GPTEntry) Int )
  let gpttlbline ← (( do (undefined_GPTTLBLine (← occLabel 1234) ()) ) : SailME
    (GPCFRecord × GPTEntry) GPTTLBLine )
  let w__0 ← (( do readReg GPCCR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let pgs ← (( do (DecodePGS (_get_GPCCR_EL3_Type_PGS w__0)) ) : SailME (GPCFRecord × GPTEntry)
    PGSe )
  let w__1 ← (( do readReg __tlb_enabled ) : SailME (GPCFRecord × GPTEntry) Bool )
  if (w__1 : Bool)
  then
    (do
      let gpttlbline ← (( do (GPTTLBLookup pa pgs) ) : SailME (GPCFRecord × GPTEntry) GPTTLBLine
        )
      if (gpttlbline.valid_name : Bool)
      then
        (do
          let w__2 ← (( do (GPCNoFault ()) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
          SailME.throw ((w__2, gpttlbline.gpt_entry) : (GPCFRecord × GPTEntry)))
      else (pure (())))
  else (pure (()))
  let w__3 ← (( do readReg GPTBR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let base : (BitVec 56) :=
    (Sail.BitVec.zeroExtend ((_get_GPTBR_EL3_Type_BADDR w__3) +++ (Zeros (n := 12))) 56)
  let pps ← (( do (DecodePPS ()) ) : SailME (GPCFRecord × GPTEntry) Int )
  let l0sz ← (( do (GPTL0Size ()) ) : SailME (GPCFRecord × GPTEntry) Int )
  let alignment : Int := (Max.max ((pps -i l0sz) +i 3) 12)
  ArmFull.assert (56 ≥b alignment) "sail-inputs/03-v8_base.sail:19822.39-19822.40"
  let base : (BitVec 56) :=
    (base &&& (Sail.BitVec.castWidth (m := 56) (Complement.complement
        (Sail.BitVec.zeroExtend (Ones (n := (Sail.Int.toNatChecked (alignment)))) 56))))
  let gptaccdesc ← (( do (CreateAccDescGPTW accdesc) ) : SailME (GPCFRecord × GPTEntry)
    AccessDescriptor )
  let gptaddrdesc ← (( do (undefined_AddressDescriptor (← occLabel 1235) ()) ) : SailME
    (GPCFRecord × GPTEntry) AddressDescriptor )
  let w__4 ← (( do readReg GPCCR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let w__5 ← (( do readReg GPCCR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let w__6 ← (( do readReg GPCCR_EL3 ) : SailME (GPCFRecord × GPTEntry) (BitVec 64) )
  let w__7 ← (( do
    (WalkMemAttrs (_get_GPCCR_EL3_Type_SH w__4) (_get_GPCCR_EL3_Type_ORGN w__5)
      (_get_GPCCR_EL3_Type_IRGN w__6)) ) : SailME (GPCFRecord × GPTEntry) MemoryAttributes )
  let gptaddrdesc := ({ gptaddrdesc with memattrs := w__7 } : AddressDescriptor)
  let w__8 ← (( do (NoFault__1 gptaccdesc) ) : SailME (GPCFRecord × GPTEntry) FaultRecord )
  let gptaddrdesc := ({ gptaddrdesc with fault := w__8 } : AddressDescriptor)
  let gptaddrdesc : AddressDescriptor :=
    { gptaddrdesc with paddress := { gptaddrdesc.paddress with paspace := PAS_Root } }
  let w__9 ← (( do (GPTLevel0Index pa) ) : SailME (GPCFRecord × GPTEntry) Int )
  let gptaddrdesc :=
    ({ gptaddrdesc with paddress := { gptaddrdesc.paddress with address := (BitVec.addInt base
          (w__9 *i 8)) } } : AddressDescriptor)
  let level_0_entry ← (( do (undefined_bitvector_at (← occLabel 1236) 64) ) : SailME
    (GPCFRecord × GPTEntry) (BitVec 64) )
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1237) ()) ) : SailME
    (GPCFRecord × GPTEntry) PhysMemRetStatus )
  let w__10 ← (( do (PhysMemRead gptaddrdesc 8 gptaccdesc none) ) : SailME
    (GPCFRecord × GPTEntry) (PhysMemRetStatus × (BitVec (8 * 8))) )
  let (tup__0, tup__1) := (w__10 : (PhysMemRetStatus × (BitVec (8 * 8))))
  let memstatus : PhysMemRetStatus := tup__0
  let level_0_entry : (BitVec 64) := tup__1
  if ((IsFault__2 memstatus) : Bool)
  then
    (do
      let w__11 ← (( do (GPCFault GPCF_EABT 0) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
      let w__12 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCFRecord × GPTEntry) GPTEntry )
      (pure ((w__11, w__12))))
  else
    (do
      let result ← (( do (undefined_GPTEntry (← occLabel 1238) ()) ) : SailME
        (GPCFRecord × GPTEntry) GPTEntry )
      let table ← (( do (undefined_GPTTable (← occLabel 1239) ()) ) : SailME
        (GPCFRecord × GPTEntry) GPTTable )
      let gpf ← (( do (undefined_GPCF (← occLabel 1240) ()) ) : SailME (GPCFRecord × GPTEntry)
        GPCF )
      let questionMark := (Sail.BitVec.extractLsb level_0_entry 3 0)
      let (gpf, result, table) ← (( do
        if ((questionMark == GPT_Block) : Bool)
        then
          (do
            let w__13 ← (( do (DecodeGPTBlock pgs level_0_entry) ) : SailME
              (GPCFRecord × GPTEntry) (GPCF × GPTEntry) )
            let (tup__0, tup__1) := (w__13 : (GPCF × GPTEntry))
            let gpf : GPCF := tup__0
            let result : GPTEntry := tup__1
            let result : GPTEntry := { result with pa := pa }
            let w__15 ← (( do
              (pure ((← do
                    readReg __tlb_enabled) && ((BEq.beq gpf GPCF_None) : Bool))) ) : SailME
              (GPCFRecord × GPTEntry) Bool )
            let _ : Unit :=
              if (w__15 : Bool)
              then (GPTTLBCache pgs result)
              else ()
            let w__16 ← (( do (GPCFault gpf 0) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
            SailME.throw ((w__16, result) : (GPCFRecord × GPTEntry))
            (pure ((gpf, result, table))))
        else
          (do
            let (gpf, table) ← (( do
              if ((questionMark == GPT_Table) : Bool)
              then
                (do
                  let w__17 ← (( do (DecodeGPTTable pgs level_0_entry) ) : SailME
                    (GPCFRecord × GPTEntry) (GPCF × GPTTable) )
                  let (tup__0, tup__1) := (w__17 : (GPCF × GPTTable))
                  let gpf : GPCF := tup__0
                  let table : GPTTable := tup__1
                  if ((bne gpf GPCF_None) : Bool)
                  then
                    (do
                      let w__18 ← (( do (GPCFault gpf 0) ) : SailME (GPCFRecord × GPTEntry)
                        GPCFRecord )
                      let w__19 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME
                        (GPCFRecord × GPTEntry) GPTEntry )
                      SailME.throw ((w__18, w__19) : (GPCFRecord × GPTEntry)))
                  else (pure (()))
                  (pure ((gpf, table))))
              else
                (do
                  let w__20 ← (( do (GPCFault GPCF_Walk 0) ) : SailME (GPCFRecord × GPTEntry)
                    GPCFRecord )
                  let w__21 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCFRecord × GPTEntry)
                    GPTEntry )
                  SailME.throw ((w__20, w__21) : (GPCFRecord × GPTEntry))
                  (pure ((gpf, table)))) ) : SailME (GPCFRecord × GPTEntry) (GPCF × GPTTable) )
            (pure ((gpf, result, table)))) ) : SailME (GPCFRecord × GPTEntry)
        (GPCF × GPTEntry × GPTTable) )
      ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb level_0_entry 3 0)) == GPT_Table) "sail-inputs/03-v8_base.sail:19859.45-19859.46"
      let w__22 ← (( do (GPTLevel1Index pa) ) : SailME (GPCFRecord × GPTEntry) Int )
      let offset : Int := (w__22 *i 8)
      let gptaddrdesc : AddressDescriptor :=
        { gptaddrdesc with paddress := { gptaddrdesc.paddress with address := (BitVec.addInt
              table.address offset) } }
      let level_1_entry ← (( do (undefined_bitvector_at (← occLabel 1241) 64) ) : SailME
        (GPCFRecord × GPTEntry) (BitVec 64) )
      let w__23 ← (( do (PhysMemRead gptaddrdesc 8 gptaccdesc none) ) : SailME
        (GPCFRecord × GPTEntry) (PhysMemRetStatus × (BitVec (8 * 8))) )
      let (tup__0, tup__1) := (w__23 : (PhysMemRetStatus × (BitVec (8 * 8))))
      let memstatus : PhysMemRetStatus := tup__0
      let level_1_entry : (BitVec 64) := tup__1
      if ((IsFault__2 memstatus) : Bool)
      then
        (do
          let w__24 ← (( do (GPCFault GPCF_EABT 1) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord
            )
          let w__25 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCFRecord × GPTEntry) GPTEntry )
          (pure ((w__24, w__25))))
      else
        (do
          let questionMark := (Sail.BitVec.extractLsb level_1_entry 3 0)
          let (gpf, result) ← (( do
            if ((questionMark == GPT_Contig) : Bool)
            then
              (do
                let w__26 ← (( do (DecodeGPTContiguous pgs level_1_entry) ) : SailME
                  (GPCFRecord × GPTEntry) (GPCF × GPTEntry) )
                let (tup__0, tup__1) := (w__26 : (GPCF × GPTEntry))
                let gpf : GPCF := tup__0
                let result : GPTEntry := tup__1
                (pure ((gpf, result))))
            else
              (do
                let gpi_index ← (( do (GPIIndex pa) ) : SailME (GPCFRecord × GPTEntry) Int )
                let w__27 ← (( do (DecodeGPTGranules pgs gpi_index level_1_entry) ) : SailME
                  (GPCFRecord × GPTEntry) (GPCF × GPTEntry) )
                let (tup__0, tup__1) := (w__27 : (GPCF × GPTEntry))
                let gpf : GPCF := tup__0
                let result : GPTEntry := tup__1
                (pure ((gpf, result)))) ) : SailME (GPCFRecord × GPTEntry) (GPCF × GPTEntry) )
          if ((bne gpf GPCF_None) : Bool)
          then
            (do
              let w__28 ← (( do (GPCFault gpf 1) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
              let w__29 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCFRecord × GPTEntry)
                GPTEntry )
              (pure ((w__28, w__29))))
          else
            (do
              let result : GPTEntry := { result with pa := pa }
              let w__30 ← (( do readReg __tlb_enabled ) : SailME (GPCFRecord × GPTEntry) Bool )
              let _ : Unit :=
                if (w__30 : Bool)
                then (GPTTLBCache pgs result)
                else ()
              let w__31 ← (( do (GPCNoFault ()) ) : SailME (GPCFRecord × GPTEntry) GPCFRecord )
              (pure ((w__31, result))))))


def AArch64_CheckSystemAccess (op0 : (BitVec 2)) (op1 : (BitVec 3)) (crn : (BitVec 4)) (crm : (BitVec 4)) (op2 : (BitVec 3)) (rt : (BitVec 5)) (read : (BitVec 1)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              (HaveTME ())) : Bool)
         then
           (do
             let w__1 ← (( do readReg TSTATE ) : SailM TMState )
             (pure (((w__1.depth >b 0) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do (CheckTransactionalSystemAccess op0 op1 crn crm op2 read) ) : SailM Bool
          )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (FailTransaction TMFailure_ERR false))
  else (pure (()))


def __InitSystem (_ : Unit) : SailM Unit := do
  writeReg DBGEN Signal_Low
  (TakeReset true)
  let w__0 ← (( do readReg CNTCR ) : SailM (BitVec 32) )
  writeReg CNTCR (Sail.BitVec.updateSubrange w__0 0 0 1#1)


/-- Type quantifiers: k_add : Bool, d : Nat, 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADR_Op_A_txt (add : Bool) (d : Nat) (imm32 : (BitVec 32)) : SailM Unit := do
  let result ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure (((Align_bits w__0 4) + imm32))))
    else
      (do
        let w__1 ← (( do (PC_read__1 ()) ) : SailM (BitVec 32) )
        (pure (((Align_bits w__1 4) - imm32)))) ) : SailM (BitVec 32) )
  if ((d == 15) : Bool)
  then
    (do
      (ALUWritePC result))
  else
    (do
      (R_set d result))


def decode_aarch32_instrs_B_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:1401.29-1401.30"
      let imm32 : (BitVec 32) := (sign_extend (imm24 +++ 0b00#2) 32)
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_B_T1enc_A_txt (cond : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:1419.29-1419.30"
      if ((cond == 0b1110#4) : Bool)
      then sailThrow ((Error_See "UDF"))
      else (pure (()))
      if ((cond == 0b1111#4) : Bool)
      then sailThrow ((Error_See "SVC"))
      else (pure (()))
      let imm32 : (BitVec 32) := (sign_extend (imm8 +++ 0#1) 32)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_B_T2enc_A_txt (imm11 : (BitVec 11)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (sign_extend (imm11 +++ 0#1) 32)
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_B_T3enc_A_txt (S : (BitVec 1)) (cond : (BitVec 4)) (imm6 : (BitVec 6)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:1465.29-1465.30"
      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb cond 3 1)) == 0b111#3) : Bool)
      then sailThrow ((Error_See "Related encodings"))
      else (pure (()))
      let imm32 : (BitVec 32) :=
        (sign_extend (((((S +++ J2) +++ J1) +++ imm6) +++ imm11) +++ 0#1) 32)
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_B_T4enc_A_txt (S : (BitVec 1)) (imm10 : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) :=
        (sign_extend (((((S +++ I1) +++ I2) +++ imm10) +++ imm11) +++ 0#1) 32)
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_B_Op_A_txt imm32))
  else (pure (()))


def decode_aarch32_instrs_BL_i_A1enc_A_txt (cond : (BitVec 4)) (imm24 : (BitVec 24)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:1968.29-1968.30"
      let imm32 : (BitVec 32) := (sign_extend (imm24 +++ 0b00#2) 32)
      let targetInstrSet : InstrSet := InstrSet_A32
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure (()))


def decode_aarch32_instrs_BL_i_A2enc_A_txt (H : (BitVec 1)) (imm24 : (BitVec 24)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let imm32 : (BitVec 32) := (sign_extend ((imm24 +++ H) +++ 0#1) 32)
      let targetInstrSet : InstrSet := InstrSet_T32
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure (()))


def decode_aarch32_instrs_BL_i_T1enc_A_txt (S : (BitVec 1)) (imm10 : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm11 : (BitVec 11)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) :=
        (sign_extend (((((S +++ I1) +++ I2) +++ imm10) +++ imm11) +++ 0#1) 32)
      let targetInstrSet : InstrSet := InstrSet_T32
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure (()))


def decode_aarch32_instrs_BL_i_T2enc_A_txt (S : (BitVec 1)) (imm10H : (BitVec 10)) (J1 : (BitVec 1)) (J2 : (BitVec 1)) (imm10L : (BitVec 10)) (H : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((H == 1#1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let I1 : (BitVec 1) := (Complement.complement (J1 ^^^ S))
      let I2 : (BitVec 1) := (Complement.complement (J2 ^^^ S))
      let imm32 : (BitVec 32) :=
        (sign_extend (((((S +++ I1) +++ I2) +++ imm10H) +++ imm10L) +++ 0b00#2) 32)
      let targetInstrSet : InstrSet := InstrSet_A32
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BL_i_Op_A_txt imm32 targetInstrSet))
  else (pure (()))


def decode_aarch32_instrs_BLX_r_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:2077.29-2077.30"
      let m : Int := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BLX_r_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BLX_r_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m : Int := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BLX_r_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BX_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:2135.29-2135.30"
      let m : Int := (BitVec.toNat Rm)
      (execute_aarch32_instrs_BX_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BX_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m : Int := (BitVec.toNat Rm)
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BX_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BXJ_A1enc_A_txt (cond : (BitVec 4)) (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:2187.29-2187.30"
      let m : Int := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BXJ_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_BXJ_T1enc_A_txt (Rm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let m : Int := (BitVec.toNat Rm)
      if ((m == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let w__3 ← (( do
        if ((← do
             (InITBlock ())) : Bool)
        then
          (do
            let w__2 ← (( do (LastInITBlock ()) ) : SailM Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_BXJ_Op_A_txt (Sail.Int.toNatChecked (m))))
  else (pure (()))


def decode_aarch32_instrs_CBNZ_T1enc_A_txt (op : (BitVec 1)) (i : (BitVec 1)) (imm5 : (BitVec 5)) (Rn : (BitVec 3)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm5) +++ 0#1) 32)
  let nonzero : Bool := (op == 1#1)
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  (execute_aarch32_instrs_CBNZ_Op_A_txt imm32 (Sail.Int.toNatChecked (n)) nonzero)


/-- Type quantifiers: k_nXS : Bool -/
def execute_aarch64_instrs_system_barriers_dsb (alias' : DSBAlias) (domain : MBReqDomain) (nXS__arg : Bool) (types : MBReqTypes) : SailM Unit := do
  let nXS : Bool := nXS__arg
  match alias' with
  | .DSBAlias_SSBB =>
    (do
      (SpeculativeStoreBypassBarrierToVA ()))
  | .DSBAlias_PSSBB => (pure ((SpeculativeStoreBypassBarrierToPA ())))
  | .DSBAlias_DSB =>
    (do
      let w__2 ← (( do
        if ((← do
             (HaveTME ())) : Bool)
        then
          (do
            let w__1 ← (( do readReg TSTATE ) : SailM TMState )
            (pure (((w__1.depth >b 0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          (FailTransaction TMFailure_ERR false))
      else (pure (()))
      let w__4 ← (( do
        if (((! nXS) : Bool) : Bool)
        then
          (do
            (HaveFeatXS ()))
        else (pure false) ) : SailM Bool )
      let nXS ← (( do
        if (w__4 : Bool)
        then
          (do
            if ((← do
                 if ((← do
                      if ((← do
                           let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__5.EL == EL0) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                          (pure (((w__6.EL == EL1) : Bool))))) : Bool)
                 then
                   (do
                     (IsHCRXEL2Enabled ()))
                 else (pure false)) : Bool)
            then
              (do
                let w__10 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCRX_EL2_Type_FnXS w__10) == 1#1) : Bool))))
            else (pure false))
        else (pure (nXS)) ) : SailM Bool )
      (DataSynchronizationBarrier domain types nXS))


def Halt (reason : (BitVec 6)) : SailM Unit := do
  let is_async : Bool := false
  (Halt__1 reason is_async)


def GranuleProtectionCheck (addrdesc : AddressDescriptor) (accdesc : AccessDescriptor) : SailM GPCFRecord := SailME.run do
  let gpcf ← (( do (undefined_GPCFRecord (← occLabel 1242) ()) ) : SailME GPCFRecord GPCFRecord
    )
  let gpt_entry ← (( do (undefined_GPTEntry (← occLabel 1243) ()) ) : SailME GPCFRecord GPTEntry
    )
  let w__0 ← (( do (HaveRME ()) ) : SailME GPCFRecord Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:19895.20-19895.21"
  let w__2 ← (( do
    (pure ((← do
          readReg __tlb_enabled) && ((bne accdesc.acctype AccessType_TTW) : Bool))) ) : SailME
    GPCFRecord Bool )
  if (w__2 : Bool)
  then
    (do
      let w__3 ← (( do (TLBIncludesGPT addrdesc.tlbcontext) ) : SailME GPCFRecord Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do (GPCNoFault ()) ) : SailME GPCFRecord GPCFRecord )
          SailME.throw (w__4 : GPCFRecord))
      else (pure (())))
  else (pure (()))
  let address : FullAddress := addrdesc.paddress
  let w__5 ← (( do readReg GPCCR_EL3 ) : SailME GPCFRecord (BitVec 64) )
  if (((_get_GPCCR_EL3_Type_GPC w__5) == 0#1) : Bool)
  then
    (do
      let w__6 ← (( do readReg __tlb_enabled ) : SailME GPCFRecord Bool )
      let _ : Unit :=
        if (w__6 : Bool)
        then (SetTLBIncludesGPT addrdesc.tlbcontext 56)
        else ()
      (GPCNoFault ()))
  else
    (do
      let w__8 ← (( do (GPCRegistersConsistent ()) ) : SailME GPCFRecord Bool )
      if ((! w__8) : Bool)
      then
        (do
          (GPCFault GPCF_Walk 0))
      else
        (do
          let w__10 ← (( do (AbovePPS address.address) ) : SailME GPCFRecord Bool )
          if (w__10 : Bool)
          then
            (do
              if ((BEq.beq address.paspace PAS_NonSecure) : Bool)
              then
                (do
                  let w__12 ← (( do
                    (pure ((← do
                          readReg __tlb_enabled) && ((bne accdesc.acctype AccessType_TTW) : Bool)))
                    ) : SailME GPCFRecord Bool )
                  let _ : Unit :=
                    if (w__12 : Bool)
                    then (SetTLBIncludesGPT addrdesc.tlbcontext 56)
                    else ()
                  (GPCNoFault ()))
              else
                (do
                  (GPCFault GPCF_Fail 0)))
          else
            (do
              let w__16 ← (( do readReg GPTBR_EL3 ) : SailME GPCFRecord (BitVec 64) )
              let gpt_base : (BitVec 56) :=
                (Sail.BitVec.zeroExtend ((_get_GPTBR_EL3_Type_BADDR w__16) +++ (Zeros (n := 12))) 56)
              let w__17 ← (( do (AbovePPS gpt_base) ) : SailME GPCFRecord Bool )
              if (w__17 : Bool)
              then
                (do
                  (GPCFault GPCF_AddressSize 0))
              else
                (do
                  let w__19 ← (( do (GPTWalk address.address accdesc) ) : SailME GPCFRecord
                    (GPCFRecord × GPTEntry) )
                  let (tup__0, tup__1) := (w__19 : (GPCFRecord × GPTEntry))
                  let gpcf : GPCFRecord := tup__0
                  let gpt_entry : GPTEntry := tup__1
                  if ((bne gpcf.gpf GPCF_None) : Bool)
                  then (pure (gpcf))
                  else
                    (do
                      let permitted ← (( do (GPICheck address.paspace gpt_entry.gpi) ) : SailME
                        GPCFRecord Bool )
                      if ((! permitted) : Bool)
                      then
                        (do
                          (GPCFault GPCF_Fail gpt_entry.level))
                      else
                        (do
                          let w__21 ← (( do
                            (pure ((← do
                                  readReg __tlb_enabled) && ((bne accdesc.acctype AccessType_TTW) : Bool)))
                            ) : SailME GPCFRecord Bool )
                          let _ : Unit :=
                            if (w__21 : Bool)
                            then (SetTLBIncludesGPT addrdesc.tlbcontext gpt_entry.contig_size)
                            else ()
                          (GPCNoFault ())))))))


end ArmFull.Functions
