import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork

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

def undefined_BranchType (ℓ : ChoiceLabel) (_ : Unit) : SailM BranchType := do
  (internal_pick_at (ℓ.child 0)
    [BranchType_DIRCALL, BranchType_INDCALL, BranchType_ERET, BranchType_DBGEXIT, BranchType_RET, BranchType_DIR, BranchType_INDIR, BranchType_EXCEPTION, BranchType_TMFAIL, BranchType_RESET, BranchType_UNKNOWN])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 10 -/
def BranchType_of_num (arg_ : Nat) : BranchType :=
  match arg_ with
  | 0 => BranchType_DIRCALL
  | 1 => BranchType_INDCALL
  | 2 => BranchType_ERET
  | 3 => BranchType_DBGEXIT
  | 4 => BranchType_RET
  | 5 => BranchType_DIR
  | 6 => BranchType_INDIR
  | 7 => BranchType_EXCEPTION
  | 8 => BranchType_TMFAIL
  | 9 => BranchType_RESET
  | _ => BranchType_UNKNOWN


def num_of_BranchType (arg_ : BranchType) : Int :=
  match arg_ with
  | .BranchType_DIRCALL => 0
  | .BranchType_INDCALL => 1
  | .BranchType_ERET => 2
  | .BranchType_DBGEXIT => 3
  | .BranchType_RET => 4
  | .BranchType_DIR => 5
  | .BranchType_INDIR => 6
  | .BranchType_EXCEPTION => 7
  | .BranchType_TMFAIL => 8
  | .BranchType_RESET => 9
  | .BranchType_UNKNOWN => 10


def undefined_InterruptID (ℓ : ChoiceLabel) (_ : Unit) : SailM InterruptID := do
  (internal_pick_at (ℓ.child 0)
    [InterruptID_PMUIRQ, InterruptID_COMMIRQ, InterruptID_CTIIRQ, InterruptID_COMMRX, InterruptID_COMMTX, InterruptID_CNTP, InterruptID_CNTHP, InterruptID_CNTHPS, InterruptID_CNTPS, InterruptID_CNTV, InterruptID_CNTHV, InterruptID_CNTHVS, InterruptID_PMBIRQ])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 12 -/
def InterruptID_of_num (arg_ : Nat) : InterruptID :=
  match arg_ with
  | 0 => InterruptID_PMUIRQ
  | 1 => InterruptID_COMMIRQ
  | 2 => InterruptID_CTIIRQ
  | 3 => InterruptID_COMMRX
  | 4 => InterruptID_COMMTX
  | 5 => InterruptID_CNTP
  | 6 => InterruptID_CNTHP
  | 7 => InterruptID_CNTHPS
  | 8 => InterruptID_CNTPS
  | 9 => InterruptID_CNTV
  | 10 => InterruptID_CNTHV
  | 11 => InterruptID_CNTHVS
  | _ => InterruptID_PMBIRQ


def num_of_InterruptID (arg_ : InterruptID) : Int :=
  match arg_ with
  | .InterruptID_PMUIRQ => 0
  | .InterruptID_COMMIRQ => 1
  | .InterruptID_CTIIRQ => 2
  | .InterruptID_COMMRX => 3
  | .InterruptID_COMMTX => 4
  | .InterruptID_CNTP => 5
  | .InterruptID_CNTHP => 6
  | .InterruptID_CNTHPS => 7
  | .InterruptID_CNTPS => 8
  | .InterruptID_CNTV => 9
  | .InterruptID_CNTHV => 10
  | .InterruptID_CNTHVS => 11
  | .InterruptID_PMBIRQ => 12


def undefined_Exception (ℓ : ChoiceLabel) (_ : Unit) : SailM Exception := do
  (internal_pick_at (ℓ.child 0)
    [Exception_Uncategorized, Exception_WFxTrap, Exception_CP15RTTrap, Exception_CP15RRTTrap, Exception_CP14RTTrap, Exception_CP14DTTrap, Exception_CP14RRTTrap, Exception_AdvSIMDFPAccessTrap, Exception_FPIDTrap, Exception_LDST64BTrap, Exception_PACTrap, Exception_IllegalState, Exception_SupervisorCall, Exception_HypervisorCall, Exception_MonitorCall, Exception_SystemRegisterTrap, Exception_ERetTrap, Exception_InstructionAbort, Exception_PCAlignment, Exception_DataAbort, Exception_NV2DataAbort, Exception_PACFail, Exception_SPAlignment, Exception_FPTrappedException, Exception_SError, Exception_Breakpoint, Exception_SoftwareStep, Exception_Watchpoint, Exception_NV2Watchpoint, Exception_SoftwareBreakpoint, Exception_VectorCatch, Exception_IRQ, Exception_SVEAccessTrap, Exception_SMEAccessTrap, Exception_TSTARTAccessTrap, Exception_GPC, Exception_BranchTarget, Exception_MemCpyMemSet, Exception_GCSFail, Exception_SystemRegister128Trap, Exception_FIQ])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 40 -/
def Exception_of_num (arg_ : Nat) : Exception :=
  match arg_ with
  | 0 => Exception_Uncategorized
  | 1 => Exception_WFxTrap
  | 2 => Exception_CP15RTTrap
  | 3 => Exception_CP15RRTTrap
  | 4 => Exception_CP14RTTrap
  | 5 => Exception_CP14DTTrap
  | 6 => Exception_CP14RRTTrap
  | 7 => Exception_AdvSIMDFPAccessTrap
  | 8 => Exception_FPIDTrap
  | 9 => Exception_LDST64BTrap
  | 10 => Exception_PACTrap
  | 11 => Exception_IllegalState
  | 12 => Exception_SupervisorCall
  | 13 => Exception_HypervisorCall
  | 14 => Exception_MonitorCall
  | 15 => Exception_SystemRegisterTrap
  | 16 => Exception_ERetTrap
  | 17 => Exception_InstructionAbort
  | 18 => Exception_PCAlignment
  | 19 => Exception_DataAbort
  | 20 => Exception_NV2DataAbort
  | 21 => Exception_PACFail
  | 22 => Exception_SPAlignment
  | 23 => Exception_FPTrappedException
  | 24 => Exception_SError
  | 25 => Exception_Breakpoint
  | 26 => Exception_SoftwareStep
  | 27 => Exception_Watchpoint
  | 28 => Exception_NV2Watchpoint
  | 29 => Exception_SoftwareBreakpoint
  | 30 => Exception_VectorCatch
  | 31 => Exception_IRQ
  | 32 => Exception_SVEAccessTrap
  | 33 => Exception_SMEAccessTrap
  | 34 => Exception_TSTARTAccessTrap
  | 35 => Exception_GPC
  | 36 => Exception_BranchTarget
  | 37 => Exception_MemCpyMemSet
  | 38 => Exception_GCSFail
  | 39 => Exception_SystemRegister128Trap
  | _ => Exception_FIQ


def num_of_Exception (arg_ : Exception) : Int :=
  match arg_ with
  | .Exception_Uncategorized => 0
  | .Exception_WFxTrap => 1
  | .Exception_CP15RTTrap => 2
  | .Exception_CP15RRTTrap => 3
  | .Exception_CP14RTTrap => 4
  | .Exception_CP14DTTrap => 5
  | .Exception_CP14RRTTrap => 6
  | .Exception_AdvSIMDFPAccessTrap => 7
  | .Exception_FPIDTrap => 8
  | .Exception_LDST64BTrap => 9
  | .Exception_PACTrap => 10
  | .Exception_IllegalState => 11
  | .Exception_SupervisorCall => 12
  | .Exception_HypervisorCall => 13
  | .Exception_MonitorCall => 14
  | .Exception_SystemRegisterTrap => 15
  | .Exception_ERetTrap => 16
  | .Exception_InstructionAbort => 17
  | .Exception_PCAlignment => 18
  | .Exception_DataAbort => 19
  | .Exception_NV2DataAbort => 20
  | .Exception_PACFail => 21
  | .Exception_SPAlignment => 22
  | .Exception_FPTrappedException => 23
  | .Exception_SError => 24
  | .Exception_Breakpoint => 25
  | .Exception_SoftwareStep => 26
  | .Exception_Watchpoint => 27
  | .Exception_NV2Watchpoint => 28
  | .Exception_SoftwareBreakpoint => 29
  | .Exception_VectorCatch => 30
  | .Exception_IRQ => 31
  | .Exception_SVEAccessTrap => 32
  | .Exception_SMEAccessTrap => 33
  | .Exception_TSTARTAccessTrap => 34
  | .Exception_GPC => 35
  | .Exception_BranchTarget => 36
  | .Exception_MemCpyMemSet => 37
  | .Exception_GCSFail => 38
  | .Exception_SystemRegister128Trap => 39
  | .Exception_FIQ => 40


def undefined_TranslationStage (ℓ : ChoiceLabel) (_ : Unit) : SailM TranslationStage := do
  (internal_pick_at (ℓ.child 0) [TranslationStage_1, TranslationStage_12])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TranslationStage_of_num (arg_ : Nat) : TranslationStage :=
  match arg_ with
  | 0 => TranslationStage_1
  | _ => TranslationStage_12


def num_of_TranslationStage (arg_ : TranslationStage) : Int :=
  match arg_ with
  | .TranslationStage_1 => 0
  | .TranslationStage_12 => 1


def undefined_ATAccess (ℓ : ChoiceLabel) (_ : Unit) : SailM ATAccess := do
  (internal_pick_at (ℓ.child 0)
    [ATAccess_Read, ATAccess_Write, ATAccess_ReadPAN, ATAccess_WritePAN])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ATAccess_of_num (arg_ : Nat) : ATAccess :=
  match arg_ with
  | 0 => ATAccess_Read
  | 1 => ATAccess_Write
  | 2 => ATAccess_ReadPAN
  | _ => ATAccess_WritePAN


def num_of_ATAccess (arg_ : ATAccess) : Int :=
  match arg_ with
  | .ATAccess_Read => 0
  | .ATAccess_Write => 1
  | .ATAccess_ReadPAN => 2
  | .ATAccess_WritePAN => 3


def undefined_Regime (ℓ : ChoiceLabel) (_ : Unit) : SailM Regime := do
  (internal_pick_at (ℓ.child 0) [Regime_EL3, Regime_EL30, Regime_EL2, Regime_EL20, Regime_EL10])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def Regime_of_num (arg_ : Nat) : Regime :=
  match arg_ with
  | 0 => Regime_EL3
  | 1 => Regime_EL30
  | 2 => Regime_EL2
  | 3 => Regime_EL20
  | _ => Regime_EL10


def num_of_Regime (arg_ : Regime) : Int :=
  match arg_ with
  | .Regime_EL3 => 0
  | .Regime_EL30 => 1
  | .Regime_EL2 => 2
  | .Regime_EL20 => 3
  | .Regime_EL10 => 4


def undefined_TGx (ℓ : ChoiceLabel) (_ : Unit) : SailM TGx := do
  (internal_pick_at (ℓ.child 0) [TGx_4KB, TGx_16KB, TGx_64KB])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def TGx_of_num (arg_ : Nat) : TGx :=
  match arg_ with
  | 0 => TGx_4KB
  | 1 => TGx_16KB
  | _ => TGx_64KB


def num_of_TGx (arg_ : TGx) : Int :=
  match arg_ with
  | .TGx_4KB => 0
  | .TGx_16KB => 1
  | .TGx_64KB => 2


def undefined_DescriptorType (ℓ : ChoiceLabel) (_ : Unit) : SailM DescriptorType := do
  (internal_pick_at (ℓ.child 0)
    [DescriptorType_Table, DescriptorType_Leaf, DescriptorType_Invalid])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def DescriptorType_of_num (arg_ : Nat) : DescriptorType :=
  match arg_ with
  | 0 => DescriptorType_Table
  | 1 => DescriptorType_Leaf
  | _ => DescriptorType_Invalid


def num_of_DescriptorType (arg_ : DescriptorType) : Int :=
  match arg_ with
  | .DescriptorType_Table => 0
  | .DescriptorType_Leaf => 1
  | .DescriptorType_Invalid => 2


def Domain_NoAccess : (BitVec 2) := 0b00#2


def Domain_Client : (BitVec 2) := 0b01#2


def undefined_SDFType (ℓ : ChoiceLabel) (_ : Unit) : SailM SDFType := do
  (internal_pick_at (ℓ.child 0)
    [SDFType_Table, SDFType_Invalid, SDFType_Supersection, SDFType_Section, SDFType_LargePage, SDFType_SmallPage])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def SDFType_of_num (arg_ : Nat) : SDFType :=
  match arg_ with
  | 0 => SDFType_Table
  | 1 => SDFType_Invalid
  | 2 => SDFType_Supersection
  | 3 => SDFType_Section
  | 4 => SDFType_LargePage
  | _ => SDFType_SmallPage


def num_of_SDFType (arg_ : SDFType) : Int :=
  match arg_ with
  | .SDFType_Table => 0
  | .SDFType_Invalid => 1
  | .SDFType_Supersection => 2
  | .SDFType_Section => 3
  | .SDFType_LargePage => 4
  | .SDFType_SmallPage => 5


def FINAL_LEVEL : Nat := 3


def undefined_SVECmp (ℓ : ChoiceLabel) (_ : Unit) : SailM SVECmp := do
  (internal_pick_at (ℓ.child 0) [Cmp_EQ, Cmp_NE, Cmp_GE, Cmp_GT, Cmp_LT, Cmp_LE, Cmp_UN])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def SVECmp_of_num (arg_ : Nat) : SVECmp :=
  match arg_ with
  | 0 => Cmp_EQ
  | 1 => Cmp_NE
  | 2 => Cmp_GE
  | 3 => Cmp_GT
  | 4 => Cmp_LT
  | 5 => Cmp_LE
  | _ => Cmp_UN


def num_of_SVECmp (arg_ : SVECmp) : Int :=
  match arg_ with
  | .Cmp_EQ => 0
  | .Cmp_NE => 1
  | .Cmp_GE => 2
  | .Cmp_GT => 3
  | .Cmp_LT => 4
  | .Cmp_LE => 5
  | .Cmp_UN => 6


def MAX_VL : Nat := 2048


def MAX_PL : Nat := 256


def ZT0_LEN : Nat := 512


def undefined_SMEExceptionType (ℓ : ChoiceLabel) (_ : Unit) : SailM SMEExceptionType := do
  (internal_pick_at (ℓ.child 0)
    [SMEExceptionType_AccessTrap, SMEExceptionType_Streaming, SMEExceptionType_NotStreaming, SMEExceptionType_InactiveZA, SMEExceptionType_InaccessibleZT0])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def SMEExceptionType_of_num (arg_ : Nat) : SMEExceptionType :=
  match arg_ with
  | 0 => SMEExceptionType_AccessTrap
  | 1 => SMEExceptionType_Streaming
  | 2 => SMEExceptionType_NotStreaming
  | 3 => SMEExceptionType_InactiveZA
  | _ => SMEExceptionType_InaccessibleZT0


def num_of_SMEExceptionType (arg_ : SMEExceptionType) : Int :=
  match arg_ with
  | .SMEExceptionType_AccessTrap => 0
  | .SMEExceptionType_Streaming => 1
  | .SMEExceptionType_NotStreaming => 2
  | .SMEExceptionType_InactiveZA => 3
  | .SMEExceptionType_InaccessibleZT0 => 4


def undefined_GCSInstruction (ℓ : ChoiceLabel) (_ : Unit) : SailM GCSInstruction := do
  (internal_pick_at (ℓ.child 0)
    [GCSInstType_PRET, GCSInstType_POPM, GCSInstType_PRETAA, GCSInstType_PRETAB, GCSInstType_SS1, GCSInstType_SS2, GCSInstType_POPCX, GCSInstType_POPX])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def GCSInstruction_of_num (arg_ : Nat) : GCSInstruction :=
  match arg_ with
  | 0 => GCSInstType_PRET
  | 1 => GCSInstType_POPM
  | 2 => GCSInstType_PRETAA
  | 3 => GCSInstType_PRETAB
  | 4 => GCSInstType_SS1
  | 5 => GCSInstType_SS2
  | 6 => GCSInstType_POPCX
  | _ => GCSInstType_POPX


def num_of_GCSInstruction (arg_ : GCSInstruction) : Int :=
  match arg_ with
  | .GCSInstType_PRET => 0
  | .GCSInstType_POPM => 1
  | .GCSInstType_PRETAA => 2
  | .GCSInstType_PRETAB => 3
  | .GCSInstType_SS1 => 4
  | .GCSInstType_SS2 => 5
  | .GCSInstType_POPCX => 6
  | .GCSInstType_POPX => 7


def undefined_MOPSStage (ℓ : ChoiceLabel) (_ : Unit) : SailM MOPSStage := do
  (internal_pick_at (ℓ.child 0) [MOPSStage_Prologue, MOPSStage_Main, MOPSStage_Epilogue])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MOPSStage_of_num (arg_ : Nat) : MOPSStage :=
  match arg_ with
  | 0 => MOPSStage_Prologue
  | 1 => MOPSStage_Main
  | _ => MOPSStage_Epilogue


def num_of_MOPSStage (arg_ : MOPSStage) : Int :=
  match arg_ with
  | .MOPSStage_Prologue => 0
  | .MOPSStage_Main => 1
  | .MOPSStage_Epilogue => 2


def undefined_FPCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_FPCR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_FPSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_FPSR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_FPSR_Type_IDC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_FPSR_Type_IDC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_CTR_EL0_Type_IDC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_CTR_Type_IDC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_FPSCR_Type_IDC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_CTR_EL0_Type_IDC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_CTR_Type_IDC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_FPSCR_Type_IDC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_FPSR_Type_IXC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_FPSR_Type_IXC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_FPSCR_Type_IXC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_FPSCR_Type_IXC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_FPSR_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_FPSR_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_AMCFGR_EL0_Type_N (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_AMCFGR_Type_N (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_DSPSR_EL0_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_DSPSR_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_FPSCR_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_PMCFGR_Type_N (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_PMCR_EL0_Type_N (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 11 x)


def _update_PMCR_Type_N (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 11 x)


def _update_SPSR_EL1_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_EL2_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_EL3_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_abt_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_fiq_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_hyp_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_irq_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_mon_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_svc_Type_N (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_SPSR_und_Type_N (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_TTBCR_Type_N (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 0 x)


def _get_AMCFGR_EL0_Type_N (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_AMCFGR_Type_N (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_DSPSR_EL0_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_DSPSR_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_FPSCR_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_PMCFGR_Type_N (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _get_PMCR_EL0_Type_N (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 15 11)


def _get_PMCR_Type_N (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 15 11)


def _get_SPSR_EL1_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_EL2_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_EL3_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_abt_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_fiq_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_hyp_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_irq_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_mon_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_svc_Type_N (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_SPSR_und_Type_N (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_TTBCR_Type_N (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 2 0)


def _get_FPSR_Type_QC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_FPSR_Type_QC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_FPSCR_Type_QC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_FPSCR_Type_QC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _get_FPSR_Type_UFC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_FPSR_Type_UFC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_FPSCR_Type_UFC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_FPSCR_Type_UFC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_FPSR_Type_V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_FPSR_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_DSPSR_EL0_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_DSPSR_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_FPSCR_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_GICR_INVALLR_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_GICR_INVLPIR_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_SCTLR_Type_V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_SPSR_EL1_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_SPSR_EL2_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_SPSR_EL3_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_SPSR_abt_Type_V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


end ArmFull.Functions
