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

def undefined_SystemHintOp (ℓ : ChoiceLabel) (_ : Unit) : SailM SystemHintOp := do
  (internal_pick_at (ℓ.child 0)
    [SystemHintOp_NOP, SystemHintOp_YIELD, SystemHintOp_WFE, SystemHintOp_WFI, SystemHintOp_SEV, SystemHintOp_SEVL, SystemHintOp_DGH, SystemHintOp_ESB, SystemHintOp_PSB, SystemHintOp_TSB, SystemHintOp_BTI, SystemHintOp_WFET, SystemHintOp_WFIT, SystemHintOp_CLRBHB, SystemHintOp_GCSB, SystemHintOp_CHKFEAT, SystemHintOp_CSDB])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 16 -/
def SystemHintOp_of_num (arg_ : Nat) : SystemHintOp :=
  match arg_ with
  | 0 => SystemHintOp_NOP
  | 1 => SystemHintOp_YIELD
  | 2 => SystemHintOp_WFE
  | 3 => SystemHintOp_WFI
  | 4 => SystemHintOp_SEV
  | 5 => SystemHintOp_SEVL
  | 6 => SystemHintOp_DGH
  | 7 => SystemHintOp_ESB
  | 8 => SystemHintOp_PSB
  | 9 => SystemHintOp_TSB
  | 10 => SystemHintOp_BTI
  | 11 => SystemHintOp_WFET
  | 12 => SystemHintOp_WFIT
  | 13 => SystemHintOp_CLRBHB
  | 14 => SystemHintOp_GCSB
  | 15 => SystemHintOp_CHKFEAT
  | _ => SystemHintOp_CSDB


def num_of_SystemHintOp (arg_ : SystemHintOp) : Int :=
  match arg_ with
  | .SystemHintOp_NOP => 0
  | .SystemHintOp_YIELD => 1
  | .SystemHintOp_WFE => 2
  | .SystemHintOp_WFI => 3
  | .SystemHintOp_SEV => 4
  | .SystemHintOp_SEVL => 5
  | .SystemHintOp_DGH => 6
  | .SystemHintOp_ESB => 7
  | .SystemHintOp_PSB => 8
  | .SystemHintOp_TSB => 9
  | .SystemHintOp_BTI => 10
  | .SystemHintOp_WFET => 11
  | .SystemHintOp_WFIT => 12
  | .SystemHintOp_CLRBHB => 13
  | .SystemHintOp_GCSB => 14
  | .SystemHintOp_CHKFEAT => 15
  | .SystemHintOp_CSDB => 16


def undefined_PSTATEField (ℓ : ChoiceLabel) (_ : Unit) : SailM PSTATEField := do
  (internal_pick_at (ℓ.child 0)
    [PSTATEField_DAIFSet, PSTATEField_DAIFClr, PSTATEField_PAN, PSTATEField_UAO, PSTATEField_DIT, PSTATEField_SSBS, PSTATEField_TCO, PSTATEField_SVCRSM, PSTATEField_SVCRZA, PSTATEField_SVCRSMZA, PSTATEField_ALLINT, PSTATEField_PM, PSTATEField_SP])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 12 -/
def PSTATEField_of_num (arg_ : Nat) : PSTATEField :=
  match arg_ with
  | 0 => PSTATEField_DAIFSet
  | 1 => PSTATEField_DAIFClr
  | 2 => PSTATEField_PAN
  | 3 => PSTATEField_UAO
  | 4 => PSTATEField_DIT
  | 5 => PSTATEField_SSBS
  | 6 => PSTATEField_TCO
  | 7 => PSTATEField_SVCRSM
  | 8 => PSTATEField_SVCRZA
  | 9 => PSTATEField_SVCRSMZA
  | 10 => PSTATEField_ALLINT
  | 11 => PSTATEField_PM
  | _ => PSTATEField_SP


def num_of_PSTATEField (arg_ : PSTATEField) : Int :=
  match arg_ with
  | .PSTATEField_DAIFSet => 0
  | .PSTATEField_DAIFClr => 1
  | .PSTATEField_PAN => 2
  | .PSTATEField_UAO => 3
  | .PSTATEField_DIT => 4
  | .PSTATEField_SSBS => 5
  | .PSTATEField_TCO => 6
  | .PSTATEField_SVCRSM => 7
  | .PSTATEField_SVCRZA => 8
  | .PSTATEField_SVCRSMZA => 9
  | .PSTATEField_ALLINT => 10
  | .PSTATEField_PM => 11
  | .PSTATEField_SP => 12


def undefined_TLBILevel (ℓ : ChoiceLabel) (_ : Unit) : SailM TLBILevel := do
  (internal_pick_at (ℓ.child 0) [TLBILevel_Any, TLBILevel_Last])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TLBILevel_of_num (arg_ : Nat) : TLBILevel :=
  match arg_ with
  | 0 => TLBILevel_Any
  | _ => TLBILevel_Last


def num_of_TLBILevel (arg_ : TLBILevel) : Int :=
  match arg_ with
  | .TLBILevel_Any => 0
  | .TLBILevel_Last => 1


def undefined_TLBIOp (ℓ : ChoiceLabel) (_ : Unit) : SailM TLBIOp := do
  (internal_pick_at (ℓ.child 0)
    [TLBIOp_DALL, TLBIOp_DASID, TLBIOp_DVA, TLBIOp_IALL, TLBIOp_IASID, TLBIOp_IVA, TLBIOp_ALL, TLBIOp_ASID, TLBIOp_IPAS2, TLBIPOp_IPAS2, TLBIOp_VAA, TLBIOp_VA, TLBIPOp_VAA, TLBIPOp_VA, TLBIOp_VMALL, TLBIOp_VMALLS12, TLBIOp_RIPAS2, TLBIPOp_RIPAS2, TLBIOp_RVAA, TLBIOp_RVA, TLBIPOp_RVAA, TLBIPOp_RVA, TLBIOp_RPA, TLBIOp_PAALL])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 23 -/
def TLBIOp_of_num (arg_ : Nat) : TLBIOp :=
  match arg_ with
  | 0 => TLBIOp_DALL
  | 1 => TLBIOp_DASID
  | 2 => TLBIOp_DVA
  | 3 => TLBIOp_IALL
  | 4 => TLBIOp_IASID
  | 5 => TLBIOp_IVA
  | 6 => TLBIOp_ALL
  | 7 => TLBIOp_ASID
  | 8 => TLBIOp_IPAS2
  | 9 => TLBIPOp_IPAS2
  | 10 => TLBIOp_VAA
  | 11 => TLBIOp_VA
  | 12 => TLBIPOp_VAA
  | 13 => TLBIPOp_VA
  | 14 => TLBIOp_VMALL
  | 15 => TLBIOp_VMALLS12
  | 16 => TLBIOp_RIPAS2
  | 17 => TLBIPOp_RIPAS2
  | 18 => TLBIOp_RVAA
  | 19 => TLBIOp_RVA
  | 20 => TLBIPOp_RVAA
  | 21 => TLBIPOp_RVA
  | 22 => TLBIOp_RPA
  | _ => TLBIOp_PAALL


def num_of_TLBIOp (arg_ : TLBIOp) : Int :=
  match arg_ with
  | .TLBIOp_DALL => 0
  | .TLBIOp_DASID => 1
  | .TLBIOp_DVA => 2
  | .TLBIOp_IALL => 3
  | .TLBIOp_IASID => 4
  | .TLBIOp_IVA => 5
  | .TLBIOp_ALL => 6
  | .TLBIOp_ASID => 7
  | .TLBIOp_IPAS2 => 8
  | .TLBIPOp_IPAS2 => 9
  | .TLBIOp_VAA => 10
  | .TLBIOp_VA => 11
  | .TLBIPOp_VAA => 12
  | .TLBIPOp_VA => 13
  | .TLBIOp_VMALL => 14
  | .TLBIOp_VMALLS12 => 15
  | .TLBIOp_RIPAS2 => 16
  | .TLBIPOp_RIPAS2 => 17
  | .TLBIOp_RVAA => 18
  | .TLBIOp_RVA => 19
  | .TLBIPOp_RVAA => 20
  | .TLBIPOp_RVA => 21
  | .TLBIOp_RPA => 22
  | .TLBIOp_PAALL => 23


def undefined_TLBIMemAttr (ℓ : ChoiceLabel) (_ : Unit) : SailM TLBIMemAttr := do
  (internal_pick_at (ℓ.child 0) [TLBI_AllAttr, TLBI_ExcludeXS])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def TLBIMemAttr_of_num (arg_ : Nat) : TLBIMemAttr :=
  match arg_ with
  | 0 => TLBI_AllAttr
  | _ => TLBI_ExcludeXS


def num_of_TLBIMemAttr (arg_ : TLBIMemAttr) : Int :=
  match arg_ with
  | .TLBI_AllAttr => 0
  | .TLBI_ExcludeXS => 1


def MAX_ZERO_BLOCK_SIZE : Nat := 2048


def undefined_VBitOp (ℓ : ChoiceLabel) (_ : Unit) : SailM VBitOp := do
  (internal_pick_at (ℓ.child 0) [VBitOp_VBIF, VBitOp_VBIT, VBitOp_VBSL, VBitOp_VEOR])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def VBitOp_of_num (arg_ : Nat) : VBitOp :=
  match arg_ with
  | 0 => VBitOp_VBIF
  | 1 => VBitOp_VBIT
  | 2 => VBitOp_VBSL
  | _ => VBitOp_VEOR


def num_of_VBitOp (arg_ : VBitOp) : Int :=
  match arg_ with
  | .VBitOp_VBIF => 0
  | .VBitOp_VBIT => 1
  | .VBitOp_VBSL => 2
  | .VBitOp_VEOR => 3


def undefined_CompareOp (ℓ : ChoiceLabel) (_ : Unit) : SailM CompareOp := do
  (internal_pick_at (ℓ.child 0)
    [CompareOp_GT, CompareOp_GE, CompareOp_EQ, CompareOp_LE, CompareOp_LT])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def CompareOp_of_num (arg_ : Nat) : CompareOp :=
  match arg_ with
  | 0 => CompareOp_GT
  | 1 => CompareOp_GE
  | 2 => CompareOp_EQ
  | 3 => CompareOp_LE
  | _ => CompareOp_LT


def num_of_CompareOp (arg_ : CompareOp) : Int :=
  match arg_ with
  | .CompareOp_GT => 0
  | .CompareOp_GE => 1
  | .CompareOp_EQ => 2
  | .CompareOp_LE => 3
  | .CompareOp_LT => 4


def undefined_ImmediateOp (ℓ : ChoiceLabel) (_ : Unit) : SailM ImmediateOp := do
  (internal_pick_at (ℓ.child 0)
    [ImmediateOp_MOVI, ImmediateOp_MVNI, ImmediateOp_ORR, ImmediateOp_BIC])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def ImmediateOp_of_num (arg_ : Nat) : ImmediateOp :=
  match arg_ with
  | 0 => ImmediateOp_MOVI
  | 1 => ImmediateOp_MVNI
  | 2 => ImmediateOp_ORR
  | _ => ImmediateOp_BIC


def num_of_ImmediateOp (arg_ : ImmediateOp) : Int :=
  match arg_ with
  | .ImmediateOp_MOVI => 0
  | .ImmediateOp_MVNI => 1
  | .ImmediateOp_ORR => 2
  | .ImmediateOp_BIC => 3


def undefined_ReduceOp (ℓ : ChoiceLabel) (_ : Unit) : SailM ReduceOp := do
  (internal_pick_at (ℓ.child 0)
    [ReduceOp_FMINNUM, ReduceOp_FMAXNUM, ReduceOp_FMIN, ReduceOp_FMAX, ReduceOp_FADD, ReduceOp_ADD])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def ReduceOp_of_num (arg_ : Nat) : ReduceOp :=
  match arg_ with
  | 0 => ReduceOp_FMINNUM
  | 1 => ReduceOp_FMAXNUM
  | 2 => ReduceOp_FMIN
  | 3 => ReduceOp_FMAX
  | 4 => ReduceOp_FADD
  | _ => ReduceOp_ADD


def num_of_ReduceOp (arg_ : ReduceOp) : Int :=
  match arg_ with
  | .ReduceOp_FMINNUM => 0
  | .ReduceOp_FMAXNUM => 1
  | .ReduceOp_FMIN => 2
  | .ReduceOp_FMAX => 3
  | .ReduceOp_FADD => 4
  | .ReduceOp_ADD => 5


def undefined_CrossTriggerIn (ℓ : ChoiceLabel) (_ : Unit) : SailM CrossTriggerIn := do
  (internal_pick_at (ℓ.child 0)
    [CrossTriggerIn_CrossHalt, CrossTriggerIn_PMUOverflow, CrossTriggerIn_RSVD2, CrossTriggerIn_RSVD3, CrossTriggerIn_TraceExtOut0, CrossTriggerIn_TraceExtOut1, CrossTriggerIn_TraceExtOut2, CrossTriggerIn_TraceExtOut3])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 7 -/
def CrossTriggerIn_of_num (arg_ : Nat) : CrossTriggerIn :=
  match arg_ with
  | 0 => CrossTriggerIn_CrossHalt
  | 1 => CrossTriggerIn_PMUOverflow
  | 2 => CrossTriggerIn_RSVD2
  | 3 => CrossTriggerIn_RSVD3
  | 4 => CrossTriggerIn_TraceExtOut0
  | 5 => CrossTriggerIn_TraceExtOut1
  | 6 => CrossTriggerIn_TraceExtOut2
  | _ => CrossTriggerIn_TraceExtOut3


def num_of_CrossTriggerIn (arg_ : CrossTriggerIn) : Int :=
  match arg_ with
  | .CrossTriggerIn_CrossHalt => 0
  | .CrossTriggerIn_PMUOverflow => 1
  | .CrossTriggerIn_RSVD2 => 2
  | .CrossTriggerIn_RSVD3 => 3
  | .CrossTriggerIn_TraceExtOut0 => 4
  | .CrossTriggerIn_TraceExtOut1 => 5
  | .CrossTriggerIn_TraceExtOut2 => 6
  | .CrossTriggerIn_TraceExtOut3 => 7


def DebugHalt_Breakpoint : (BitVec 6) := 0b000111#6


def DebugHalt_EDBGRQ : (BitVec 6) := 0b010011#6


def DebugHalt_Step_Normal : (BitVec 6) := 0b011011#6


def DebugHalt_Step_Exclusive : (BitVec 6) := 0b011111#6


def DebugHalt_OSUnlockCatch : (BitVec 6) := 0b100011#6


def DebugHalt_ResetCatch : (BitVec 6) := 0b100111#6


def DebugHalt_Watchpoint : (BitVec 6) := 0b101011#6


def DebugHalt_HaltInstruction : (BitVec 6) := 0b101111#6


def DebugHalt_SoftwareAccess : (BitVec 6) := 0b110011#6


def DebugHalt_ExceptionCatch : (BitVec 6) := 0b110111#6


def DebugHalt_Step_NoSyndrome : (BitVec 6) := 0b111011#6


def RCW64_PROTECTED_BIT : Nat := 52


def RCW128_PROTECTED_BIT : Nat := 114


def undefined_InterruptReq (ℓ : ChoiceLabel) (_ : Unit) : SailM InterruptReq := do
  let w__0 ← (( do (undefined_bool_at (ℓ.child 0) ()) ) : SailM Bool )
  let w__1 ← (( do (undefined_bool_at (ℓ.child 1) ()) ) : SailM Bool )
  let w__2 ← (( do (undefined_bool_at (ℓ.child 2) ()) ) : SailM Bool )
  let w__3 ← (( do (undefined_bool_at (ℓ.child 3) ()) ) : SailM Bool )
  let w__4 ← (( do (undefined_bool_at (ℓ.child 4) ()) ) : SailM Bool )
  let w__5 ← (( do (undefined_bool_at (ℓ.child 5) ()) ) : SailM Bool )
  let w__6 ← (( do (undefined_bool_at (ℓ.child 6) ()) ) : SailM Bool )
  (pure ({ take_SE := w__0
           take_vSE := w__1
           take_IRQ := w__2
           take_vIRQ := w__3
           take_FIQ := w__4
           take_vFIQ := w__5
           iesb_req := w__6 }))


def undefined___InstrEnc (ℓ : ChoiceLabel) (_ : Unit) : SailM __InstrEnc := do
  (internal_pick_at (ℓ.child 0) [__A64, __A32, __T16, __T32])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def __InstrEnc_of_num (arg_ : Nat) : __InstrEnc :=
  match arg_ with
  | 0 => __A64
  | 1 => __A32
  | 2 => __T16
  | _ => __T32


def num_of___InstrEnc (arg_ : __InstrEnc) : Int :=
  match arg_ with
  | .__A64 => 0
  | .__A32 => 1
  | .__T16 => 2
  | .__T32 => 3


def lst_64bv : (BitVec 2) := 0b01#2


def lst_64b : (BitVec 2) := 0b10#2


def lst_64bv0 : (BitVec 2) := 0b11#2


def CFG_ID_AA64PFR0_EL1_EL0 : (BitVec 4) := 0b0010#4


def CFG_ID_AA64PFR0_EL1_EL1 : (BitVec 4) := 0b0001#4


def CFG_ID_AA64PFR0_EL1_EL2 : (BitVec 4) := 0b0001#4


def CFG_ID_AA64PFR0_EL1_EL3 : (BitVec 4) := 0b0001#4


def CFG_PMCR_IDCODE : (BitVec 8) := 0b00000000#8


def CFG_MPAM_none : (BitVec 4) := 0b0000#4


def CFG_MPAM_v0p1 : (BitVec 4) := 0b0000#4


def CFG_MPAM_v1p1 : (BitVec 4) := 0b0001#4


def CFG_MPAM_frac_none : (BitVec 4) := 0b0000#4


def CFG_MPAM_frac_v0p1 : (BitVec 4) := 0b0001#4


def CFG_MPAM_frac_v1p1 : (BitVec 4) := 0b0001#4


def undefined_SRType (ℓ : ChoiceLabel) (_ : Unit) : SailM SRType := do
  (internal_pick_at (ℓ.child 0) [SRType_LSL, SRType_LSR, SRType_ASR, SRType_ROR, SRType_RRX])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def SRType_of_num (arg_ : Nat) : SRType :=
  match arg_ with
  | 0 => SRType_LSL
  | 1 => SRType_LSR
  | 2 => SRType_ASR
  | 3 => SRType_ROR
  | _ => SRType_RRX


def num_of_SRType (arg_ : SRType) : Int :=
  match arg_ with
  | .SRType_LSL => 0
  | .SRType_LSR => 1
  | .SRType_ASR => 2
  | .SRType_ROR => 3
  | .SRType_RRX => 4


def undefined_VCGEType (ℓ : ChoiceLabel) (_ : Unit) : SailM VCGEType := do
  (internal_pick_at (ℓ.child 0) [VCGEType_signed, VCGEType_unsigned, VCGEType_fp])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def VCGEType_of_num (arg_ : Nat) : VCGEType :=
  match arg_ with
  | 0 => VCGEType_signed
  | 1 => VCGEType_unsigned
  | _ => VCGEType_fp


def num_of_VCGEType (arg_ : VCGEType) : Int :=
  match arg_ with
  | .VCGEType_signed => 0
  | .VCGEType_unsigned => 1
  | .VCGEType_fp => 2


def undefined_VFPNegMul (ℓ : ChoiceLabel) (_ : Unit) : SailM VFPNegMul := do
  (internal_pick_at (ℓ.child 0) [VFPNegMul_VNMLA, VFPNegMul_VNMLS, VFPNegMul_VNMUL])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def VFPNegMul_of_num (arg_ : Nat) : VFPNegMul :=
  match arg_ with
  | 0 => VFPNegMul_VNMLA
  | 1 => VFPNegMul_VNMLS
  | _ => VFPNegMul_VNMUL


def num_of_VFPNegMul (arg_ : VFPNegMul) : Int :=
  match arg_ with
  | .VFPNegMul_VNMLA => 0
  | .VFPNegMul_VNMLS => 1
  | .VFPNegMul_VNMUL => 2


def undefined_VCGTtype (ℓ : ChoiceLabel) (_ : Unit) : SailM VCGTtype := do
  (internal_pick_at (ℓ.child 0) [VCGTtype_signed, VCGTtype_unsigned, VCGTtype_fp])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def VCGTtype_of_num (arg_ : Nat) : VCGTtype :=
  match arg_ with
  | 0 => VCGTtype_signed
  | 1 => VCGTtype_unsigned
  | _ => VCGTtype_fp


def num_of_VCGTtype (arg_ : VCGTtype) : Int :=
  match arg_ with
  | .VCGTtype_signed => 0
  | .VCGTtype_unsigned => 1
  | .VCGTtype_fp => 2


def undefined_VBitOps (ℓ : ChoiceLabel) (_ : Unit) : SailM VBitOps := do
  (internal_pick_at (ℓ.child 0) [VBitOps_VBIF, VBitOps_VBIT, VBitOps_VBSL])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def VBitOps_of_num (arg_ : Nat) : VBitOps :=
  match arg_ with
  | 0 => VBitOps_VBIF
  | 1 => VBitOps_VBIT
  | _ => VBitOps_VBSL


def num_of_VBitOps (arg_ : VBitOps) : Int :=
  match arg_ with
  | .VBitOps_VBIF => 0
  | .VBitOps_VBIT => 1
  | .VBitOps_VBSL => 2


def DebugException_Breakpoint : (BitVec 4) := 0b0001#4


def DebugException_BKPT : (BitVec 4) := 0b0011#4


def DebugException_VectorCatch : (BitVec 4) := 0b0101#4


def DebugException_Watchpoint : (BitVec 4) := 0b1010#4


def undefined_HCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_HCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HCR_EL2_Type_AMO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_HCR_EL2_Type_AMO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_HCR_Type_AMO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_HCR_Type_AMO (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_HCR_EL2_Type_AMVOFFEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)


def _update_HCR_EL2_Type_AMVOFFEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)


def _update_SCR_EL3_Type_AMVOFFEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 35 x)


def _get_SCR_EL3_Type_AMVOFFEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 35 35)


def _get_HCR_EL2_Type_API (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)


def _update_HCR_EL2_Type_API (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)


def _update_ID_AA64ISAR1_EL1_Type_API (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 8 x)


def _update_SCR_EL3_Type_API (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_ID_AA64ISAR1_EL1_Type_API (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 11 8)


def _get_SCR_EL3_Type_API (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _get_HCR_EL2_Type_APK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _update_HCR_EL2_Type_APK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _update_SCR_EL3_Type_APK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_SCR_EL3_Type_APK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_HCR_EL2_Type_AT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)


def _update_HCR_EL2_Type_AT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)


def _update_ID_AA64MMFR2_EL1_Type_AT (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 35 32 x)


def _get_ID_AA64MMFR2_EL1_Type_AT (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 35 32)


def _get_HCR_EL2_Type_ATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)


def _update_HCR_EL2_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)


def _update_SCR_EL3_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_SCTLR_EL1_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)


def _update_SCTLR_EL2_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)


def _update_SCTLR_EL3_Type_ATA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)


def _get_SCR_EL3_Type_ATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_SCTLR_EL1_Type_ATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)


def _get_SCTLR_EL2_Type_ATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)


def _get_SCTLR_EL3_Type_ATA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)


def _get_HCR_EL2_Type_BSU (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _update_HCR_EL2_Type_BSU (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _update_HCR_Type_BSU (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _get_HCR_Type_BSU (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _get_HCR_EL2_Type_CD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 32 32)


def _update_HCR_EL2_Type_CD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 32 32 x)


def _update_HCR2_Type_CD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_HCR2_Type_CD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_HCR_EL2_Type_DC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_HCR_EL2_Type_DC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_HCR_Type_DC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_HCR_Type_DC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_HCR_EL2_Type_DCT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)


end ArmFull.Functions
