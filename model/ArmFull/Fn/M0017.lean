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

def num_of_AccessType (arg_ : AccessType) : Int :=
  match arg_ with
  | .AccessType_IFETCH => 0
  | .AccessType_GPR => 1
  | .AccessType_ASIMD => 2
  | .AccessType_SVE => 3
  | .AccessType_SME => 4
  | .AccessType_IC => 5
  | .AccessType_DC => 6
  | .AccessType_DCZero => 7
  | .AccessType_AT => 8
  | .AccessType_NV2 => 9
  | .AccessType_SPE => 10
  | .AccessType_GCS => 11
  | .AccessType_GPTW => 12
  | .AccessType_TTW => 13


def undefined_MemOp (ℓ : ChoiceLabel) (_ : Unit) : SailM MemOp := do
  (internal_pick_at (ℓ.child 0) [MemOp_LOAD, MemOp_STORE, MemOp_PREFETCH])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MemOp_of_num (arg_ : Nat) : MemOp :=
  match arg_ with
  | 0 => MemOp_LOAD
  | 1 => MemOp_STORE
  | _ => MemOp_PREFETCH


def num_of_MemOp (arg_ : MemOp) : Int :=
  match arg_ with
  | .MemOp_LOAD => 0
  | .MemOp_STORE => 1
  | .MemOp_PREFETCH => 2


def undefined_VARange (ℓ : ChoiceLabel) (_ : Unit) : SailM VARange := do
  (internal_pick_at (ℓ.child 0) [VARange_LOWER, VARange_UPPER])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def VARange_of_num (arg_ : Nat) : VARange :=
  match arg_ with
  | 0 => VARange_LOWER
  | _ => VARange_UPPER


def num_of_VARange (arg_ : VARange) : Int :=
  match arg_ with
  | .VARange_LOWER => 0
  | .VARange_UPPER => 1


def undefined_MemAtomicOp (ℓ : ChoiceLabel) (_ : Unit) : SailM MemAtomicOp := do
  (internal_pick_at (ℓ.child 0)
    [MemAtomicOp_GCSSS1, MemAtomicOp_ADD, MemAtomicOp_BIC, MemAtomicOp_EOR, MemAtomicOp_ORR, MemAtomicOp_SMAX, MemAtomicOp_SMIN, MemAtomicOp_UMAX, MemAtomicOp_UMIN, MemAtomicOp_SWP, MemAtomicOp_CAS])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 10 -/
def MemAtomicOp_of_num (arg_ : Nat) : MemAtomicOp :=
  match arg_ with
  | 0 => MemAtomicOp_GCSSS1
  | 1 => MemAtomicOp_ADD
  | 2 => MemAtomicOp_BIC
  | 3 => MemAtomicOp_EOR
  | 4 => MemAtomicOp_ORR
  | 5 => MemAtomicOp_SMAX
  | 6 => MemAtomicOp_SMIN
  | 7 => MemAtomicOp_UMAX
  | 8 => MemAtomicOp_UMIN
  | 9 => MemAtomicOp_SWP
  | _ => MemAtomicOp_CAS


def num_of_MemAtomicOp (arg_ : MemAtomicOp) : Int :=
  match arg_ with
  | .MemAtomicOp_GCSSS1 => 0
  | .MemAtomicOp_ADD => 1
  | .MemAtomicOp_BIC => 2
  | .MemAtomicOp_EOR => 3
  | .MemAtomicOp_ORR => 4
  | .MemAtomicOp_SMAX => 5
  | .MemAtomicOp_SMIN => 6
  | .MemAtomicOp_UMAX => 7
  | .MemAtomicOp_UMIN => 8
  | .MemAtomicOp_SWP => 9
  | .MemAtomicOp_CAS => 10


def undefined_CacheOp (ℓ : ChoiceLabel) (_ : Unit) : SailM CacheOp := do
  (internal_pick_at (ℓ.child 0) [CacheOp_Clean, CacheOp_Invalidate, CacheOp_CleanInvalidate])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def CacheOp_of_num (arg_ : Nat) : CacheOp :=
  match arg_ with
  | 0 => CacheOp_Clean
  | 1 => CacheOp_Invalidate
  | _ => CacheOp_CleanInvalidate


def num_of_CacheOp (arg_ : CacheOp) : Int :=
  match arg_ with
  | .CacheOp_Clean => 0
  | .CacheOp_Invalidate => 1
  | .CacheOp_CleanInvalidate => 2


def undefined_CacheOpScope (ℓ : ChoiceLabel) (_ : Unit) : SailM CacheOpScope := do
  (internal_pick_at (ℓ.child 0)
    [CacheOpScope_SetWay, CacheOpScope_PoU, CacheOpScope_PoC, CacheOpScope_PoE, CacheOpScope_PoP, CacheOpScope_PoDP, CacheOpScope_PoPA, CacheOpScope_ALLU, CacheOpScope_ALLUIS])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 8 -/
def CacheOpScope_of_num (arg_ : Nat) : CacheOpScope :=
  match arg_ with
  | 0 => CacheOpScope_SetWay
  | 1 => CacheOpScope_PoU
  | 2 => CacheOpScope_PoC
  | 3 => CacheOpScope_PoE
  | 4 => CacheOpScope_PoP
  | 5 => CacheOpScope_PoDP
  | 6 => CacheOpScope_PoPA
  | 7 => CacheOpScope_ALLU
  | _ => CacheOpScope_ALLUIS


def num_of_CacheOpScope (arg_ : CacheOpScope) : Int :=
  match arg_ with
  | .CacheOpScope_SetWay => 0
  | .CacheOpScope_PoU => 1
  | .CacheOpScope_PoC => 2
  | .CacheOpScope_PoE => 3
  | .CacheOpScope_PoP => 4
  | .CacheOpScope_PoDP => 5
  | .CacheOpScope_PoPA => 6
  | .CacheOpScope_ALLU => 7
  | .CacheOpScope_ALLUIS => 8


def undefined_CacheType (ℓ : ChoiceLabel) (_ : Unit) : SailM CacheType := do
  (internal_pick_at (ℓ.child 0)
    [CacheType_Data, CacheType_Tag, CacheType_Data_Tag, CacheType_Instruction])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def CacheType_of_num (arg_ : Nat) : CacheType :=
  match arg_ with
  | 0 => CacheType_Data
  | 1 => CacheType_Tag
  | 2 => CacheType_Data_Tag
  | _ => CacheType_Instruction


def num_of_CacheType (arg_ : CacheType) : Int :=
  match arg_ with
  | .CacheType_Data => 0
  | .CacheType_Tag => 1
  | .CacheType_Data_Tag => 2
  | .CacheType_Instruction => 3


def undefined_CachePASpace (ℓ : ChoiceLabel) (_ : Unit) : SailM CachePASpace := do
  (internal_pick_at (ℓ.child 0)
    [CPAS_NonSecure, CPAS_Any, CPAS_RealmNonSecure, CPAS_Realm, CPAS_Root, CPAS_SecureNonSecure, CPAS_Secure])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def CachePASpace_of_num (arg_ : Nat) : CachePASpace :=
  match arg_ with
  | 0 => CPAS_NonSecure
  | 1 => CPAS_Any
  | 2 => CPAS_RealmNonSecure
  | 3 => CPAS_Realm
  | 4 => CPAS_Root
  | 5 => CPAS_SecureNonSecure
  | _ => CPAS_Secure


def num_of_CachePASpace (arg_ : CachePASpace) : Int :=
  match arg_ with
  | .CPAS_NonSecure => 0
  | .CPAS_Any => 1
  | .CPAS_RealmNonSecure => 2
  | .CPAS_Realm => 3
  | .CPAS_Root => 4
  | .CPAS_SecureNonSecure => 5
  | .CPAS_Secure => 6


def undefined_MemType (ℓ : ChoiceLabel) (_ : Unit) : SailM MemType := do
  (internal_pick_at (ℓ.child 0) [MemType_Normal, MemType_Device])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 1 -/
def MemType_of_num (arg_ : Nat) : MemType :=
  match arg_ with
  | 0 => MemType_Normal
  | _ => MemType_Device


def num_of_MemType (arg_ : MemType) : Int :=
  match arg_ with
  | .MemType_Normal => 0
  | .MemType_Device => 1


def undefined_DeviceType (ℓ : ChoiceLabel) (_ : Unit) : SailM DeviceType := do
  (internal_pick_at (ℓ.child 0)
    [DeviceType_GRE, DeviceType_nGRE, DeviceType_nGnRE, DeviceType_nGnRnE])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def DeviceType_of_num (arg_ : Nat) : DeviceType :=
  match arg_ with
  | 0 => DeviceType_GRE
  | 1 => DeviceType_nGRE
  | 2 => DeviceType_nGnRE
  | _ => DeviceType_nGnRnE


def num_of_DeviceType (arg_ : DeviceType) : Int :=
  match arg_ with
  | .DeviceType_GRE => 0
  | .DeviceType_nGRE => 1
  | .DeviceType_nGnRE => 2
  | .DeviceType_nGnRnE => 3


def undefined_MemAttrHints (ℓ : ChoiceLabel) (_ : Unit) : SailM MemAttrHints := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 2) ) : SailM (BitVec 2) )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 2) ) : SailM (BitVec 2) )
  let w__2 ← (( do (undefined_bool_at (ℓ.child 2) ()) ) : SailM Bool )
  (pure ({ attrs := w__0
           hints := w__1
           transient := w__2 }))


def LOG2_TAG_GRANULE : Nat := 4


def MemAttr_NC : (BitVec 2) := 0b00#2


def MemAttr_WT : (BitVec 2) := 0b10#2


def MemAttr_WB : (BitVec 2) := 0b11#2


def MemHint_No : (BitVec 2) := 0b00#2


def MemHint_WA : (BitVec 2) := 0b01#2


def MemHint_RA : (BitVec 2) := 0b10#2


def MemHint_RWA : (BitVec 2) := 0b11#2


def undefined_Shareability (ℓ : ChoiceLabel) (_ : Unit) : SailM Shareability := do
  (internal_pick_at (ℓ.child 0) [Shareability_NSH, Shareability_ISH, Shareability_OSH])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def Shareability_of_num (arg_ : Nat) : Shareability :=
  match arg_ with
  | 0 => Shareability_NSH
  | 1 => Shareability_ISH
  | _ => Shareability_OSH


def num_of_Shareability (arg_ : Shareability) : Int :=
  match arg_ with
  | .Shareability_NSH => 0
  | .Shareability_ISH => 1
  | .Shareability_OSH => 2


def undefined_MemTagType (ℓ : ChoiceLabel) (_ : Unit) : SailM MemTagType := do
  (internal_pick_at (ℓ.child 0)
    [MemTag_Untagged, MemTag_AllocationTagged, MemTag_CanonicallyTagged])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MemTagType_of_num (arg_ : Nat) : MemTagType :=
  match arg_ with
  | 0 => MemTag_Untagged
  | 1 => MemTag_AllocationTagged
  | _ => MemTag_CanonicallyTagged


def num_of_MemTagType (arg_ : MemTagType) : Int :=
  match arg_ with
  | .MemTag_Untagged => 0
  | .MemTag_AllocationTagged => 1
  | .MemTag_CanonicallyTagged => 2


def undefined_PASpace (ℓ : ChoiceLabel) (_ : Unit) : SailM PASpace := do
  (internal_pick_at (ℓ.child 0) [PAS_NonSecure, PAS_Secure, PAS_Root, PAS_Realm])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def PASpace_of_num (arg_ : Nat) : PASpace :=
  match arg_ with
  | 0 => PAS_NonSecure
  | 1 => PAS_Secure
  | 2 => PAS_Root
  | _ => PAS_Realm


def num_of_PASpace (arg_ : PASpace) : Int :=
  match arg_ with
  | .PAS_NonSecure => 0
  | .PAS_Secure => 1
  | .PAS_Root => 2
  | .PAS_Realm => 3


def undefined_GPCF (ℓ : ChoiceLabel) (_ : Unit) : SailM GPCF := do
  (internal_pick_at (ℓ.child 0) [GPCF_None, GPCF_AddressSize, GPCF_Walk, GPCF_EABT, GPCF_Fail])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 4 -/
def GPCF_of_num (arg_ : Nat) : GPCF :=
  match arg_ with
  | 0 => GPCF_None
  | 1 => GPCF_AddressSize
  | 2 => GPCF_Walk
  | 3 => GPCF_EABT
  | _ => GPCF_Fail


def num_of_GPCF (arg_ : GPCF) : Int :=
  match arg_ with
  | .GPCF_None => 0
  | .GPCF_AddressSize => 1
  | .GPCF_Walk => 2
  | .GPCF_EABT => 3
  | .GPCF_Fail => 4


def undefined_Fault (ℓ : ChoiceLabel) (_ : Unit) : SailM Fault := do
  (internal_pick_at (ℓ.child 0)
    [Fault_None, Fault_AccessFlag, Fault_Alignment, Fault_Background, Fault_Domain, Fault_Permission, Fault_Translation, Fault_AddressSize, Fault_SyncExternal, Fault_SyncExternalOnWalk, Fault_SyncParity, Fault_SyncParityOnWalk, Fault_GPCFOnWalk, Fault_GPCFOnOutput, Fault_AsyncParity, Fault_AsyncExternal, Fault_TagCheck, Fault_Debug, Fault_TLBConflict, Fault_BranchTarget, Fault_HWUpdateAccessFlag, Fault_Lockdown, Fault_Exclusive, Fault_ICacheMaint])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 23 -/
def Fault_of_num (arg_ : Nat) : Fault :=
  match arg_ with
  | 0 => Fault_None
  | 1 => Fault_AccessFlag
  | 2 => Fault_Alignment
  | 3 => Fault_Background
  | 4 => Fault_Domain
  | 5 => Fault_Permission
  | 6 => Fault_Translation
  | 7 => Fault_AddressSize
  | 8 => Fault_SyncExternal
  | 9 => Fault_SyncExternalOnWalk
  | 10 => Fault_SyncParity
  | 11 => Fault_SyncParityOnWalk
  | 12 => Fault_GPCFOnWalk
  | 13 => Fault_GPCFOnOutput
  | 14 => Fault_AsyncParity
  | 15 => Fault_AsyncExternal
  | 16 => Fault_TagCheck
  | 17 => Fault_Debug
  | 18 => Fault_TLBConflict
  | 19 => Fault_BranchTarget
  | 20 => Fault_HWUpdateAccessFlag
  | 21 => Fault_Lockdown
  | 22 => Fault_Exclusive
  | _ => Fault_ICacheMaint


def num_of_Fault (arg_ : Fault) : Int :=
  match arg_ with
  | .Fault_None => 0
  | .Fault_AccessFlag => 1
  | .Fault_Alignment => 2
  | .Fault_Background => 3
  | .Fault_Domain => 4
  | .Fault_Permission => 5
  | .Fault_Translation => 6
  | .Fault_AddressSize => 7
  | .Fault_SyncExternal => 8
  | .Fault_SyncExternalOnWalk => 9
  | .Fault_SyncParity => 10
  | .Fault_SyncParityOnWalk => 11
  | .Fault_GPCFOnWalk => 12
  | .Fault_GPCFOnOutput => 13
  | .Fault_AsyncParity => 14
  | .Fault_AsyncExternal => 15
  | .Fault_TagCheck => 16
  | .Fault_Debug => 17
  | .Fault_TLBConflict => 18
  | .Fault_BranchTarget => 19
  | .Fault_HWUpdateAccessFlag => 20
  | .Fault_Lockdown => 21
  | .Fault_Exclusive => 22
  | .Fault_ICacheMaint => 23


def undefined_ErrorState (ℓ : ChoiceLabel) (_ : Unit) : SailM ErrorState := do
  (internal_pick_at (ℓ.child 0)
    [ErrorState_UC, ErrorState_UEU, ErrorState_UEO, ErrorState_UER, ErrorState_CE, ErrorState_Uncategorized, ErrorState_IMPDEF])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 6 -/
def ErrorState_of_num (arg_ : Nat) : ErrorState :=
  match arg_ with
  | 0 => ErrorState_UC
  | 1 => ErrorState_UEU
  | 2 => ErrorState_UEO
  | 3 => ErrorState_UER
  | 4 => ErrorState_CE
  | 5 => ErrorState_Uncategorized
  | _ => ErrorState_IMPDEF


def num_of_ErrorState (arg_ : ErrorState) : Int :=
  match arg_ with
  | .ErrorState_UC => 0
  | .ErrorState_UEU => 1
  | .ErrorState_UEO => 2
  | .ErrorState_UER => 3
  | .ErrorState_CE => 4
  | .ErrorState_Uncategorized => 5
  | .ErrorState_IMPDEF => 6


def undefined_Permissions (ℓ : ChoiceLabel) (_ : Unit) : SailM Permissions := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 2) ) : SailM (BitVec 2) )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 1) ) : SailM (BitVec 1) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 1) ) : SailM (BitVec 1) )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 3) ) : SailM (BitVec 3) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 1) ) : SailM (BitVec 1) )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 1) ) : SailM (BitVec 1) )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do (undefined_bitvector_at (ℓ.child 8) 4) ) : SailM (BitVec 4) )
  let w__9 ← (( do (undefined_bitvector_at (ℓ.child 9) 4) ) : SailM (BitVec 4) )
  let w__10 ← (( do (undefined_bitvector_at (ℓ.child 10) 1) ) : SailM (BitVec 1) )
  let w__11 ← (( do (undefined_bitvector_at (ℓ.child 11) 4) ) : SailM (BitVec 4) )
  let w__12 ← (( do (undefined_bitvector_at (ℓ.child 12) 1) ) : SailM (BitVec 1) )
  let w__13 ← (( do (undefined_bitvector_at (ℓ.child 13) 4) ) : SailM (BitVec 4) )
  let w__14 ← (( do (undefined_bitvector_at (ℓ.child 14) 4) ) : SailM (BitVec 4) )
  let w__15 ← (( do (undefined_bitvector_at (ℓ.child 15) 2) ) : SailM (BitVec 2) )
  let w__16 ← (( do (undefined_bitvector_at (ℓ.child 16) 1) ) : SailM (BitVec 1) )
  let w__17 ← (( do (undefined_bitvector_at (ℓ.child 17) 1) ) : SailM (BitVec 1) )
  let w__18 ← (( do (undefined_bitvector_at (ℓ.child 18) 1) ) : SailM (BitVec 1) )
  (pure ({ ap_table := w__0
           xn_table := w__1
           pxn_table := w__2
           uxn_table := w__3
           ap := w__4
           xn := w__5
           uxn := w__6
           pxn := w__7
           ppi := w__8
           upi := w__9
           ndirty := w__10
           s2pi := w__11
           s2dirty := w__12
           po_index := w__13
           s2po_index := w__14
           s2ap := w__15
           s2tag_na := w__16
           s2xnx := w__17
           s2xn := w__18 }))


def undefined_S1AccessControls (ℓ : ChoiceLabel) (_ : Unit) : SailM S1AccessControls := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 1) ) : SailM (BitVec 1) )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 1) ) : SailM (BitVec 1) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 1) ) : SailM (BitVec 1) )
  let w__4 ← (( do (undefined_bool_at (ℓ.child 4) ()) ) : SailM Bool )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 1) ) : SailM (BitVec 1) )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 1) ) : SailM (BitVec 1) )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do (undefined_bitvector_at (ℓ.child 8) 1) ) : SailM (BitVec 1) )
  (pure ({ r := w__0
           w := w__1
           x := w__2
           gcs := w__3
           overlay := w__4
           or := w__5
           ow := w__6
           ox := w__7
           wxn := w__8 }))


def undefined_S2AccessControls (ℓ : ChoiceLabel) (_ : Unit) : SailM S2AccessControls := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 1) ) : SailM (BitVec 1) )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 1) ) : SailM (BitVec 1) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 1) ) : SailM (BitVec 1) )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 1) ) : SailM (BitVec 1) )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 1) ) : SailM (BitVec 1) )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do (undefined_bitvector_at (ℓ.child 8) 1) ) : SailM (BitVec 1) )
  let w__9 ← (( do (undefined_bool_at (ℓ.child 9) ()) ) : SailM Bool )
  let w__10 ← (( do (undefined_bitvector_at (ℓ.child 10) 1) ) : SailM (BitVec 1) )
  let w__11 ← (( do (undefined_bitvector_at (ℓ.child 11) 1) ) : SailM (BitVec 1) )
  let w__12 ← (( do (undefined_bitvector_at (ℓ.child 12) 1) ) : SailM (BitVec 1) )
  let w__13 ← (( do (undefined_bitvector_at (ℓ.child 13) 1) ) : SailM (BitVec 1) )
  let w__14 ← (( do (undefined_bitvector_at (ℓ.child 14) 1) ) : SailM (BitVec 1) )
  let w__15 ← (( do (undefined_bitvector_at (ℓ.child 15) 1) ) : SailM (BitVec 1) )
  let w__16 ← (( do (undefined_bitvector_at (ℓ.child 16) 1) ) : SailM (BitVec 1) )
  (pure ({ r := w__0
           w := w__1
           x := w__2
           r_rcw := w__3
           w_rcw := w__4
           r_mmu := w__5
           w_mmu := w__6
           toplevel0 := w__7
           toplevel1 := w__8
           overlay := w__9
           or := w__10
           ow := w__11
           ox := w__12
           or_rcw := w__13
           ow_rcw := w__14
           or_mmu := w__15
           ow_mmu := w__16 }))


def undefined_MBReqDomain (ℓ : ChoiceLabel) (_ : Unit) : SailM MBReqDomain := do
  (internal_pick_at (ℓ.child 0)
    [MBReqDomain_Nonshareable, MBReqDomain_InnerShareable, MBReqDomain_OuterShareable, MBReqDomain_FullSystem])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def MBReqDomain_of_num (arg_ : Nat) : MBReqDomain :=
  match arg_ with
  | 0 => MBReqDomain_Nonshareable
  | 1 => MBReqDomain_InnerShareable
  | 2 => MBReqDomain_OuterShareable
  | _ => MBReqDomain_FullSystem


def num_of_MBReqDomain (arg_ : MBReqDomain) : Int :=
  match arg_ with
  | .MBReqDomain_Nonshareable => 0
  | .MBReqDomain_InnerShareable => 1
  | .MBReqDomain_OuterShareable => 2
  | .MBReqDomain_FullSystem => 3


def undefined_MBReqTypes (ℓ : ChoiceLabel) (_ : Unit) : SailM MBReqTypes := do
  (internal_pick_at (ℓ.child 0) [MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def MBReqTypes_of_num (arg_ : Nat) : MBReqTypes :=
  match arg_ with
  | 0 => MBReqTypes_Reads
  | 1 => MBReqTypes_Writes
  | _ => MBReqTypes_All


def num_of_MBReqTypes (arg_ : MBReqTypes) : Int :=
  match arg_ with
  | .MBReqTypes_Reads => 0
  | .MBReqTypes_Writes => 1
  | .MBReqTypes_All => 2


def undefined_PrefetchHint (ℓ : ChoiceLabel) (_ : Unit) : SailM PrefetchHint := do
  (internal_pick_at (ℓ.child 0) [Prefetch_READ, Prefetch_WRITE, Prefetch_EXEC])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def PrefetchHint_of_num (arg_ : Nat) : PrefetchHint :=
  match arg_ with
  | 0 => Prefetch_READ
  | 1 => Prefetch_WRITE
  | _ => Prefetch_EXEC


def num_of_PrefetchHint (arg_ : PrefetchHint) : Int :=
  match arg_ with
  | .Prefetch_READ => 0
  | .Prefetch_WRITE => 1
  | .Prefetch_EXEC => 2


def undefined_Unpredictable (ℓ : ChoiceLabel) (_ : Unit) : SailM Unpredictable := do
  (internal_pick_at (ℓ.child 0)
    [Unpredictable_VMSR, Unpredictable_WBOVERLAPLD, Unpredictable_WBOVERLAPST, Unpredictable_LDPOVERLAP, Unpredictable_BASEOVERLAP, Unpredictable_DATAOVERLAP, Unpredictable_DEVPAGE2, Unpredictable_INSTRDEVICE, Unpredictable_RESCPACR, Unpredictable_RESMAIR, Unpredictable_S1CTAGGED, Unpredictable_S2RESMEMATTR, Unpredictable_RESTEXCB, Unpredictable_RESPRRR, Unpredictable_RESDACR, Unpredictable_RESVTCRS, Unpredictable_RESTnSZ, Unpredictable_RESTCF, Unpredictable_DEVICETAGSTORE, Unpredictable_OORTnSZ, Unpredictable_LARGEIPA, Unpredictable_ESRCONDPASS, Unpredictable_ILZEROIT, Unpredictable_ILZEROT, Unpredictable_BPVECTORCATCHPRI, Unpredictable_VCMATCHHALF, Unpredictable_VCMATCHDAPA, Unpredictable_WPMASKANDBAS, Unpredictable_WPBASCONTIGUOUS, Unpredictable_RESWPMASK, Unpredictable_WPMASKEDBITS, Unpredictable_RESBPWPCTRL, Unpredictable_BPNOTIMPL, Unpredictable_RESBPTYPE, Unpredictable_RESMDSELR, Unpredictable_BPNOTCTXCMP, Unpredictable_BPMATCHHALF, Unpredictable_BPMISMATCHHALF, Unpredictable_BPLINKINGDISABLED, Unpredictable_RESBPMASK, Unpredictable_BPMASK, Unpredictable_BPMASKEDBITS, Unpredictable_BPLINKEDADDRMATCH, Unpredictable_RESTARTALIGNPC, Unpredictable_RESTARTZEROUPPERPC, Unpredictable_ZEROUPPER, Unpredictable_ERETZEROUPPERPC, Unpredictable_A32FORCEALIGNPC, Unpredictable_SMD, Unpredictable_NONFAULT, Unpredictable_SVEZEROUPPER, Unpredictable_SVELDNFDATA, Unpredictable_SVELDNFZERO, Unpredictable_CHECKSPNONEACTIVE, Unpredictable_SMEZEROUPPER, Unpredictable_NVNV1, Unpredictable_Shareability, Unpredictable_AFUPDATE, Unpredictable_DBUPDATE, Unpredictable_IESBinDebug, Unpredictable_BADPMSFCR, Unpredictable_ZEROBTYPE, Unpredictable_EL2TIMESTAMP, Unpredictable_EL1TIMESTAMP, Unpredictable_RESERVEDNSxB, Unpredictable_WFxTDEBUG, Unpredictable_LS64UNSUPPORTED, Unpredictable_MISALIGNEDATOMIC, Unpredictable_CLEARERRITEZERO, Unpredictable_ALUEXCEPTIONRETURN, Unpredictable_IGNORETRAPINDEBUG, Unpredictable_DBGxVR_RESS, Unpredictable_PMUEVENTCOUNTER, Unpredictable_PMSCR_PCT, Unpredictable_CounterReservedForEL2, Unpredictable_BRBFILTRATE, Unpredictable_MOPSOVERLAP31, Unpredictable_STOREONLYTAGCHECKEDCAS, Unpredictable_RESTC])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 78 -/
def Unpredictable_of_num (arg_ : Nat) : Unpredictable :=
  match arg_ with
  | 0 => Unpredictable_VMSR
  | 1 => Unpredictable_WBOVERLAPLD
  | 2 => Unpredictable_WBOVERLAPST
  | 3 => Unpredictable_LDPOVERLAP
  | 4 => Unpredictable_BASEOVERLAP
  | 5 => Unpredictable_DATAOVERLAP
  | 6 => Unpredictable_DEVPAGE2
  | 7 => Unpredictable_INSTRDEVICE
  | 8 => Unpredictable_RESCPACR
  | 9 => Unpredictable_RESMAIR
  | 10 => Unpredictable_S1CTAGGED
  | 11 => Unpredictable_S2RESMEMATTR
  | 12 => Unpredictable_RESTEXCB
  | 13 => Unpredictable_RESPRRR
  | 14 => Unpredictable_RESDACR
  | 15 => Unpredictable_RESVTCRS
  | 16 => Unpredictable_RESTnSZ
  | 17 => Unpredictable_RESTCF
  | 18 => Unpredictable_DEVICETAGSTORE
  | 19 => Unpredictable_OORTnSZ
  | 20 => Unpredictable_LARGEIPA
  | 21 => Unpredictable_ESRCONDPASS
  | 22 => Unpredictable_ILZEROIT
  | 23 => Unpredictable_ILZEROT
  | 24 => Unpredictable_BPVECTORCATCHPRI
  | 25 => Unpredictable_VCMATCHHALF
  | 26 => Unpredictable_VCMATCHDAPA
  | 27 => Unpredictable_WPMASKANDBAS
  | 28 => Unpredictable_WPBASCONTIGUOUS
  | 29 => Unpredictable_RESWPMASK
  | 30 => Unpredictable_WPMASKEDBITS
  | 31 => Unpredictable_RESBPWPCTRL
  | 32 => Unpredictable_BPNOTIMPL
  | 33 => Unpredictable_RESBPTYPE
  | 34 => Unpredictable_RESMDSELR
  | 35 => Unpredictable_BPNOTCTXCMP
  | 36 => Unpredictable_BPMATCHHALF
  | 37 => Unpredictable_BPMISMATCHHALF
  | 38 => Unpredictable_BPLINKINGDISABLED
  | 39 => Unpredictable_RESBPMASK
  | 40 => Unpredictable_BPMASK
  | 41 => Unpredictable_BPMASKEDBITS
  | 42 => Unpredictable_BPLINKEDADDRMATCH
  | 43 => Unpredictable_RESTARTALIGNPC
  | 44 => Unpredictable_RESTARTZEROUPPERPC
  | 45 => Unpredictable_ZEROUPPER
  | 46 => Unpredictable_ERETZEROUPPERPC
  | 47 => Unpredictable_A32FORCEALIGNPC
  | 48 => Unpredictable_SMD
  | 49 => Unpredictable_NONFAULT
  | 50 => Unpredictable_SVEZEROUPPER
  | 51 => Unpredictable_SVELDNFDATA
  | 52 => Unpredictable_SVELDNFZERO
  | 53 => Unpredictable_CHECKSPNONEACTIVE
  | 54 => Unpredictable_SMEZEROUPPER
  | 55 => Unpredictable_NVNV1
  | 56 => Unpredictable_Shareability
  | 57 => Unpredictable_AFUPDATE
  | 58 => Unpredictable_DBUPDATE
  | 59 => Unpredictable_IESBinDebug
  | 60 => Unpredictable_BADPMSFCR
  | 61 => Unpredictable_ZEROBTYPE
  | 62 => Unpredictable_EL2TIMESTAMP
  | 63 => Unpredictable_EL1TIMESTAMP
  | 64 => Unpredictable_RESERVEDNSxB
  | 65 => Unpredictable_WFxTDEBUG
  | 66 => Unpredictable_LS64UNSUPPORTED
  | 67 => Unpredictable_MISALIGNEDATOMIC
  | 68 => Unpredictable_CLEARERRITEZERO
  | 69 => Unpredictable_ALUEXCEPTIONRETURN
  | 70 => Unpredictable_IGNORETRAPINDEBUG
  | 71 => Unpredictable_DBGxVR_RESS
  | 72 => Unpredictable_PMUEVENTCOUNTER
  | 73 => Unpredictable_PMSCR_PCT
  | 74 => Unpredictable_CounterReservedForEL2
  | 75 => Unpredictable_BRBFILTRATE
  | 76 => Unpredictable_MOPSOVERLAP31
  | 77 => Unpredictable_STOREONLYTAGCHECKEDCAS
  | _ => Unpredictable_RESTC


end ArmFull.Functions
