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

def SHAmajority (x : (BitVec 32)) (y : (BitVec 32)) (z : (BitVec 32)) : (BitVec 32) :=
  ((x &&& y) ||| ((x ||| y) &&& z))


def Sbox (sboxin : (BitVec 8)) : (BitVec 8) :=
  let sboxstring : (BitVec 2048) :=
    0xD690E9FECCE13DB716B614C228FB2C052B679A762ABE04C3AA441326498606999C4250F491EF987A33540B43EDCFAC62E4B31CA9C908E89580DF94FA758F3FA64707A7FCF37317BA83593C19E6854FA8686B81B27164DA8BF8EB0F4B70569D351E240E5E6358D1A225227C3B01217887D40046579FD327524C3602E7A0C4C89EEABF8AD240C738B5A3F7F2CEF96115A1E0AE5DA49B341A55AD933230F58CB1E31DF6E22E8266CA60C02923AB0D534E6FD5DB3745DEFD8E2F03FF6A726D6C5B518D1BAF92BBDDBC7F11D95C411F105AD80AC13188A5CD7BBD2D74D012B8E5B4B08969974A0C96777E65B9F109C56EC68418F07DEC3ADC4D2079EE5F3ED7CB3948#2048
  let sboxin : Int := (BitVec.toNat sboxin)
  (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb sboxstring
    (Sail.Int.toNatChecked ((((255 -i sboxin) *i 8) +i 7)))
    (Sail.Int.toNatChecked (((255 -i sboxin) *i 8)))))


def RESTRICT_PREDICTIONS (c : ExecutionCntxt) : Unit :=
  ()


def undefined_CONTEXTIDR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CONTEXTIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CONTEXTIDR_EL1_Type_PROCID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_CONTEXTIDR_EL1_Type_PROCID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_CONTEXTIDR_EL2_Type_PROCID (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_CONTEXTIDR_EL2_Type_PROCID (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def undefined_TTBCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_TTBCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_TTBCR_Type_EAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_TTBCR_Type_EAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_TTBCR_Type_PD0 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_TTBCR_Type_PD0 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_TTBCR_Type_PD1 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_TTBCR_Type_PD1 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_TTBCR_Type_T2E (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_TTBCR_Type_T2E (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def TTBCR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _TTBCR_NS ) : SailM TTBCR_Type )
  let w__0 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_CONTEXTIDR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_CONTEXTIDR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_CONTEXTIDR_Type_ASID (v : (BitVec 32)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 7 0)


def _update_CONTEXTIDR_Type_ASID (v : (BitVec 32)) (x : (BitVec 8)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 0 x)


def _update_TTBR0_EL1_Type_ASID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def _update_TTBR0_EL2_Type_ASID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def _update_TTBR0_Type_ASID (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _update_TTBR1_EL1_Type_ASID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def _update_TTBR1_EL2_Type_ASID (v : (BitVec 128)) (x : (BitVec 16)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def _update_TTBR1_Type_ASID (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 48 x)


def _get_TTBR0_EL1_Type_ASID (v : (BitVec 128)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _get_TTBR0_EL2_Type_ASID (v : (BitVec 128)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _get_TTBR0_Type_ASID (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def _get_TTBR1_EL1_Type_ASID (v : (BitVec 128)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _get_TTBR1_EL2_Type_ASID (v : (BitVec 128)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _get_TTBR1_Type_ASID (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 55 48)


def CONTEXTIDR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _CONTEXTIDR_NS ) : SailM CONTEXTIDR_Type )
  let w__0 ← (( do readReg CONTEXTIDR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_TTBR0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TTBR0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_TTBR0_Type_BADDR (v : (BitVec 64)) : (BitVec 47) :=
  (Sail.BitVec.extractLsb v 47 1)


def _update_TTBR0_Type_BADDR (v : (BitVec 64)) (x : (BitVec 47)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 1 x)


def _update_GPTBR_EL3_Type_BADDR (v : (BitVec 64)) (x : (BitVec 40)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 0 x)


def _update_HTTBR_Type_BADDR (v : (BitVec 64)) (x : (BitVec 47)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 1 x)


def _update_TTBR1_Type_BADDR (v : (BitVec 64)) (x : (BitVec 47)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 1 x)


def _update_VNCR_EL2_Type_BADDR (v : (BitVec 64)) (x : (BitVec 45)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 12 x)


def _update_VTTBR_Type_BADDR (v : (BitVec 64)) (x : (BitVec 47)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 1 x)


def _get_GPTBR_EL3_Type_BADDR (v : (BitVec 64)) : (BitVec 40) :=
  (Sail.BitVec.extractLsb v 39 0)


def _get_HTTBR_Type_BADDR (v : (BitVec 64)) : (BitVec 47) :=
  (Sail.BitVec.extractLsb v 47 1)


def _get_TTBR1_Type_BADDR (v : (BitVec 64)) : (BitVec 47) :=
  (Sail.BitVec.extractLsb v 47 1)


def _get_VNCR_EL2_Type_BADDR (v : (BitVec 64)) : (BitVec 45) :=
  (Sail.BitVec.extractLsb v 56 12)


def _get_VTTBR_Type_BADDR (v : (BitVec 64)) : (BitVec 47) :=
  (Sail.BitVec.extractLsb v 47 1)


def _get_TTBR0_Type_CnP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_TTBR0_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_HTTBR_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_ID_AA64MMFR2_EL1_Type_CnP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_ID_MMFR4_EL1_Type_CnP (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_ID_MMFR4_Type_CnP (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 12 x)


def _update_TTBR0_EL1_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TTBR0_EL2_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TTBR0_EL3_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TTBR1_EL1_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TTBR1_EL2_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_TTBR1_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_VSTTBR_EL2_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_VTTBR_EL2_Type_CnP (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_VTTBR_Type_CnP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_HTTBR_Type_CnP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_ID_AA64MMFR2_EL1_Type_CnP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_ID_MMFR4_EL1_Type_CnP (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_ID_MMFR4_Type_CnP (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 15 12)


def _get_TTBR0_EL1_Type_CnP (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TTBR0_EL2_Type_CnP (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TTBR0_EL3_Type_CnP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TTBR1_EL1_Type_CnP (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TTBR1_EL2_Type_CnP (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TTBR1_Type_CnP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_VSTTBR_EL2_Type_CnP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_VTTBR_EL2_Type_CnP (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_VTTBR_Type_CnP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_TTBR0_Type_IRGN (v : (BitVec 64)) : (BitVec 2) :=
  ((Sail.BitVec.extractLsb v 0 0) +++ (Sail.BitVec.extractLsb v 6 6))


def _update_TTBR0_Type_IRGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 0 0
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((2 -i 1)))
        (Sail.Int.toNatChecked ((((2 -i 1) -i ((0 -i 0) +i 1)) +i 1))))) 6 6
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((2 -i 1) -i ((0 -i 0) +i 1))))
      (Sail.Int.toNatChecked (((((2 -i 1) -i ((0 -i 0) +i 1)) -i ((6 -i 6) +i 1)) +i 1)))))


def _update_GPCCR_EL3_Type_IRGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _update_TTBR1_Type_IRGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 6 6
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((2 -i 1)))
        (Sail.Int.toNatChecked ((((2 -i 1) -i ((6 -i 6) +i 1)) +i 1))))) 0 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((2 -i 1) -i ((6 -i 6) +i 1))))
      (Sail.Int.toNatChecked (((((2 -i 1) -i ((6 -i 6) +i 1)) -i ((0 -i 0) +i 1)) +i 1)))))


def _get_GPCCR_EL3_Type_IRGN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _get_TTBR1_Type_IRGN (v : (BitVec 64)) : (BitVec 2) :=
  ((Sail.BitVec.extractLsb v 6 6) +++ (Sail.BitVec.extractLsb v 0 0))


def _get_TTBR0_Type_NOS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_TTBR0_Type_NOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_PAR_Type_NOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_TTBR1_Type_NOS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_PAR_Type_NOS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_TTBR1_Type_NOS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_TTBR0_Type_RGN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)


def _update_TTBR0_Type_RGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 3 x)


def _update_TTBR1_Type_RGN (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 3 x)


def _get_TTBR1_Type_RGN (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 4 3)


def _get_TTBR0_Type_TTB0 (v : (BitVec 64)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 31 7)


def _update_TTBR0_Type_TTB0 (v : (BitVec 64)) (x : (BitVec 25)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 7 x)


def undefined_TTBR0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector_at (ℓ.child 0) 128)


def Mk_TTBR0_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v


def _get_TTBR0_EL1_Type_SKL (v : (BitVec 128)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _update_TTBR0_EL1_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _update_TTBR0_EL2_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _update_TTBR0_EL3_Type_SKL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _update_TTBR1_EL1_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _update_TTBR1_EL2_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _update_VSTTBR_EL2_Type_SKL (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _update_VTTBR_EL2_Type_SKL (v : (BitVec 128)) (x : (BitVec 2)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 2 1 x)


def _get_TTBR0_EL2_Type_SKL (v : (BitVec 128)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _get_TTBR0_EL3_Type_SKL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _get_TTBR1_EL1_Type_SKL (v : (BitVec 128)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _get_TTBR1_EL2_Type_SKL (v : (BitVec 128)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _get_VSTTBR_EL2_Type_SKL (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def _get_VTTBR_EL2_Type_SKL (v : (BitVec 128)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 2 1)


def undefined_HTTBR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_HTTBR_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_TTBR0_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector_at (ℓ.child 0) 128)


def Mk_TTBR0_EL2_Type (v : (BitVec 128)) : (BitVec 128) :=
  v


def TTBR0_EL2_read (_ : Unit) : SailM (BitVec 128) := do
  let r ← (( do readReg _TTBR0_EL2 ) : SailM TTBR0_EL2_Type )
  let w__0 ← (( do readReg HTTBR ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 47 1 (BitVec.slice w__0 1 47)) : (BitVec 128))
  (pure (r))


def undefined_TTBR1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_TTBR1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_TTBR1_Type_TTB1 (v : (BitVec 64)) : (BitVec 25) :=
  (Sail.BitVec.extractLsb v 31 7)


def _update_TTBR1_Type_TTB1 (v : (BitVec 64)) (x : (BitVec 25)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 7 x)


def undefined_TTBR1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector_at (ℓ.child 0) 128)


def Mk_TTBR1_EL1_Type (v : (BitVec 128)) : (BitVec 128) :=
  v


def undefined_TTBR1_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 128) := do
  (undefined_bitvector_at (ℓ.child 0) 128)


def Mk_TTBR1_EL2_Type (v : (BitVec 128)) : (BitVec 128) :=
  v


def IsExternalSyncAbort (statuscode : Fault) : SailM Bool := do
  ArmFull.assert (bne statuscode Fault_None) "sail-arm/v8_base.sail:13362.35-13362.36"
  (pure (((BEq.beq statuscode Fault_SyncExternal) || ((BEq.beq statuscode Fault_SyncParity) || ((BEq.beq
            statuscode Fault_SyncExternalOnWalk) || (BEq.beq statuscode Fault_SyncParityOnWalk))))))


def PendSErrorInterrupt (fault : FaultRecord) : Unit :=
  ()


def IsAsyncAbort (statuscode : Fault) : SailM Bool := do
  ArmFull.assert (bne statuscode Fault_None) "sail-arm/v8_base.sail:13606.35-13606.36"
  (pure (((BEq.beq statuscode Fault_AsyncExternal) || (BEq.beq statuscode Fault_AsyncParity))))


def IsExternalAbort (statuscode : Fault) : SailM Bool := do
  ArmFull.assert (bne statuscode Fault_None) "sail-arm/v8_base.sail:13619.35-13619.36"
  (pure (((BEq.beq statuscode Fault_SyncExternal) || ((BEq.beq statuscode Fault_SyncParity) || ((BEq.beq
            statuscode Fault_SyncExternalOnWalk) || ((BEq.beq statuscode Fault_SyncParityOnWalk) || ((BEq.beq
                statuscode Fault_AsyncExternal) || (BEq.beq statuscode Fault_AsyncParity))))))))


def IsSecondStage (fault : FaultRecord) : SailM Bool := do
  ArmFull.assert (bne fault.statuscode Fault_None) "sail-arm/v8_base.sail:13630.41-13630.42"
  (pure (fault.secondstage))


def IPAValid (fault : FaultRecord) : SailM Bool := do
  ArmFull.assert (bne fault.statuscode Fault_None) "sail-arm/v8_base.sail:13675.41-13675.42"
  (pure (if ((bne fault.gpcf.gpf GPCF_None) : Bool)
    then fault.secondstage
    else
      (if (fault.s2fs1walk : Bool)
      then
        ((BEq.beq fault.statuscode Fault_AccessFlag) || ((BEq.beq fault.statuscode Fault_Permission) || ((BEq.beq
                fault.statuscode Fault_Translation) || (BEq.beq fault.statuscode Fault_AddressSize))))
      else
        (if (fault.secondstage : Bool)
        then
          ((BEq.beq fault.statuscode Fault_AccessFlag) || ((BEq.beq fault.statuscode
                Fault_Translation) || (BEq.beq fault.statuscode Fault_AddressSize)))
        else false))))


def HDFAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HDFAR_Type := value_name
  let w__0 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
  writeReg FAR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HDFAR r


def HIFAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HIFAR_Type := value_name
  let w__0 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
  writeReg FAR_EL2 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _HIFAR r


def undefined_HPFAR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_HPFAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HPFAR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HPFAR ) : SailM HPFAR_Type )
  let w__0 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def HPFAR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HPFAR_Type := value_name
  let w__0 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
  writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HPFAR r


def undefined_HSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_HSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HSR_Type := value_name
  let w__0 ← (( do readReg ESR_EL2 ) : SailM (BitVec 64) )
  writeReg ESR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HSR r


def ELR_hyp_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ELR_hyp_Type := value_name
  let w__0 ← (( do readReg ELR_EL2 ) : SailM (BitVec 64) )
  writeReg ELR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _ELR_hyp r


def HVBAR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HVBAR ) : SailM HVBAR_Type )
  let w__0 ← (( do readReg VBAR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_MVBAR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_MVBAR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_MVBAR_Type_Reserved (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _update_MVBAR_Type_Reserved (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def DFAR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DFAR_Type := value_name
  let w__0 ← (( do readReg FAR_EL1 ) : SailM (BitVec 64) )
  writeReg FAR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DFAR_NS r


def HDFAR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HDFAR ) : SailM HDFAR_Type )
  let w__0 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_DFSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DFSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DFSR_Type_AET (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_DFSR_Type_AET (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_DISR_EL1_Type_AET (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 10 x)


def _update_VDFSR_Type_AET (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_VDISR_EL2_Type_AET (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_VDISR_Type_AET (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_VSESR_EL2_Type_AET (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_DISR_EL1_Type_AET (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 12 10)


def _get_VDFSR_Type_AET (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_VDISR_EL2_Type_AET (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_VDISR_Type_AET (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_VSESR_EL2_Type_AET (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_DFSR_Type_CM (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_DFSR_Type_CM (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _update_EDHSR_Type_CM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_EDHSR_Type_CM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _get_DFSR_Type_Domain (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 7 4)


def _update_DFSR_Type_Domain (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 4 x)


def _get_DFSR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_DFSR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_DISR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_IFSR32_EL2_Type_ExT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_IFSR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_VDFSR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_VDISR_EL2_Type_ExT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_VDISR_Type_ExT (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


end ArmFull.Functions
