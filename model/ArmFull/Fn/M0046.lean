module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork set_option backward.proofsInPublic true @[expose] public section

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

def AESInvShiftRows (op : (BitVec 128)) : (BitVec 128) :=
  ((((((((((((((((Sail.BitVec.extractLsb op 31 24) +++ (Sail.BitVec.extractLsb op 55 48)) +++ (Sail.BitVec.extractLsb
                                op 79 72)) +++ (Sail.BitVec.extractLsb op 103 96)) +++ (Sail.BitVec.extractLsb
                            op 127 120)) +++ (Sail.BitVec.extractLsb op 23 16)) +++ (Sail.BitVec.extractLsb
                        op 47 40)) +++ (Sail.BitVec.extractLsb op 71 64)) +++ (Sail.BitVec.extractLsb
                    op 95 88)) +++ (Sail.BitVec.extractLsb op 119 112)) +++ (Sail.BitVec.extractLsb
                op 15 8)) +++ (Sail.BitVec.extractLsb op 39 32)) +++ (Sail.BitVec.extractLsb op 63
            56)) +++ (Sail.BitVec.extractLsb op 87 80)) +++ (Sail.BitVec.extractLsb op 111 104)) +++ (Sail.BitVec.extractLsb
      op 7 0))


def FFmul02 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_02 : (BitVec 2048) :=
    (((((((((((((((0xE5E7E1E3EDEFE9EBF5F7F1F3FDFFF9FB#128 +++ 0xC5C7C1C3CDCFC9CBD5D7D1D3DDDFD9DB#128) +++ 0xA5A7A1A3ADAFA9ABB5B7B1B3BDBFB9BB#128) +++ 0x858781838D8F898B959791939D9F999B#128) +++ 0x656761636D6F696B757771737D7F797B#128) +++ 0x454741434D4F494B555751535D5F595B#128) +++ 0x252721232D2F292B353731333D3F393B#128) +++ 0x050701030D0F090B151711131D1F191B#128) +++ 0xFEFCFAF8F6F4F2F0EEECEAE8E6E4E2E0#128) +++ 0xDEDCDAD8D6D4D2D0CECCCAC8C6C4C2C0#128) +++ 0xBEBCBAB8B6B4B2B0AEACAAA8A6A4A2A0#128) +++ 0x9E9C9A98969492908E8C8A8886848280#128) +++ 0x7E7C7A78767472706E6C6A6866646260#128) +++ 0x5E5C5A58565452504E4C4A4846444240#128) +++ 0x3E3C3A38363432302E2C2A2826242220#128) +++ 0x1E1C1A18161412100E0C0A0806040200#128)
  (BitVec.slice FFmul_02 (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul03 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_03 : (BitVec 2048) :=
    (((((((((((((((0x1A191C1F16151013020104070E0D080B#128 +++ 0x2A292C2F26252023323134373E3D383B#128) +++ 0x7A797C7F76757073626164676E6D686B#128) +++ 0x4A494C4F46454043525154575E5D585B#128) +++ 0xDAD9DCDFD6D5D0D3C2C1C4C7CECDC8CB#128) +++ 0xEAE9ECEFE6E5E0E3F2F1F4F7FEFDF8FB#128) +++ 0xBAB9BCBFB6B5B0B3A2A1A4A7AEADA8AB#128) +++ 0x8A898C8F86858083929194979E9D989B#128) +++ 0x818287848D8E8B88999A9F9C95969390#128) +++ 0xB1B2B7B4BDBEBBB8A9AAAFACA5A6A3A0#128) +++ 0xE1E2E7E4EDEEEBE8F9FAFFFCF5F6F3F0#128) +++ 0xD1D2D7D4DDDEDBD8C9CACFCCC5C6C3C0#128) +++ 0x414247444D4E4B48595A5F5C55565350#128) +++ 0x717277747D7E7B78696A6F6C65666360#128) +++ 0x212227242D2E2B28393A3F3C35363330#128) +++ 0x111217141D1E1B18090A0F0C05060300#128)
  (BitVec.slice FFmul_03 (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul09 (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_09 : (BitVec 2048) :=
    (((((((((((((((0x464F545D626B70790E071C152A233831#128 +++ 0xD6DFC4CDF2FBE0E99E978C85BAB3A8A1#128) +++ 0x7D746F6659504B42353C272E1118030A#128) +++ 0xEDE4FFF6C9C0DBD2A5ACB7BE8188939A#128) +++ 0x3039222B141D060F78716A635C554E47#128) +++ 0xA0A9B2BB848D969FE8E1FAF3CCC5DED7#128) +++ 0x0B0219102F263D34434A5158676E757C#128) +++ 0x9B928980BFB6ADA4D3DAC1C8F7FEE5EC#128) +++ 0xAAA3B8B18E879C95E2EBF0F9C6CFD4DD#128) +++ 0x3A3328211E170C05727B6069565F444D#128) +++ 0x9198838AB5BCA7AED9D0CBC2FDF4EFE6#128) +++ 0x0108131A252C373E49405B526D647F76#128) +++ 0xDCD5CEC7F8F1EAE3949D868FB0B9A2AB#128) +++ 0x4C455E5768617A73040D161F2029323B#128) +++ 0xE7EEF5FCC3CAD1D8AFA6BDB48B829990#128) +++ 0x777E656C535A41483F362D241B120900#128)
  (BitVec.slice FFmul_09 (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul0B (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0B : (BitVec 2048) :=
    (((((((((((((((0xA3A8B5BE8F849992FBF0EDE6D7DCC1CA#128 +++ 0x1318050E3F3429224B405D56676C717A#128) +++ 0xD8D3CEC5F4FFE2E9808B969DACA7BAB1#128) +++ 0x68637E75444F5259303B262D1C170A01#128) +++ 0x555E434879726F640D061B10212A373C#128) +++ 0xE5EEF3F8C9C2DFD4BDB6ABA0919A878C#128) +++ 0x2E2538330209141F767D606B5A514C47#128) +++ 0x9E958883B2B9A4AFC6CDD0DBEAE1FCF7#128) +++ 0x545F424978736E650C071A11202B363D#128) +++ 0xE4EFF2F9C8C3DED5BCB7AAA1909B868D#128) +++ 0x2F2439320308151E777C616A5B504D46#128) +++ 0x9F948982B3B8A5AEC7CCD1DAEBE0FDF6#128) +++ 0xA2A9B4BF8E859893FAF1ECE7D6DDC0CB#128) +++ 0x1219040F3E3528234A415C57666D707B#128) +++ 0xD9D2CFC4F5FEE3E8818A979CADA6BBB0#128) +++ 0x69627F74454E5358313A272C1D160B00#128)
  (BitVec.slice FFmul_0B (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul0D (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0D : (BitVec 2048) :=
    (((((((((((((((0x979A8D80A3AEB9B4FFF2E5E8CBC6D1DC#128 +++ 0x474A5D50737E69642F2235381B16010C#128) +++ 0x2C21363B1815020F44495E53707D6A67#128) +++ 0xFCF1E6EBC8C5D2DF94998E83A0ADBAB7#128) +++ 0xFAF7E0EDCEC3D4D9929F8885A6ABBCB1#128) +++ 0x2A27303D1E130409424F5855767B6C61#128) +++ 0x414C5B5675786F622924333E1D10070A#128) +++ 0x919C8B86A5A8BFB2F9F4E3EECDC0D7DA#128) +++ 0x4D40575A7974636E25283F32111C0B06#128) +++ 0x9D90878AA9A4B3BEF5F8EFE2C1CCDBD6#128) +++ 0xF6FBECE1C2CFD8D59E938489AAA7B0BD#128) +++ 0x262B3C31121F08054E4354597A77606D#128) +++ 0x202D3A3714190E034845525F7C71666B#128) +++ 0xF0FDEAE7C4C9DED39895828FACA1B6BB#128) +++ 0x9B96818CAFA2B5B8F3FEE9E4C7CADDD0#128) +++ 0x4B46515C7F726568232E3934171A0D00#128)
  (BitVec.slice FFmul_0D (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def FFmul0E (b : (BitVec 8)) : (BitVec 8) :=
  let FFmul_0E : (BitVec 2048) :=
    (((((((((((((((0x8D83919FB5BBA9A7FDF3E1EFC5CBD9D7#128 +++ 0x6D63717F555B49471D13010F252B3937#128) +++ 0x56584A446E60727C26283A341E10020C#128) +++ 0xB6B8AAA48E80929CC6C8DAD4FEF0E2EC#128) +++ 0x202E3C321816040A505E4C426866747A#128) +++ 0xC0CEDCD2F8F6E4EAB0BEACA28886949A#128) +++ 0xFBF5E7E9C3CDDFD18B859799B3BDAFA1#128) +++ 0x1B150709232D3F316B657779535D4F41#128) +++ 0xCCC2D0DEF4FAE8E6BCB2A0AE848A9896#128) +++ 0x2C22303E141A08065C52404E646A7876#128) +++ 0x17190B052F21333D67697B755F51434D#128) +++ 0xF7F9EBE5CFC1D3DD87899B95BFB1A3AD#128) +++ 0x616F7D735957454B111F0D032927353B#128) +++ 0x818F9D93B9B7A5ABF1FFEDE3C9C7D5DB#128) +++ 0xBAB4A6A8828C9E90CAC4D6D8F2FCEEE0#128) +++ 0x5A544648626C7E702A243638121C0E00#128)
  (BitVec.slice FFmul_0E (Sail.Int.toNatChecked (((BitVec.toNat b) *i 8))) 8)


def SHAchoose (x : (BitVec 32)) (y : (BitVec 32)) (z : (BitVec 32)) : (BitVec 32) :=
  (((y ^^^ z) &&& x) ^^^ z)


def SHAparity (x : (BitVec 32)) (y : (BitVec 32)) (z : (BitVec 32)) : (BitVec 32) :=
  ((x ^^^ y) ^^^ z)


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
  ArmFull.assert (bne statuscode Fault_None) "sail-inputs/03-v8_base.sail:13375.35-13375.36"
  (pure (((BEq.beq statuscode Fault_SyncExternal) || ((BEq.beq statuscode Fault_SyncParity) || ((BEq.beq
            statuscode Fault_SyncExternalOnWalk) || (BEq.beq statuscode Fault_SyncParityOnWalk))))))


def PendSErrorInterrupt (fault : FaultRecord) : Unit :=
  ()


def IsAsyncAbort (statuscode : Fault) : SailM Bool := do
  ArmFull.assert (bne statuscode Fault_None) "sail-inputs/03-v8_base.sail:13619.35-13619.36"
  (pure (((BEq.beq statuscode Fault_AsyncExternal) || (BEq.beq statuscode Fault_AsyncParity))))


def IsExternalAbort (statuscode : Fault) : SailM Bool := do
  ArmFull.assert (bne statuscode Fault_None) "sail-inputs/03-v8_base.sail:13632.35-13632.36"
  (pure (((BEq.beq statuscode Fault_SyncExternal) || ((BEq.beq statuscode Fault_SyncParity) || ((BEq.beq
            statuscode Fault_SyncExternalOnWalk) || ((BEq.beq statuscode Fault_SyncParityOnWalk) || ((BEq.beq
                statuscode Fault_AsyncExternal) || (BEq.beq statuscode Fault_AsyncParity))))))))


def IsSecondStage (fault : FaultRecord) : SailM Bool := do
  ArmFull.assert (bne fault.statuscode Fault_None) "sail-inputs/03-v8_base.sail:13643.41-13643.42"
  (pure (fault.secondstage))


def IPAValid (fault : FaultRecord) : SailM Bool := do
  ArmFull.assert (bne fault.statuscode Fault_None) "sail-inputs/03-v8_base.sail:13688.41-13688.42"
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


end ArmFull.Functions
