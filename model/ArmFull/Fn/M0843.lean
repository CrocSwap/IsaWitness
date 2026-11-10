import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0034
import ArmFull.Fn.M0049
import ArmFull.Fn.M0100
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0181
import ArmFull.Fn.M0186
import ArmFull.Fn.M0215
import ArmFull.Fn.M0217
import ArmFull.Fn.M0218
import ArmFull.Fn.M0227
import ArmFull.Fn.M0244
import ArmFull.Fn.M0254
import ArmFull.Fn.M0580
import ArmFull.Fn.M0581
import ArmFull.Fn.M0582
import ArmFull.Fn.M0840

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

def decode_msr_imm_aarch64_instrs_system_register_cpsr (op2 : (BitVec 3)) (CRm : (BitVec 4)) (op1 : (BitVec 3)) : SailM Unit := do
  if (((op1 == 0b000#3) && (op2 == 0b000#3)) : Bool)
  then sailThrow ((Error_See "CFINV"))
  else (pure (()))
  if (((op1 == 0b000#3) && (op2 == 0b001#3)) : Bool)
  then sailThrow ((Error_See "XAFLAG"))
  else (pure (()))
  if (((op1 == 0b000#3) && (op2 == 0b010#3)) : Bool)
  then sailThrow ((Error_See "AXFLAG"))
  else (pure (()))
  (AArch64_CheckSystemAccess 0b00#2 op1 0b0100#4 CRm op2 0b11111#5 0#1)
  let min_EL ← (( do (undefined_bitvector_at (← occLabel 4662) 2) ) : SailM (BitVec 2) )
  let need_secure : Bool := false
  let b__0 := op1
  let (min_EL, need_secure) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (let min_EL : (BitVec 2) := EL1
      (pure ((min_EL, need_secure))))
    else
      (do
        match b__0 with
        | 0b010 =>
          (let min_EL : (BitVec 2) := EL1
          (pure ((min_EL, need_secure))))
        | 0b011 =>
          (let min_EL : (BitVec 2) := EL0
          (pure ((min_EL, need_secure))))
        | 0b100 =>
          (let min_EL : (BitVec 2) := EL2
          (pure ((min_EL, need_secure))))
        | 0b101 =>
          (do
            let w__0 ← (( do (HaveVirtHostExt ()) ) : SailM Bool )
            if ((! w__0) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let min_EL : (BitVec 2) := EL2
            (pure ((min_EL, need_secure))))
        | 0b110 =>
          (let min_EL : (BitVec 2) := EL3
          (pure ((min_EL, need_secure))))
        | _ =>
          (let min_EL : (BitVec 2) := EL1
          let need_secure : Bool := true
          (pure ((min_EL, need_secure))))) ) : SailM ((BitVec 2) × Bool) )
  let min_EL := min_EL
  let w__4 ← (( do
    if ((← do
         let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure ((((BitVec.toNat w__1.EL) <b (BitVec.toNat min_EL)) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((need_secure : Bool) : Bool)
        then
          (do
            let w__2 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
            (pure (((bne w__2 SS_Secure) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let operand : (BitVec 4) := CRm
  let field ← (( do (undefined_PSTATEField (← occLabel 4663) ()) ) : SailM PSTATEField )
  let field ← (( do
    match (BitVec.setWidth 6 (op1 +++ op2)) with
    | 0b000011 =>
      (do
        let w__5 ← (( do (HaveUAOExt ()) ) : SailM Bool )
        if ((! w__5) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_UAO)))
    | 0b000100 =>
      (do
        let w__6 ← (( do (HavePANExt ()) ) : SailM Bool )
        if ((! w__6) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_PAN)))
    | 0b000101 => (pure (PSTATEField_SP))
    | 0b001000 =>
      (do
        let b__1 := CRm
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
        then
          (do
            let w__7 ← (( do (HaveFeatNMI ()) ) : SailM Bool )
            if ((! w__7) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure (PSTATEField_ALLINT)))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
            then
              (do
                let w__8 ← (( do (HaveFeatEBEP ()) ) : SailM Bool )
                if ((! w__8) : Bool)
                then sailThrow ((Error_Undefined ()))
                else (pure (()))
                (pure (PSTATEField_PM)))
            else sailThrow ((Error_Undefined ()))))
    | 0b011010 =>
      (do
        let w__9 ← (( do (HaveDITExt ()) ) : SailM Bool )
        if ((! w__9) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_DIT)))
    | 0b011011 =>
      (do
        let b__3 := CRm
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
        then
          (do
            let w__10 ← (( do (HaveSME ()) ) : SailM Bool )
            if ((! w__10) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure (PSTATEField_SVCRSM)))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
            then
              (do
                let w__11 ← (( do (HaveSME ()) ) : SailM Bool )
                if ((! w__11) : Bool)
                then sailThrow ((Error_Undefined ()))
                else (pure (()))
                (pure (PSTATEField_SVCRZA)))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
                then
                  (do
                    let w__12 ← (( do (HaveSME ()) ) : SailM Bool )
                    if ((! w__12) : Bool)
                    then sailThrow ((Error_Undefined ()))
                    else (pure (()))
                    (pure (PSTATEField_SVCRSMZA)))
                else sailThrow ((Error_Undefined ())))))
    | 0b011100 =>
      (do
        let w__13 ← (( do (HaveMTEExt ()) ) : SailM Bool )
        if ((! w__13) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_TCO)))
    | 0b011110 => (pure (PSTATEField_DAIFSet))
    | 0b011111 => (pure (PSTATEField_DAIFClr))
    | 0b011001 =>
      (do
        let w__14 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
        if ((! w__14) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_SSBS)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM PSTATEField )
  let w__16 ← (( do
    (pure ((← do
          let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__15.EL == EL0) : Bool)))) && (((BEq.beq field PSTATEField_DAIFSet) || (BEq.beq
            field PSTATEField_DAIFClr)) : Bool))) ) : SailM Bool )
  if (w__16 : Bool)
  then
    (do
      let w__19 ← (( do
        if ((← do
             (IsInHost ())) : Bool)
        then (pure true)
        else
          (do
            let w__18 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            (pure ((((_get_SCTLR_EL1_Type_UMA w__18) == 0#1) : Bool)))) ) : SailM Bool )
      if (w__19 : Bool)
      then
        (do
          let w__22 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__21) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__22 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_system_register_cpsr field operand)


def decode_pacda_aarch64_instrs_integer_pac_pacda_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (let source_is_sp : Bool :=
        if ((n == 31) : Bool)
        then true
        else source_is_sp
      (pure (source_is_sp)))
    else
      (do
        if ((n != 31) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (source_is_sp))) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_pacda_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_pacdb_aarch64_instrs_integer_pac_pacdb_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (let source_is_sp : Bool :=
        if ((n == 31) : Bool)
        then true
        else source_is_sp
      (pure (source_is_sp)))
    else
      (do
        if ((n != 31) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (source_is_sp))) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_pacdb_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_pacga_aarch64_instrs_integer_pac_pacga_dp_2src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp : Bool :=
    if ((m == 31) : Bool)
    then true
    else source_is_sp
  (execute_aarch64_instrs_integer_pac_pacga_dp_2src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_pacia_aarch64_instrs_integer_pac_pacia_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (let source_is_sp : Bool :=
        if ((n == 31) : Bool)
        then true
        else source_is_sp
      (pure (source_is_sp)))
    else
      (do
        if ((n != 31) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (source_is_sp))) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_pacia_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_pacia_aarch64_instrs_integer_pac_pacia_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Int := 17
  let n : Int := 0
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0011000 =>
      (let d : Int := 30
      let n : Int := 31
      (pure ((d, n, source_is_sp))))
    | 0b0011001 =>
      (do
        let d : Int := 30
        let source_is_sp : Bool := true
        let w__0 ← (( do (HaveBTIExt ()) ) : SailM Bool )
        if (w__0 : Bool)
        then
          (do
            let w__1 ← (( do (BTypeCompatible_PACIXSP ()) ) : SailM Bool )
            (SetBTypeCompatible w__1))
        else (pure (()))
        (pure ((d, n, source_is_sp))))
    | 0b0001000 =>
      (let d : Int := 17
      let n : Int := 16
      (pure ((d, n, source_is_sp))))
    | 0b0001010 => sailThrow ((Error_See "PACIB"))
    | 0b0001100 => sailThrow ((Error_See "AUTIA"))
    | 0b0001110 => sailThrow ((Error_See "AUTIB"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001101#6 : (BitVec 6))) : Bool)
        then sailThrow ((Error_See "PACIB"))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001110#6 : (BitVec 6))) : Bool)
            then sailThrow ((Error_See "AUTIA"))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001111#6 : (BitVec 6))) : Bool)
                then sailThrow ((Error_See "AUTIB"))
                else
                  (do
                    match b__0 with
                    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
                    | _ => sailThrow ((Error_See "HINT")))))
        (pure ((d, n, source_is_sp)))) ) : SailM (Int × Int × Bool) )
  let n : Int := n
  let d : Int := d
  ArmFull.assert ((0 ≤b n) && (n ≤b 31)) "/home/doug/boss-scratch/armcert-defects/c27-accepted/armcert_c27.sail:247.43-247.44"
  (execute_aarch64_instrs_integer_pac_pacia_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_pacib_aarch64_instrs_integer_pac_pacib_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Z : (BitVec 1)) : SailM Unit := do
  let source_is_sp : Bool := false
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let source_is_sp ← (( do
    if ((Z == 0#1) : Bool)
    then
      (let source_is_sp : Bool :=
        if ((n == 31) : Bool)
        then true
        else source_is_sp
      (pure (source_is_sp)))
    else
      (do
        if ((n != 31) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (source_is_sp))) ) : SailM Bool )
  (execute_aarch64_instrs_integer_pac_pacib_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


def decode_pacib_aarch64_instrs_integer_pac_pacib_hint (op2 : (BitVec 3)) (CRm : (BitVec 4)) : SailM Unit := do
  let d : Int := 17
  let n : Int := 0
  let source_is_sp : Bool := false
  let (d, n, source_is_sp) ← (( do
    match (BitVec.setWidth 7 (CRm +++ op2)) with
    | 0b0011010 =>
      (let d : Int := 30
      let n : Int := 31
      (pure ((d, n, source_is_sp))))
    | 0b0011011 =>
      (do
        let d : Int := 30
        let source_is_sp : Bool := true
        let w__0 ← (( do (HaveBTIExt ()) ) : SailM Bool )
        if (w__0 : Bool)
        then
          (do
            let w__1 ← (( do (BTypeCompatible_PACIXSP ()) ) : SailM Bool )
            (SetBTypeCompatible w__1))
        else (pure (()))
        (pure ((d, n, source_is_sp))))
    | 0b0001010 =>
      (let d : Int := 17
      let n : Int := 16
      (pure ((d, n, source_is_sp))))
    | 0b0001000 => sailThrow ((Error_See "PACIA"))
    | 0b0001100 => sailThrow ((Error_See "AUTIA"))
    | 0b0001110 => sailThrow ((Error_See "AUTIB"))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001100#6 : (BitVec 6))) : Bool)
        then sailThrow ((Error_See "PACIA"))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001110#6 : (BitVec 6))) : Bool)
            then sailThrow ((Error_See "AUTIA"))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb b__0 6 1)) == (0b001111#6 : (BitVec 6))) : Bool)
                then sailThrow ((Error_See "AUTIB"))
                else
                  (do
                    match b__0 with
                    | 0b0000111 => sailThrow ((Error_See "XPACLRI"))
                    | _ => sailThrow ((Error_See "HINT")))))
        (pure ((d, n, source_is_sp)))) ) : SailM (Int × Int × Bool) )
  let n : Int := n
  let d : Int := d
  ArmFull.assert ((0 ≤b n) && (n ≤b 31)) "/home/doug/boss-scratch/armcert-defects/c27-accepted/armcert_c27.sail:302.43-302.44"
  (execute_aarch64_instrs_integer_pac_pacib_dp_1src (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (n)) source_is_sp)


/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_system_sysinstwithreg_wfet (d : Nat) : SailM Unit := do
  let w__0 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let localtimeout : Int := (BitVec.toNat w__0)
  let w__3 ← (( do
    if ((← do
         (Halted ())) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_WFxTDEBUG))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  (Hint_WFE localtimeout WFxType_WFET)


/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_system_sysinstwithreg_wfit (d : Nat) : SailM Unit := do
  let w__0 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let localtimeout : Int := (BitVec.toNat w__0)
  let w__3 ← (( do
    if ((← do
         (Halted ())) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_WFxTDEBUG))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  (Hint_WFI localtimeout WFxType_WFIT)


/-- Type quantifiers: SVL : Nat, dim_dim_esize : Nat, esize : Nat, esize = 64 ∧
  (is_VL SVL) ∧ dim_dim_esize = (SVL / esize * (SVL / esize * esize)) -/
def execute_ZERO_ZA_I__ (SVL : Nat) (dim_dim_esize : Nat) (esize : Nat) (mask : (BitVec 8)) : SailM Unit := do
  (CheckSMEAndZAEnabled ())
  let SVL : Nat := SVL
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv SVL esize)))
  let result : (BitVec dim_dim_esize) := (Sail.BitVec.castWidth (Zeros (n := dim_dim_esize)))
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
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 7
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
        then
          (do
            (ZAtile_set SVL i esize dim_dim_esize (Sail.BitVec.castWidth result)))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg
  = 2 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7466)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
                let res : Int := (Max.max element1 element2)
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))) ) : SailM
                  (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg
  = 2 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7467)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
                let res : Int := (Max.max element1 element2)
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))) ) : SailM
                  (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


end ArmFull.Functions
