import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0045
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0100
import ArmFull.Fn.M0113
import ArmFull.Fn.M0114
import ArmFull.Fn.M0115
import ArmFull.Fn.M0116

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

def EL3SDDUndef (_ : Unit) : SailM Bool := do
  if ((← do
       (Halted ())) : Bool)
  then
    (do
      let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (pure ((((_get_EDSCR_Type_SDD w__1) == 1#1) : Bool))))
  else (pure false)


def HaveFeatHCX (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_HCX)


def HaveMTE4Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MTE4)


def MPAM1_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _MPAM1_EL1 ) : SailM MPAM1_EL1_Type )
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      let r := ((BitVec.update r 63 (Bit (BitVec.slice w__0 63 1))) : (BitVec 64))
      (pure (r)))
  else
    (do
      let w__1 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      let r := ((BitVec.update r 63 (Bit (BitVec.slice w__1 63 1))) : (BitVec 64))
      (pure (r)))


def DefaultMPAMinfo (partidspace : PARTIDspaceType) : SailM MPAMinfo := do
  let DefaultInfo ← (( do (undefined_MPAMinfo (← occLabel 746) ()) ) : SailM MPAMinfo )
  let DefaultInfo : MPAMinfo := { DefaultInfo with mpam_sp := partidspace }
  let DefaultInfo : MPAMinfo := { DefaultInfo with partid := DefaultPARTID }
  let DefaultInfo : MPAMinfo := { DefaultInfo with pmg := DefaultPMG }
  (pure (DefaultInfo))


def HaveMPAMv0p1Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MPAMv0p1)


def HaveMPAMv1p1Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MPAMv1p1)


/-- Type quantifiers: vpartid : Int -/
def mapvpmw (vpartid : Int) : SailM (BitVec 16) := do
  let vpmw ← (( do (undefined_bitvector_at (← occLabel 758) 64) ) : SailM (BitVec 64) )
  let wd : Int := (fdiv_int vpartid 4)
  let vpmw ← (( do
    match wd with
    | 0 =>
      (do
        readReg MPAMVPM0_EL2)
    | 1 =>
      (do
        readReg MPAMVPM1_EL2)
    | 2 =>
      (do
        readReg MPAMVPM2_EL2)
    | 3 =>
      (do
        readReg MPAMVPM3_EL2)
    | 4 =>
      (do
        readReg MPAMVPM4_EL2)
    | 5 =>
      (do
        readReg MPAMVPM5_EL2)
    | 6 =>
      (do
        readReg MPAMVPM6_EL2)
    | 7 =>
      (do
        readReg MPAMVPM7_EL2)
    | _ =>
      (let vpmw : (BitVec 64) := (Zeros (n := 64))
      (pure (vpmw))) ) : SailM (BitVec 64) )
  let vpmw := vpmw
  let vpme_lsb : Int := ((fmod_int vpartid 4) *i 16)
  (pure ((BitVec.slice vpmw (Sail.Int.toNatChecked (vpme_lsb)) 16)))


def HaveCRCExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_CRC32)


def HaveAESExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_AES)


def HaveBit128PMULLExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_PMULL)


def HaveSHA1Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SHA1)


def HaveSHA256Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SHA256)


def HaveSHA512Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SHA512)


def HaveSHA3Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SHA3)


def HaveSM3Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SM3)


def HaveSM4Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SM4)


/-- Type quantifiers: k_part1 : Bool -/
def SHA256hash (x_in : (BitVec 128)) (y_in : (BitVec 128)) (w : (BitVec 128)) (part1 : Bool) : SailM (BitVec 128) := do
  let chs ← (( do (undefined_bitvector_at (← occLabel 790) 32) ) : SailM (BitVec 32) )
  let maj ← (( do (undefined_bitvector_at (← occLabel 791) 32) ) : SailM (BitVec 32) )
  let t ← (( do (undefined_bitvector_at (← occLabel 792) 32) ) : SailM (BitVec 32) )
  let x : (BitVec 128) := x_in
  let y : (BitVec 128) := y_in
  let (chs, maj, t, x, y) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Nat := 3
    (do
      let mut loop_vars := (chs, maj, t, x, y)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (chs, maj, t, x, y) := loop_vars
        loop_vars ← do
          let chs : (BitVec 32) :=
            (SHAchoose (Sail.BitVec.extractLsb y 31 0) (Sail.BitVec.extractLsb y 63 32)
              (Sail.BitVec.extractLsb y 95 64))
          let maj : (BitVec 32) :=
            (SHAmajority (Sail.BitVec.extractLsb x 31 0) (Sail.BitVec.extractLsb x 63 32)
              (Sail.BitVec.extractLsb x 95 64))
          let w__0 ← (( do (Elem_read w e 32) ) : SailM (BitVec 32) )
          let t :=
            (((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) ((Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb
                    y 127 96)) + (SHAhashSIGMA1 (Sail.BitVec.extractLsb y 31 0)))) + chs)) + w__0) : (BitVec 32))
          let x : (BitVec 128) :=
            (Sail.BitVec.updateSubrange x 127 96
              (t + (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.extractLsb x 127 96))))
          let y : (BitVec 128) :=
            (Sail.BitVec.updateSubrange y 127 96
              ((t + (SHAhashSIGMA0 (Sail.BitVec.extractLsb x 31 0))) + maj))
          let split_vec ← (( do (ROL (y +++ x) 32) ) : SailM (BitVec (128 + 128)) )
          let y : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 255 128)
          let x : (BitVec 128) := (Sail.BitVec.extractLsb split_vec 127 0)
          (pure ((chs, maj, t, x, y)))
      (pure loop_vars)) ) : SailM
    ((BitVec 32) × (BitVec 32) × (BitVec 32) × (BitVec 128) × (BitVec 128)) )
  (pure (if (part1 : Bool)
    then x
    else y))


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def UnsignedRecipEstimate (operand : (BitVec k_N)) : SailM (BitVec k_N) := do
  let estimate ← (( do (undefined_int_at (← occLabel 812) ()) ) : SailM Int )
  let increasedprecision_name ← (( do (undefined_bool_at (← occLabel 813) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length operand) == 32) "sail-arm/v8_base.sail:13084.19-13084.20"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 814)
      (Sail.BitVec.length operand))) ) : SailM (BitVec k_N) )
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access operand
           (Sail.Int.toNatChecked (((Sail.BitVec.length result) -i 1))))])) == 0#1) : Bool)
  then
    (let result : (BitVec k_N) := (Sail.BitVec.castWidth (Ones (n := (Sail.BitVec.length result))))
    (pure (result)))
  else
    (do
      let increasedprecision_name : Bool := false
      let estimate ← (( do
        (RecipEstimate (BitVec.toNat (Sail.BitVec.extractLsb operand 31 23)) increasedprecision_name)
        ) : SailM Int )
      let result : (BitVec k_N) :=
        (Sail.BitVec.castWidth ((integer_subrange estimate 8 0) +++ (Zeros
            (n := (Sail.Int.toNatChecked (((Sail.BitVec.length result) -i 9)))))))
      (pure (result)))


/-- Type quantifiers: a_in : Int, k_increasedprecision_name : Bool -/
def RecipSqrtEstimate (a_in : Int) (increasedprecision_name : Bool) : SailM Int := do
  let round_up ← (( do (undefined_bool_at (← occLabel 815) ()) ) : SailM Bool )
  let a : Int := a_in
  let r ← (( do (undefined_int_at (← occLabel 816) ()) ) : SailM Int )
  let r ← (( do
    if ((! increasedprecision_name) : Bool)
    then
      (do
        ArmFull.assert ((128 ≤b a) && (a <b 512)) "sail-arm/v8_base.sail:13104.33-13104.34"
        let a : Int :=
          if ((a <b 256) : Bool)
          then ((a *i 2) +i 1)
          else
            (let a : Int := (Int.shiftl (Int.shiftr a 1) 1)
            ((a +i 1) *i 2))
        let a : Int := a
        let b : Int := 512
        let b ← (( do
          let loop_vars ← sailWhileFuelM (α := Int) (fuel := 1048576) (fun b => (pure (((a *i (b +i 1)) *i (b +i 1)) <b (2 ^i 28)))) b
            fun b => do (pure ((b +i 1) : Int))
          (pure loop_vars) ) : SailM Int )
        let b : Int := b
        let r : Int := (fdiv_int (b +i 1) 2)
        ArmFull.assert ((256 ≤b r) && (r <b 512)) "sail-arm/v8_base.sail:13118.33-13118.34"
        (pure (r)))
    else
      (do
        ArmFull.assert ((1024 ≤b a) && (a <b 4096)) "sail-arm/v8_base.sail:13120.35-13120.36"
        let real_val ← (( do (undefined_real_at (← occLabel 817) ()) ) : SailM real )
        let real_val : real :=
          if ((a <b 2048) : Bool)
          then
            (let a : Int := ((a *i 2) +i 1)
            (div_real (to_real a) (2)))
          else
            (let a : Int := (Int.shiftl (Int.shiftr a 1) 1)
            let a : Int := (a +i 1)
            (to_real a))
        let w__0 ← (( do (sqrt_real real_val) ) : SailM real )
        let real_val : real := (w__0 : real)
        let real_val : real := (mult_real real_val (to_real (2 ^i 47)))
        let int_val : Int := (round_down real_val)
        let error : real := (sub_real real_val (to_real int_val))
        let round_up : Bool := (gt_real error (1/2))
        let int_val : Int :=
          if (round_up : Bool)
          then (int_val +i 1)
          else int_val
        let real_val : real := (div_real (to_real (2 ^i 65)) (to_real int_val))
        let int_val : Int := (round_down real_val)
        let error : real := (sub_real real_val (to_real int_val))
        let round_up : Bool :=
          ((gt_real error (1/2)) || ((eq_real error (1/2)) && ((BitVec.setWidth 1 (BitVec.join1 [(integer_access
                    int_val 0)])) == 1#1)))
        let int_val : Int :=
          if (round_up : Bool)
          then (int_val +i 1)
          else int_val
        let int_val : Int := int_val
        let r : Int := int_val
        ArmFull.assert ((4096 ≤b r) && (r <b 8192)) "sail-arm/v8_base.sail:13147.35-13147.36"
        (pure (r))) ) : SailM Int )
  let r : Int := r
  (pure (r))


/-- Type quantifiers: N : Nat, i : Int, k_is_unsigned : Bool, N ≥ 0 -/
def SatQ (i : Int) (N : Nat) (is_unsigned : Bool) : SailM ((BitVec N) × Bool) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 825)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  let sat ← (( do (undefined_bool_at (← occLabel 826) ()) ) : SailM Bool )
  let w__2 ← (( do
    if (is_unsigned : Bool)
    then
      (do
        ArmFull.assert (0 ≤b (N -i 1)) "sail-arm/v8_base.sail:13218.38-13218.39"
        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (UnsignedSatQ i N)))
    else
      (do
        ArmFull.assert (0 ≤b (N -i 1)) "sail-arm/v8_base.sail:13221.38-13221.39"
        ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), x1)) <$> (SignedSatQ i N))) ) : SailM
    ((BitVec N) × Bool) )
  let (tup__0, tup__1) := (w__2 : ((BitVec N) × Bool))
  let result : (BitVec N) := tup__0
  let sat : Bool := tup__1
  (pure ((result, sat)))


def HaveRASExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_RAS)


def AArch32_PEErrorState (fault : FaultRecord) : SailM ErrorState := do
  let w__6 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do (ErrorIsContained ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  let w__1 ← (( do (ErrorIsSynchronized ()) ) : SailM Bool )
                  (pure (((! w__1) : Bool)))) : Bool)
             then
               (do
                 let w__2 ← (( do (StateIsRecoverable ()) ) : SailM Bool )
                 (pure (((! w__2) : Bool))))
             else (pure false))) : Bool)
    then (pure true)
    else
      (do
        (ReportErrorAsUC ())) ) : SailM Bool )
  if (w__6 : Bool)
  then (pure (ErrorState_UC))
  else
    (do
      let w__9 ← (( do
        if ((← do
             let w__7 ← (( do (StateIsRecoverable ()) ) : SailM Bool )
             (pure (((! w__7) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            (ReportErrorAsUEU ())) ) : SailM Bool )
      if (w__9 : Bool)
      then (pure (ErrorState_UEU))
      else
        (do
          let w__12 ← (( do
            if ((← do
                 (ActionRequired ())) : Bool)
            then (pure true)
            else
              (do
                (ReportErrorAsUER ())) ) : SailM Bool )
          let w__13 : ErrorState :=
            if (w__12 : Bool)
            then ErrorState_UER
            else ErrorState_UEO
          (pure (w__13))))


def Have52BitIPAAndPASpaceExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LPA2)


def Have56BitPAExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_D128)


def HaveMTE2Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MTE2)


def AArch32_ReportHypEntry (except : ExceptionRecord) : SailM Unit := do
  let ec ← (( do (undefined_int_at (← occLabel 846) ()) ) : SailM Int )
  let il ← (( do (undefined_bitvector_at (← occLabel 847) 1) ) : SailM (BitVec 1) )
  let exceptype : Exception := except.exceptype
  let w__0 ← (( do (AArch32_ExceptionClass exceptype) ) : SailM (Int × (BitVec 1)) )
  let (tup__0, tup__1) := (w__0 : (Int × (BitVec 1)))
  let ec : Int := tup__0
  let il : (BitVec 1) := tup__1
  let ec : Int := ec
  let iss : (BitVec 25) := except.syndrome
  let iss2 : (BitVec 24) := except.syndrome2
  let il : (BitVec 1) :=
    if ((((ec == (BitVec.toNat 0x24#8)) || ((ec == (BitVec.toNat 0x25#8)) : Bool)) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               iss 24)])) == 0#1)) : Bool)
    then 1#1
    else il
  let il := il
  (HSR_write (Mk_HSR_Type (((integer_subrange ec 5 0) +++ il) +++ iss)))
  if (((BEq.beq exceptype Exception_InstructionAbort) || (BEq.beq exceptype Exception_PCAlignment)) : Bool)
  then
    (do
      (HIFAR_write (Sail.BitVec.extractLsb except.vaddress 31 0))
      let w__1 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (HDFAR_write w__1))
  else
    (do
      if ((BEq.beq exceptype Exception_DataAbort) : Bool)
      then
        (do
          let w__2 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
          (HIFAR_write w__2)
          (HDFAR_write (Sail.BitVec.extractLsb except.vaddress 31 0)))
      else (pure (())))
  if (except.ipavalid : Bool)
  then
    (do
      let w__3 ← (( do (HPFAR_read ()) ) : SailM (BitVec 32) )
      (HPFAR_write
        (Mk_HPFAR_Type
          (Sail.BitVec.updateSubrange w__3 31 4 (Sail.BitVec.extractLsb except.ipaddress 39 12)))))
  else
    (do
      let w__4 ← (( do (HPFAR_read ()) ) : SailM (BitVec 32) )
      let w__5 ← (( do (__UNKNOWN_bits 28) ) : SailM (BitVec 28) )
      (HPFAR_write (Mk_HPFAR_Type (Sail.BitVec.updateSubrange w__4 31 4 w__5))))


def DBGDSCRext_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDSCRext ) : SailM DBGDSCRext_Type )
  let w__0 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  let w__1 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  let r := ((BitVec.update r 15 (Bit (BitVec.slice w__1 15 1))) : (BitVec 32))
  let w__2 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  let r := ((BitVec.update r 12 (Bit (BitVec.slice w__2 12 1))) : (BitVec 32))
  let w__3 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  let r := ((Sail.BitVec.updateSubrange r 5 2 (BitVec.slice w__3 2 4)) : (BitVec 32))
  (pure (r))


def DBGDSCRext_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDSCRext_Type := value_name
  let w__0 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  let w__1 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRint_write (Mk_DBGDSCRint_Type (set_slice 1 w__1 15 (BitVec.slice r 15 1))))
  let w__2 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRint_write (Mk_DBGDSCRint_Type (set_slice 1 w__2 12 (BitVec.slice r 12 1))))
  let w__3 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRint_write (Mk_DBGDSCRint_Type (set_slice 4 w__3 2 (BitVec.slice r 2 4))))
  writeReg _DBGDSCRext r


def HaveFeatLS64 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LS64)


def GetLoadStoreType (_ : Unit) : SailM (BitVec 2) := do
  (__UNKNOWN_bits 2)


def HaveDoubleFault2Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_DoubleFault2)


def HaveFeatSCTLR2 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SCTLR2)


def EncodeGPCSC (gpcf : GPCFRecord) : SailM (BitVec 6) := do
  ArmFull.assert ((gpcf.level == 0) || (gpcf.level == 1)) "sail-arm/v8_base.sail:15103.44-15103.45"
  match gpcf.gpf with
  | .GPCF_AddressSize =>
    (pure ((0b00000#5 +++ (BitVec.setWidth 1 (BitVec.join1 [(integer_access gpcf.level 0)])))))
  | .GPCF_Walk =>
    (pure ((0b00010#5 +++ (BitVec.setWidth 1 (BitVec.join1 [(integer_access gpcf.level 0)])))))
  | .GPCF_Fail =>
    (pure ((0b00110#5 +++ (BitVec.setWidth 1 (BitVec.join1 [(integer_access gpcf.level 0)])))))
  | .GPCF_EABT =>
    (pure ((0b01010#5 +++ (BitVec.setWidth 1 (BitVec.join1 [(integer_access gpcf.level 0)])))))
  | _ =>
    (do
      (undefined_bitvector_at (← occLabel 880) 6))


def HaveAccessFlagUpdateExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_HAFDBS)


def HaveAtomicExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LSE)


def HaveDirtyBitModifierExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_HAFDBS)


def GPCNoFault (_ : Unit) : SailM GPCFRecord := do
  let result ← (( do (undefined_GPCFRecord (← occLabel 883) ()) ) : SailM GPCFRecord )
  let result : GPCFRecord := { result with gpf := GPCF_None }
  (pure (result))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPInfinity (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:15378.38-15378.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let exp : (BitVec (Sail.Int.toNatChecked E)) := (Sail.BitVec.castWidth (Ones (n := E)))
  let frac : (BitVec (Sail.Int.toNatChecked (F : Int))) :=
    (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (F)))))
  (pure ((Sail.BitVec.castWidth ((sign +++ exp) +++ frac))))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPMaxNormal (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:15389.38-15389.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let exp : (BitVec (Sail.Int.toNatChecked E)) :=
    (Sail.BitVec.castWidth ((Ones (n := (Sail.Int.toNatChecked ((E -i 1))))) +++ 0#1))
  let frac : (BitVec (Sail.Int.toNatChecked (F : Int))) :=
    (Sail.BitVec.castWidth (Ones (n := (Sail.Int.toNatChecked (F)))))
  (pure ((Sail.BitVec.castWidth ((sign +++ exp) +++ frac))))


def HaveSMEFullA64 (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_SME_FA64)


def GetAccumulatedFPExceptions (_ : Unit) : SailM (BitVec 8) := do
  (__UNKNOWN_bits 8)


def HaveAltFP (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_AFP)


def FPRoundingMode (fpcr : (BitVec 64)) : SailM FPRounding := do
  (FPDecodeRounding (_get_FPCRType_RMode fpcr))


/-- Type quantifiers: M : Nat, k_N : Nat, List.elem k_N [16, 32, 64] ∧ List.elem M [16, 32, 64] -/
def FPConvertNaN (op : (BitVec k_N)) (M : Nat) : SailM (BitVec M) := do
  ArmFull.assert (((Sail.BitVec.length op) == 16) || (((Sail.BitVec.length op) == 32) || ((Sail.BitVec.length
          op) == 64))) "sail-arm/v8_base.sail:16429.41-16429.42"
  ArmFull.assert ((M == 16) || ((M == 32) || (M == 64))) "sail-arm/v8_base.sail:16430.38-16430.39"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 963)
      (Sail.Int.toNatChecked (M)))) ) : SailM (BitVec M) )
  let frac ← (( do (undefined_bitvector_at (← occLabel 964) 51) ) : SailM (BitVec 51) )
  let sign : (BitVec 1) :=
    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op
        (Sail.Int.toNatChecked (((Sail.BitVec.length op) -i 1))))]))
  let frac : (BitVec 51) :=
    match (Sail.BitVec.length op) with
    | 64 => (Sail.BitVec.extractLsb op 50 0)
    | 32 => ((Sail.BitVec.extractLsb op 21 0) +++ (Zeros (n := 29)))
    | 16 => ((Sail.BitVec.extractLsb op 8 0) +++ (Zeros (n := 42)))
    | _ => frac
  let result : (BitVec M) :=
    match M with
    | 64 =>
      (Sail.BitVec.castWidth ((sign +++ (Ones (n := (Sail.Int.toNatChecked ((M -i 52)))))) +++ frac))
    | 32 =>
      (Sail.BitVec.castWidth ((sign +++ (Ones (n := (Sail.Int.toNatChecked ((M -i 23)))))) +++ (Sail.BitVec.extractLsb
          frac 50 29)))
    | 16 =>
      (Sail.BitVec.castWidth ((sign +++ (Ones (n := (Sail.Int.toNatChecked ((M -i 10)))))) +++ (Sail.BitVec.extractLsb
          frac 50 42)))
    | _ => result
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPOnePointFive (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:17244.38-17244.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let exp : (BitVec (1 + ((Sail.Int.toNatChecked E) - 1))) :=
    (Sail.BitVec.castWidth (0#1 +++ (Ones (n := (Sail.Int.toNatChecked ((E -i 1)))))))
  let frac : (BitVec (Sail.Int.toNatChecked ((1 : Int) +i ((F : Int) -i (1 : Int))))) :=
    (Sail.BitVec.castWidth (1#1 +++ (Zeros (n := (Sail.Int.toNatChecked ((F -i 1)))))))
  let result : (BitVec (Sail.Int.toNatChecked (((1 : Int) +i ((1 : Int) +i ((E : Int) -i (1 : Int)))) +i ((1 : Int) +i ((F : Int) -i (1 : Int)))))) :=
    (Sail.BitVec.castWidth ((sign +++ exp) +++ frac))
  (pure ((Sail.BitVec.castWidth result)))


def HaveFeatRPRES (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_RPRES)


def HaveCNTSCExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_CNTSC)


def HaveMPAMExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_MPAM)


def Have16bitVMID (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_VMID16)


def AArch64_HaveHPDExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_HPDS)


def HaveQRDMLAHExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_RDM)


def HaveCommonNotPrivateTransExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_TTCNP)


def HaveExtendedExecuteNeverExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_XNX)


def AArch32_HaveHPDExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_AA32HPD)


def Have52BitVAExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LVA)


def Have52BitPAExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LPA)


def HaveV82Debug (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_Debugv8p2)


def HaveTrapLoadStoreMultipleDeviceExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LSMAOC)


def HaveFJCVTZSExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_JSCVT)


def HaveFCADDExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FCMA)


def HaveDOTPExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_DotProd)


def HaveSmallTranslationTableExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_TTST)


def HaveLSE2Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_LSE2)


def HaveFP16MulNoRoundingToFP32Ext (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FHM)


def HaveFlagManipulateExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FlagM)


def HaveFlagFormatExt (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_FlagM2)


def HaveSelfHostedTrace (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_TRF)


def HaveBlockBBM (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_BBM)


def Havev8p4Debug (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_Debugv8p4)


def HaveStage2MemAttrControl (_ : Unit) : SailM Bool := do
  (IsFeatureImplemented FEAT_S2FWB)


end ArmFull.Functions
