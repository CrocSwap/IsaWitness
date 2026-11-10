import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0020
import ArmFull.Fn.M0022
import ArmFull.Fn.M0024
import ArmFull.Fn.M0038
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0154
import ArmFull.Fn.M0156
import ArmFull.Fn.M0166
import ArmFull.Fn.M0168

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

def AArch64_HaveS1TG (tgx : TGx) : SailM Bool := do
  match tgx with
  | .TGx_4KB =>
    (do
      (__IMPDEF_boolean "Has 4K Translation Granule"))
  | .TGx_16KB =>
    (do
      (__IMPDEF_boolean "Has 16K Translation Granule"))
  | .TGx_64KB =>
    (do
      (__IMPDEF_boolean "Has 64K Translation Granule"))


def CheckTransactionalSystemAccess (op0 : (BitVec 2)) (op1 : (BitVec 3)) (crn : (BitVec 4)) (crm : (BitVec 4)) (op2 : (BitVec 3)) (read : (BitVec 1)) : SailM Bool := do
  let b__0 := (((((read +++ op0) +++ op1) +++ crn) +++ crm) +++ op2)
  if ((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb b__0 16 7)) == (0b0000110100#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
           b__0 2 1)) == (0b11#2 : (BitVec 2)))) : Bool)
  then (pure (true))
  else
    (do
      match b__0 with
      | 0b00101101110100001 => (pure (true))
      | b__0 =>
        (do
          if (((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb b__0 16 1)) == (0x6D08#16 : (BitVec 16))) : Bool)
          then (pure (true))
          else
            (do
              if (((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb b__0 16 1)) == (0x6D10#16 : (BitVec 16))) : Bool)
              then (pure (true))
              else
                (do
                  match b__0 with
                  | 0b01100001000110000 => (pure (true))
                  | 0b01101110011100100 => (pure (true))
                  | 0b11101100100101001 =>
                    (do
                      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure ((w__0.EL == EL0))))
                  | 0b11100000100101001 =>
                    (do
                      if ((← do
                           let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__1.EL == EL1) : Bool)))) : Bool)
                      then (pure true)
                      else
                        (do
                          if ((← do
                               let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
                               (pure (((w__2.EL == EL2) : Bool)))) : Bool)
                          then
                            (do
                              let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure ((((_get_HCR_EL2_Type_E2H w__3) == 1#1) : Bool))))
                          else (pure false)))
                  | 0b11110000100101001 =>
                    (do
                      if ((← do
                           let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                           (pure (((w__6.EL == EL2) : Bool)))) : Bool)
                      then
                        (do
                          let w__7 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                          (pure ((((_get_HCR_EL2_Type_E2H w__7) == 0#1) : Bool))))
                      else (pure false))
                  | 0b11111000100101001 =>
                    (do
                      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                      (pure ((w__9.EL == EL3))))
                  | 0b00101101110111000 => (pure (true))
                  | 0b10101101110111001 => (pure (true))
                  | 0b00101101110111010 => (pure (true))
                  | 0b10101101110111011 => (pure (true))
                  | 0b00100001110111110 => (pure (true))
                  | 0b11110100100101001 => (pure (false))
                  | 0b11100000100101010 => (pure (false))
                  | 0b11100000100101000 => (pure (false))
                  | 0b11110100100101000 => (pure (false))
                  | 0b11110000100101000 => (pure (false))
                  | 0b11111000100101000 => (pure (false))
                  | b__0 =>
                    (do
                      if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 16 14)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               b__0 10 10)) == (0#1 : (BitVec 1)))) : Bool)
                      then (pure (true))
                      else
                        (do
                          if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 16 14)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                   b__0 10 8)) == (0b100#3 : (BitVec 3)))) : Bool)
                          then (pure (true))
                          else
                            (do
                              if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 16
                                       14)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       b__0 10 7)) == (0xA#4 : (BitVec 4)))) : Bool)
                              then (pure (true))
                              else
                                (do
                                  if ((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                           b__0 16 6)) == (0b11100011001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                           b__0 4 0)) == (0b00010#5 : (BitVec 5)))) : Bool)
                                  then (pure (true))
                                  else
                                    (do
                                      match b__0 with
                                      | 0b11100011001011011 => (pure (true))
                                      | b__0 =>
                                        (do
                                          if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                   b__0 16 14)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   b__0 10 7)) == (0xD#4 : (BitVec 4)))) : Bool)
                                          then (pure (true))
                                          else
                                            (do
                                              if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                       b__0 16 14)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                       b__0 10 7)) == (0xE#4 : (BitVec 4)))) : Bool)
                                              then (pure (true))
                                              else
                                                (do
                                                  match b__0 with
                                                  | 0b00101101110011111 => (pure (true))
                                                  | b__0 =>
                                                    (do
                                                      if (((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb
                                                             b__0 16 1)) == (0x2DCE#16 : (BitVec 16))) : Bool)
                                                      then (pure (true))
                                                      else
                                                        (do
                                                          if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   b__0 15 14)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     b__0 10 10)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                     b__0 8 7)) == (0b11#2 : (BitVec 2))))) : Bool)
                                                          then
                                                            (do
                                                              (__IMPDEF_boolean
                                                                "Accessibility of registers encoded with op0=0b11 and CRn=0b1x11 is allowed"))
                                                          else (pure (false))))))))))))))))


def AArch64_S1DirectBasePermissions (regime : Regime) (walkstate : TTWState) (walkparams : S1TTWParams) (accdesc : AccessDescriptor) : SailM S1AccessControls := do
  let r ← (( do (undefined_bitvector_at (← occLabel 1410) 1) ) : SailM (BitVec 1) )
  let w ← (( do (undefined_bitvector_at (← occLabel 1411) 1) ) : SailM (BitVec 1) )
  let x ← (( do (undefined_bitvector_at (← occLabel 1412) 1) ) : SailM (BitVec 1) )
  let pr ← (( do (undefined_bitvector_at (← occLabel 1413) 1) ) : SailM (BitVec 1) )
  let pw ← (( do (undefined_bitvector_at (← occLabel 1414) 1) ) : SailM (BitVec 1) )
  let px ← (( do (undefined_bitvector_at (← occLabel 1415) 1) ) : SailM (BitVec 1) )
  let ur ← (( do (undefined_bitvector_at (← occLabel 1416) 1) ) : SailM (BitVec 1) )
  let uw ← (( do (undefined_bitvector_at (← occLabel 1417) 1) ) : SailM (BitVec 1) )
  let ux ← (( do (undefined_bitvector_at (← occLabel 1418) 1) ) : SailM (BitVec 1) )
  let permissions : Permissions := walkstate.permissions
  let s1perms ← (( do (undefined_S1AccessControls (← occLabel 1419) ()) ) : SailM
    S1AccessControls )
  let (pr, pw, px, ur, uw, ux) ← (( do
    if ((HasUnprivileged regime) : Bool)
    then
      (do
        let (pr, pw, ur, uw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
          match (BitVec.setWidth 2 (Sail.BitVec.extractLsb permissions.ap 2 1)) with
          | 0b00 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b01 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b10 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | _ =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((1#1, 0#1, 1#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
        let (pr, pw, ur, uw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
          match permissions.ap_table with
          | 0b00 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((pr, pw, ur, uw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b01 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((pr, pw, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | 0b10 =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((pr, 0#1, ur, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
          | _ =>
            (let (tup__0, tup__1, tup__2, tup__3) :=
              ((pr, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
            let pr : (BitVec 1) := tup__0
            let pw : (BitVec 1) := tup__1
            let ur : (BitVec 1) := tup__2
            let uw : (BitVec 1) := tup__3
            (pr, pw, ur, uw))
        let px : (BitVec 1) :=
          (Complement.complement ((permissions.pxn ||| permissions.pxn_table) ||| uw))
        let ux : (BitVec 1) := (Complement.complement (permissions.uxn ||| permissions.uxn_table))
        let w__2 ← (( do
          (pure ((← do
                (pure ((← do
                      (HavePANExt ())) && (accdesc.pan : Bool)))) && ((! ((BEq.beq regime
                    Regime_EL10) && (walkparams.nv1 == 1#1))) : Bool))) ) : SailM Bool )
        let (pr, pw, ux) ← (( do
          if (w__2 : Bool)
          then
            (do
              let w__6 ← (( do
                (pure ((← do
                      (pure ((← do
                            (pure ((← do
                                  (__IMPDEF_boolean "SCR_EL3.SIF affects EPAN")) && ((BEq.beq
                                  accdesc.ss SS_Secure) : Bool)))) && ((BEq.beq
                            walkstate.baseaddress.paspace PAS_NonSecure) : Bool)))) && ((walkparams.sif == 1#1) : Bool)))
                ) : SailM Bool )
              let ux : (BitVec 1) :=
                if (w__6 : Bool)
                then 0#1
                else ux
              let w__10 ← (( do
                (pure ((← do
                      (pure ((← do
                            (pure ((← do
                                  (__IMPDEF_boolean "Realm EL2&0 regime affects EPAN")) && ((BEq.beq
                                  accdesc.ss SS_Realm) : Bool)))) && ((BEq.beq regime Regime_EL20) : Bool)))) && ((bne
                      walkstate.baseaddress.paspace PAS_Realm) : Bool))) ) : SailM Bool )
              let ux : (BitVec 1) :=
                if (w__10 : Bool)
                then 0#1
                else ux
              let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
              let pan : (BitVec 1) := (w__11.PAN &&& ((ur ||| uw) ||| (walkparams.epan &&& ux)))
              let pr : (BitVec 1) := (pr &&& (Complement.complement pan))
              let pw : (BitVec 1) := (pw &&& (Complement.complement pan))
              (pure ((pr, pw, ux))))
          else (pure ((pr, pw, ux))) ) : SailM ((BitVec 1) × (BitVec 1) × (BitVec 1)) )
        (pure ((pr, pw, px, ur, uw, ux))))
    else
      (let (pr, pw) : ((BitVec 1) × (BitVec 1)) :=
        match (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access permissions.ap 2)])) with
        | 0 =>
          (let (tup__0, tup__1) := ((1#1, 1#1) : ((BitVec 1) × (BitVec 1)))
          let pr : (BitVec 1) := tup__0
          let pw : (BitVec 1) := tup__1
          (pr, pw))
        | _ =>
          (let (tup__0, tup__1) := ((1#1, 0#1) : ((BitVec 1) × (BitVec 1)))
          let pr : (BitVec 1) := tup__0
          let pw : (BitVec 1) := tup__1
          (pr, pw))
      let (pr, pw) : ((BitVec 1) × (BitVec 1)) :=
        match (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access permissions.ap_table 1)])) with
        | 0 =>
          (let (tup__0, tup__1) := ((pr, pw) : ((BitVec 1) × (BitVec 1)))
          let pr : (BitVec 1) := tup__0
          let pw : (BitVec 1) := tup__1
          (pr, pw))
        | _ =>
          (let (tup__0, tup__1) := ((pr, 0#1) : ((BitVec 1) × (BitVec 1)))
          let pr : (BitVec 1) := tup__0
          let pw : (BitVec 1) := tup__1
          (pr, pw))
      let px : (BitVec 1) := (Complement.complement (permissions.xn ||| permissions.xn_table))
      (pure ((pr, pw, px, ur, uw, ux)))) ) : SailM
    ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) )
  let (tup__0, tup__1, tup__2) :=
    (if ((accdesc.el == EL0) : Bool)
    then (ur, uw, ux)
    else (pr, pw, px) : ((BitVec 1) × (BitVec 1) × (BitVec 1)))
  let r : (BitVec 1) := tup__0
  let w : (BitVec 1) := tup__1
  let x : (BitVec 1) := tup__2
  let wxn : (BitVec 1) := ((walkparams.wxn &&& w) &&& x)
  let x : (BitVec 1) :=
    if (((BEq.beq accdesc.ss SS_Secure) && (BEq.beq walkstate.baseaddress.paspace PAS_NonSecure)) : Bool)
    then (x &&& (Complement.complement walkparams.sif))
    else x
  let x : (BitVec 1) :=
    if (((BEq.beq accdesc.ss SS_Root) && (bne walkstate.baseaddress.paspace PAS_Root)) : Bool)
    then 0#1
    else x
  let x : (BitVec 1) :=
    if ((((BEq.beq accdesc.ss SS_Realm) && ((BEq.beq regime Regime_EL2) || (BEq.beq regime
               Regime_EL20))) && (bne walkstate.baseaddress.paspace PAS_Realm)) : Bool)
    then 0#1
    else x
  let x := x
  let s1perms : S1AccessControls := { s1perms with r := r }
  let s1perms : S1AccessControls := { s1perms with w := w }
  let s1perms : S1AccessControls := { s1perms with x := x }
  let s1perms : S1AccessControls := { s1perms with gcs := 0#1 }
  let s1perms : S1AccessControls := { s1perms with wxn := wxn }
  let s1perms : S1AccessControls := { s1perms with overlay := true }
  (pure (s1perms))


/-- Type quantifiers: level : Int -/
def AArch64_ContiguousBitFaults (d128 : (BitVec 1)) (txsz : (BitVec 6)) (tgx : TGx) (level : Int) : SailM Bool := do
  let iasize : Int := (AArch64_IASize txsz)
  let w__0 ← (( do (ContiguousSize d128 tgx level) ) : SailM Int )
  let tsize : Int := ((TranslationSize d128 tgx level) +i w__0)
  if (((tsize >b iasize) : Bool) : Bool)
  then
    (do
      (__IMPDEF_boolean "Translation fault on misprogrammed contiguous bit"))
  else (pure false)


/-- Type quantifiers: k_N : Nat, 52 < k_N -/
def AArch64_S2NextWalkStateLeaf (currentstate : TTWState) (ss : SecurityState) (walkparams : S2TTWParams) (ipa : AddressDescriptor) (descriptor : (BitVec k_N)) : SailM TTWState := do
  let s2aarch64 ← (( do (undefined_bool_at (← occLabel 1561) ()) ) : SailM Bool )
  let nextstate ← (( do (undefined_TTWState (← occLabel 1562) ()) ) : SailM TTWState )
  let baseaddress ← (( do (undefined_FullAddress (← occLabel 1563) ()) ) : SailM FullAddress )
  let baseaddress ← (( do
    if ((BEq.beq ss SS_Secure) : Bool)
    then
      (let baseaddress : FullAddress :=
        { baseaddress with paspace := (AArch64_SS2OutputPASpace walkparams ipa.paddress.paspace) }
      (pure (baseaddress)))
    else
      (do
        if ((BEq.beq ss SS_Realm) : Bool)
        then
          (do
            let ns ← (( do
              if ((walkparams.d128 == 1#1) : Bool)
              then
                (do
                  ArmFull.assert (127 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26849.39-26849.40"
                  (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 127)])))))
              else
                (do
                  ArmFull.assert (55 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26852.38-26852.39"
                  (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 55)]))))) ) :
              SailM (BitVec 1) )
            let baseaddress : FullAddress :=
              { baseaddress with paspace := if ((ns == 1#1) : Bool)
                then PAS_NonSecure
                else PAS_Realm }
            (pure (baseaddress)))
        else
          (let baseaddress : FullAddress := { baseaddress with paspace := PAS_NonSecure }
          (pure (baseaddress)))) ) : SailM FullAddress )
  let w__0 ← (( do
    (AArch64_LeafBase descriptor walkparams.d128 walkparams.ds walkparams.tgx currentstate.level) )
    : SailM (BitVec 56) )
  let baseaddress := ({ baseaddress with address := w__0 } : FullAddress)
  let nextstate : TTWState := { nextstate with istable := false }
  let nextstate : TTWState := { nextstate with level := currentstate.level }
  let nextstate : TTWState := { nextstate with baseaddress := baseaddress }
  let w__1 ← (( do (AArch64_S2ApplyOutputPerms descriptor walkparams) ) : SailM Permissions )
  let nextstate := ({ nextstate with permissions := w__1 } : TTWState)
  let s2_attr : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 5 2)
  let s2_sh ← (( do
    if ((walkparams.ds == 1#1) : Bool)
    then (pure (walkparams.sh))
    else
      (do
        ArmFull.assert (9 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26866.33-26866.34"
        (pure ((Sail.BitVec.extractLsb descriptor 9 8)))) ) : SailM (BitVec 2) )
  let s2_fnxs : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)]))
  let nextstate ← (( do
    if ((walkparams.fwb == 1#1) : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_S2ApplyFWBMemAttrs ipa.memattrs walkparams descriptor) ) : SailM
          MemoryAttributes )
        let nextstate := ({ nextstate with memattrs := w__2 } : TTWState)
        let nextstate : TTWState :=
          if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb s2_attr 3 1)) == 0b111#3) : Bool)
          then { nextstate with permissions := { nextstate.permissions with s2tag_na := 1#1 } }
          else { nextstate with permissions := { nextstate.permissions with s2tag_na := 0#1 } }
        (pure (nextstate)))
    else
      (do
        let s2aarch64 : Bool := true
        let w__3 ← (( do (S2DecodeMemAttrs s2_attr s2_sh s2aarch64) ) : SailM MemoryAttributes )
        let nextstate := ({ nextstate with memattrs := w__3 } : TTWState)
        let nextstate : TTWState :=
          { nextstate with memattrs := { nextstate.memattrs with xs := (Complement.complement
                s2_fnxs) } }
        let nextstate : TTWState :=
          if ((s2_attr == 0b0100#4) : Bool)
          then { nextstate with permissions := { nextstate.permissions with s2tag_na := 1#1 } }
          else { nextstate with permissions := { nextstate.permissions with s2tag_na := 0#1 } }
        (pure (nextstate))) ) : SailM TTWState )
  let w__4 ← (( do
    (AArch64_ContiguousBit walkparams.tgx walkparams.d128 currentstate.level descriptor) ) : SailM
    (BitVec 1) )
  let nextstate := ({ nextstate with contiguous := w__4 } : TTWState)
  if ((walkparams.d128 == 1#1) : Bool)
  then
    (do
      ArmFull.assert (114 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26889.35-26889.36"
      let nextstate : TTWState :=
        { nextstate with s2assuredonly := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              descriptor 114)])) }
      (pure (nextstate)))
  else
    (do
      let w__5 ← (( do
        if ((walkparams.assuredonly == 1#1) : Bool)
        then
          (do
            ArmFull.assert (58 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26893.38-26893.39"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 58)])))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let nextstate := ({ nextstate with s2assuredonly := w__5 } : TTWState)
      (pure (nextstate)))


def MemHasTransactionalAccess (memattrs : MemoryAttributes) : SailM Bool := do
  if ((((((((((BEq.beq memattrs.shareability Shareability_ISH) || (BEq.beq memattrs.shareability
                       Shareability_OSH)) && (BEq.beq memattrs.memtype MemType_Normal)) && (memattrs.inner.attrs == MemAttr_WB)) && (memattrs.inner.hints == MemHint_RWA)) && (memattrs.inner.transient == false)) && (memattrs.outer.hints == MemHint_RWA)) && (memattrs.outer.attrs == MemAttr_WB)) && (memattrs.outer.transient == false)) : Bool)
  then (pure (true))
  else
    (do
      (__IMPDEF_boolean "Memory Region does not support Transactional access"))


def SPESetDataPhysicalAddress (addrdesc : AddressDescriptor) (accdesc : AccessDescriptor) : SailM Unit := do
  let ns ← (( do (undefined_bitvector_at (← occLabel 1628) 1) ) : SailM (BitVec 1) )
  let nse ← (( do (undefined_bitvector_at (← occLabel 1629) 1) ) : SailM (BitVec 1) )
  let (ns, nse) ← (( do
    match addrdesc.paddress.paspace with
    | .PAS_Secure =>
      (let ns : (BitVec 1) := 0#1
      let nse : (BitVec 1) := 0#1
      (pure ((ns, nse))))
    | .PAS_NonSecure =>
      (let ns : (BitVec 1) := 1#1
      let nse : (BitVec 1) := 0#1
      (pure ((ns, nse))))
    | .PAS_Realm =>
      (let ns : (BitVec 1) := 1#1
      let nse : (BitVec 1) := 1#1
      (pure ((ns, nse))))
    | _ =>
      (do
        (Unreachable ())
        (pure ((ns, nse)))) ) : SailM ((BitVec 1) × (BitVec 1)) )
  let w__0 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let pat ← (( do (undefined_bitvector_at (← occLabel 1630) 4) ) : SailM (BitVec 4) )
      let pat ← (( do
        if (accdesc.tagchecked : Bool)
        then
          (do
            let w__1 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
            let w__2 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
            writeReg SPESampleAddress (vectorUpdate w__1 SPEAddrPosDataPhysical
              (BitVec.update (GetElem?.getElem! w__2 SPEAddrPosDataPhysical) 62 (Bit 1#1)))
            let pat : (BitVec 4) := (AArch64_PhysicalTag addrdesc.vaddress)
            (pure (pat)))
        else
          (do
            let zero_unchecked ← (( do (__IMPDEF_boolean "SPE PAT for tag unchecked access zero")
              ) : SailM Bool )
            let pat : (BitVec 4) :=
              if ((! zero_unchecked) : Bool)
              then (AArch64_PhysicalTag addrdesc.vaddress)
              else (Zeros (n := 4))
            (pure (pat))) ) : SailM (BitVec 4) )
      let w__3 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
      let w__4 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
      writeReg SPESampleAddress (vectorUpdate w__3 SPEAddrPosDataPhysical
        (Sail.BitVec.updateSubrange (GetElem?.getElem! w__4 SPEAddrPosDataPhysical) 59 56 pat)))
  else (pure (()))
  let paddr : (BitVec 56) := addrdesc.paddress.address
  let w__5 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  let w__6 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  writeReg SPESampleAddress (vectorUpdate w__5 SPEAddrPosDataPhysical
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__6 SPEAddrPosDataPhysical)
      (Sail.Int.toNatChecked ((56 -i 1))) 0 paddr))
  let w__7 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  let w__8 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  writeReg SPESampleAddress (vectorUpdate w__7 SPEAddrPosDataPhysical
    (BitVec.update (GetElem?.getElem! w__8 SPEAddrPosDataPhysical) 63 (Bit ns)))
  let w__9 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  let w__10 ← (( do readReg SPESampleAddress ) : SailM (Vector (BitVec 64) 32) )
  writeReg SPESampleAddress (vectorUpdate w__9 SPEAddrPosDataPhysical
    (BitVec.update (GetElem?.getElem! w__10 SPEAddrPosDataPhysical) 60 (Bit nse)))
  let w__11 ← (( do readReg SPESampleAddressValid ) : SailM (Vector Bool 32) )
  writeReg SPESampleAddressValid (vectorUpdate w__11 SPEAddrPosDataPhysical true)


def CPYOptionA (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "CPY* instructions use Option A")


def CPYFOptionA (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "CPYF* instructions use Option A")


def SETOptionA (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "SET* instructions use Option A")


def SETGOptionA (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "SETG* instructions use Option A")


def GetPendingPhysicalSError (_ : Unit) : SailM FaultRecord := do
  let fault ← (( do (__UNKNOWN_FaultRecord ()) ) : SailM FaultRecord )
  let w__0 ← (( do (undefined_bool_at (← occLabel 1918) ()) ) : SailM Bool )
  let w__1 : Fault :=
    if ((w__0 : Bool) : Bool)
    then Fault_AsyncExternal
    else Fault_AsyncParity
  let fault := ({ fault with statuscode := w__1 } : FaultRecord)
  let w__2 ← (( do (GPCNoFault ()) ) : SailM GPCFRecord )
  let fault := ({ fault with gpcf := w__2 } : FaultRecord)
  let fault : FaultRecord := { fault with level := 0 }
  (pure (fault))


/-- Type quantifiers: k_cold : Bool -/
def AArch32_AutoGen_ArchitectureReset__seg3 (cold : Bool) : SailM Unit := do
  let w__1052 ← (( do readReg GICV_AEOIR ) : SailM (BitVec 32) )
  writeReg GICV_AEOIR (Sail.BitVec.updateSubrange w__1052 31 25 0b0000000#7)
  let w__1053 ← (( do readReg GICC_PMR ) : SailM (BitVec 32) )
  writeReg GICC_PMR (Sail.BitVec.updateSubrange w__1053 31 8 0b000000000000000000000000#24)
  let w__1054 ← (( do readReg GICV_ABPR ) : SailM (BitVec 32) )
  writeReg GICV_ABPR (Sail.BitVec.updateSubrange w__1054 31 3 0b00000000000000000000000000000#29)
  let w__1055 ← (( do readReg GICV_ABPR ) : SailM (BitVec 32) )
  writeReg GICV_ABPR (Sail.BitVec.updateSubrange w__1055 2 0 0b000#3)
  let w__1056 ← (( do readReg CTILSR ) : SailM (BitVec 32) )
  writeReg CTILSR (Sail.BitVec.updateSubrange w__1056 31 3 0b00000000000000000000000000000#29)
  let w__1057 ← (( do readReg CTILSR ) : SailM (BitVec 32) )
  writeReg CTILSR (Sail.BitVec.updateSubrange w__1057 1 1 1#1)
  let w__1058 ← (( do readReg GICR_MPAMIDR ) : SailM (BitVec 32) )
  writeReg GICR_MPAMIDR (Sail.BitVec.updateSubrange w__1058 31 24 0b00000000#8)
  let w__1059 ← (( do readReg CTICIDR3 ) : SailM (BitVec 32) )
  writeReg CTICIDR3 (Sail.BitVec.updateSubrange w__1059 31 8 0b000000000000000000000000#24)
  let w__1060 ← (( do readReg EDVIDSR ) : SailM (BitVec 32) )
  writeReg EDVIDSR (Sail.BitVec.updateSubrange w__1060 27 16 0b000000000000#12)
  let w__1061 ← (( do readReg GICC_RPR ) : SailM (BitVec 32) )
  writeReg GICC_RPR (Sail.BitVec.updateSubrange w__1061 31 8 0b000000000000000000000000#24)
  let w__1062 ← (( do readReg GICV_AIAR ) : SailM (BitVec 32) )
  writeReg GICV_AIAR (Sail.BitVec.updateSubrange w__1062 31 25 0b0000000#7)
  let w__1063 ← (( do readReg GICV_RPR ) : SailM (BitVec 32) )
  writeReg GICV_RPR (Sail.BitVec.updateSubrange w__1063 31 8 0b000000000000000000000000#24)
  if (cold : Bool)
  then
    (do
      let w__1064 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_TFO w__1064 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1065 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_RXfull w__1065 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1066 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_TXfull w__1066 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1067 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_RXO w__1067 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1068 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_TXU w__1068 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1069 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_INTdis w__1069 0b00#2)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1070 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_TDA w__1070 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1071 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_MA w__1071 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1072 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_SC2 w__1072 0#1)))
  else (pure (()))
  let w__1073 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  (EDSCR_write (Mk_EDSCR_Type (set_slice 1 w__1073 17 0#1)))
  if (cold : Bool)
  then
    (do
      let w__1074 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_HDE w__1074 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1075 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_ERR w__1075 0#1)))
  else (pure (()))
  let w__1076 ← (( do readReg GICV_AHPPIR ) : SailM (BitVec 32) )
  writeReg GICV_AHPPIR (Sail.BitVec.updateSubrange w__1076 31 25 0b0000000#7)
  let w__1077 ← (( do readReg GICR_CTLR ) : SailM (BitVec 32) )
  writeReg GICR_CTLR (Sail.BitVec.updateSubrange w__1077 30 27 0b0000#4)
  let w__1078 ← (( do readReg GICR_CTLR ) : SailM (BitVec 32) )
  writeReg GICR_CTLR (Sail.BitVec.updateSubrange w__1078 26 26 0#1)
  let w__1079 ← (( do readReg GICR_CTLR ) : SailM (BitVec 32) )
  writeReg GICR_CTLR (Sail.BitVec.updateSubrange w__1079 25 25 0#1)
  let w__1080 ← (( do readReg GICR_CTLR ) : SailM (BitVec 32) )
  writeReg GICR_CTLR (Sail.BitVec.updateSubrange w__1080 24 24 0#1)
  let w__1081 ← (( do readReg GICR_CTLR ) : SailM (BitVec 32) )
  writeReg GICR_CTLR (Sail.BitVec.updateSubrange w__1081 23 4 0b00000000000000000000#20)
  let w__1082 ← (( do readReg GICR_CTLR ) : SailM (BitVec 32) )
  writeReg GICR_CTLR (Sail.BitVec.updateSubrange w__1082 0 0 0#1)
  let w__1083 ← (( do readReg CNTEL0ACR ) : SailM (BitVec 32) )
  writeReg CNTEL0ACR (Sail.BitVec.updateSubrange w__1083 31 10 0b0000000000000000000000#22)
  let w__1084 ← (( do readReg CNTEL0ACR ) : SailM (BitVec 32) )
  writeReg CNTEL0ACR (Sail.BitVec.updateSubrange w__1084 7 2 0b000000#6)
  let w__1085 ← (( do readReg GICV_BPR ) : SailM (BitVec 32) )
  writeReg GICV_BPR (Sail.BitVec.updateSubrange w__1085 31 3 0b00000000000000000000000000000#29)
  let w__1086 ← (( do readReg EDDEVID2 ) : SailM (BitVec 32) )
  writeReg EDDEVID2 (Sail.BitVec.updateSubrange w__1086 31 0 0b00000000000000000000000000000000#32)
  let w__1087 ← (( do readReg GICV_EOIR ) : SailM (BitVec 32) )
  writeReg GICV_EOIR (Sail.BitVec.updateSubrange w__1087 31 25 0b0000000#7)
  let w__1088 ← (( do readReg CTICIDR0 ) : SailM (BitVec 32) )
  writeReg CTICIDR0 (Sail.BitVec.updateSubrange w__1088 31 8 0b000000000000000000000000#24)
  let w__1089 ← (( do readReg GICC_HPPIR ) : SailM (BitVec 32) )
  writeReg GICC_HPPIR (Sail.BitVec.updateSubrange w__1089 31 24 0b00000000#8)
  let w__1090 ← (( do readReg GICD_CLRSPI_NSR ) : SailM (BitVec 32) )
  writeReg GICD_CLRSPI_NSR (Sail.BitVec.updateSubrange w__1090 31 13 0b0000000000000000000#19)
  let w__1091 ← (( do readReg CTIITCTRL ) : SailM (BitVec 32) )
  writeReg CTIITCTRL (Sail.BitVec.updateSubrange w__1091 31 1 0b0000000000000000000000000000000#31)
  let w__1092 ← (( do readReg GITS_STATUSR ) : SailM (BitVec 32) )
  writeReg GITS_STATUSR (Sail.BitVec.updateSubrange w__1092 31 10 0b0000000000000000000000#22)
  let w__1093 ← (( do readReg GICH_VTR ) : SailM (BitVec 32) )
  writeReg GICH_VTR (Sail.BitVec.updateSubrange w__1093 20 5 0b0000000000000000#16)
  let w__1094 ← (( do readReg CTIPIDR3 ) : SailM (BitVec 32) )
  writeReg CTIPIDR3 (Sail.BitVec.updateSubrange w__1094 31 8 0b000000000000000000000000#24)
  let w__1095 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1095 31 10 0b0000000000000000000000#22)
  let w__1096 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1097 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
  let w__1098 : Int :=
    if (w__1097 : Bool)
    then 10
    else 9
  writeReg GICC_CTLR (BitVec.update w__1096 (Sail.Int.toNatChecked (w__1098)) (Bit 0#1))
  let w__1099 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1099 8 7 0b00#2)
  let w__1100 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1101 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1104 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1101) == 1#1) : Bool)
    then (pure (8))
    else
      (do
        let w__1102 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1103 : Int :=
          if (w__1102 : Bool)
          then 8
          else 6
        (pure (w__1103))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1100 (Sail.Int.toNatChecked (w__1104)) (Bit 0#1))
  let w__1105 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1106 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1109 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1106) == 1#1) : Bool)
    then (pure (7))
    else
      (do
        let w__1107 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1108 : Int :=
          if (w__1107 : Bool)
          then 7
          else 5
        (pure (w__1108))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1105 (Sail.Int.toNatChecked (w__1109)) (Bit 0#1))
  let w__1110 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1110 4 1 0b0000#4)
  let w__1111 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1112 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1115 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1112) == 1#1) : Bool)
    then (pure (1))
    else
      (do
        let w__1113 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1114 : Int :=
          if (w__1113 : Bool)
          then 1
          else 0
        (pure (w__1114))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1111 (Sail.Int.toNatChecked (w__1115)) (Bit 0#1))
  let w__1116 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1116 31 11 0b000000000000000000000#21)
  let w__1117 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1118 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
  let w__1119 : Int :=
    if (w__1118 : Bool)
    then 10
    else 9
  writeReg GICC_CTLR (BitVec.update w__1117 (Sail.Int.toNatChecked (w__1119)) (Bit 0#1))
  let w__1120 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1120 9 9 0#1)
  let w__1121 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1122 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1125 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1122) == 1#1) : Bool)
    then (pure (8))
    else
      (do
        let w__1123 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1124 : Int :=
          if (w__1123 : Bool)
          then 8
          else 6
        (pure (w__1124))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1121 (Sail.Int.toNatChecked (w__1125)) (Bit 0#1))
  let w__1126 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1127 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1130 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1127) == 1#1) : Bool)
    then (pure (7))
    else
      (do
        let w__1128 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1129 : Int :=
          if (w__1128 : Bool)
          then 7
          else 5
        (pure (w__1129))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1126 (Sail.Int.toNatChecked (w__1130)) (Bit 0#1))
  let w__1131 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1131 6 6 0#1)
  let w__1132 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1132 5 5 0#1)
  let w__1133 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1133 4 4 0#1)
  let w__1134 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1134 3 3 0#1)
  let w__1135 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (BitVec.update w__1135 2 (Bit 0#1))
  let w__1136 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1137 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1140 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1137) == 1#1) : Bool)
    then (pure (1))
    else
      (do
        let w__1138 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1139 : Int :=
          if (w__1138 : Bool)
          then 1
          else 0
        (pure (w__1139))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1136 (Sail.Int.toNatChecked (w__1140)) (Bit 0#1))
  let w__1141 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1141 0 0 0#1)
  let w__1142 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1142 31 10 0b0000000000000000000000#22)
  let w__1143 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1143 9 9 0#1)
  let w__1144 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1145 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1148 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1145) == 1#1) : Bool)
    then (pure (8))
    else
      (do
        let w__1146 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1147 : Int :=
          if (w__1146 : Bool)
          then 8
          else 6
        (pure (w__1147))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1144 (Sail.Int.toNatChecked (w__1148)) (Bit 0#1))
  let w__1149 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1150 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1153 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1150) == 1#1) : Bool)
    then (pure (7))
    else
      (do
        let w__1151 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1152 : Int :=
          if (w__1151 : Bool)
          then 7
          else 5
        (pure (w__1152))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1149 (Sail.Int.toNatChecked (w__1153)) (Bit 0#1))
  let w__1154 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1154 6 6 0#1)
  let w__1155 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1155 5 5 0#1)
  let w__1156 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1156 4 4 0#1)
  let w__1157 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1157 3 3 0#1)
  let w__1158 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (BitVec.update w__1158 2 (Bit 0#1))
  let w__1159 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  let w__1160 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__1163 ← (( do
    if (((_get_GICD_CTLR_Type_DS w__1160) == 1#1) : Bool)
    then (pure (1))
    else
      (do
        let w__1161 ← (( do (__IMPDEF_boolean "GICD_CTLR.DS==0, Secure access") ) : SailM Bool )
        let w__1162 : Int :=
          if (w__1161 : Bool)
          then 1
          else 0
        (pure (w__1162))) ) : SailM Int )
  writeReg GICC_CTLR (BitVec.update w__1159 (Sail.Int.toNatChecked (w__1163)) (Bit 0#1))
  let w__1164 ← (( do readReg GICC_CTLR ) : SailM (BitVec 32) )
  writeReg GICC_CTLR (Sail.BitVec.updateSubrange w__1164 0 0 0#1)
  let w__1165 ← (( do readReg EDPIDR4 ) : SailM (BitVec 32) )
  writeReg EDPIDR4 (Sail.BitVec.updateSubrange w__1165 31 8 0b000000000000000000000000#24)
  let w__1166 ← (( do readReg CTICONTROL ) : SailM (BitVec 32) )
  writeReg CTICONTROL (Sail.BitVec.updateSubrange w__1166 31 1 0b0000000000000000000000000000000#31)
  let w__1167 ← (( do readReg CTICONTROL ) : SailM (BitVec 32) )
  writeReg CTICONTROL (Sail.BitVec.updateSubrange w__1167 0 0 0#1)
  let w__1168 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (Sail.BitVec.updateSubrange w__1168 31 17 0b000000000000000#15)
  let w__1169 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (BitVec.update w__1169 15 (Bit 0#1))
  let w__1170 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (Sail.BitVec.updateSubrange w__1170 13 12 0b00#2)
  if (cold : Bool)
  then
    (do
      let w__1171 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
      writeReg EDPRSR (Sail.BitVec.updateSubrange w__1171 10 10 0#1))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1172 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
      writeReg EDPRSR (Sail.BitVec.updateSubrange w__1172 8 8 0#1))
  else (pure (()))
  let w__1173 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (Sail.BitVec.updateSubrange w__1173 3 3 1#1)
  if (cold : Bool)
  then
    (do
      let w__1174 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
      writeReg EDPRSR (Sail.BitVec.updateSubrange w__1174 1 1 1#1))
  else (pure (()))
  let w__1175 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1175 31 31 0#1)
  let w__1176 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1176 30 30 0#1)
  let w__1177 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1177 29 29 0#1)
  let w__1178 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1178 28 28 0#1)
  let w__1179 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1179 27 27 0#1)
  let w__1180 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1180 26 26 0#1)
  let w__1181 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1181 25 25 0#1)
  let w__1182 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1182 24 24 0#1)
  let w__1183 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1183 23 23 0#1)
  let w__1184 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1184 22 22 0#1)
  let w__1185 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1185 21 21 0#1)
  let w__1186 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1186 20 20 0#1)
  let w__1187 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1187 19 19 0#1)
  let w__1188 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1188 18 18 0#1)
  let w__1189 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1189 17 17 0#1)
  let w__1190 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1190 16 16 0#1)
  let w__1191 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1191 15 15 0#1)
  let w__1192 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1192 14 14 0#1)
  let w__1193 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1193 13 13 0#1)
  let w__1194 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1194 12 12 0#1)
  let w__1195 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1195 11 11 0#1)
  let w__1196 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1196 10 10 0#1)
  let w__1197 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1197 9 9 0#1)
  let w__1198 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1198 8 8 0#1)
  let w__1199 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1199 7 7 0#1)
  let w__1200 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1200 6 6 0#1)
  let w__1201 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1201 5 5 0#1)
  let w__1202 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1202 4 4 0#1)
  let w__1203 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1203 3 3 0#1)
  let w__1204 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1204 2 2 0#1)
  let w__1205 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1205 1 1 0#1)
  let w__1206 ← (( do readReg GICR_INMIR0 ) : SailM (BitVec 32) )
  writeReg GICR_INMIR0 (Sail.BitVec.updateSubrange w__1206 0 0 0#1)
  let w__1207 ← (( do readReg GICD_CLRSPI_SR ) : SailM (BitVec 32) )
  writeReg GICD_CLRSPI_SR (Sail.BitVec.updateSubrange w__1207 31 13 0b0000000000000000000#19)
  let w__1208 ← (( do readReg GICV_CTLR ) : SailM (BitVec 32) )
  writeReg GICV_CTLR (Sail.BitVec.updateSubrange w__1208 31 10 0b0000000000000000000000#22)
  let w__1209 ← (( do readReg GICV_CTLR ) : SailM (BitVec 32) )
  writeReg GICV_CTLR (Sail.BitVec.updateSubrange w__1209 8 5 0b0000#4)
  let w__1210 ← (( do readReg GICR_PARTIDR ) : SailM (BitVec 32) )
  writeReg GICR_PARTIDR (Sail.BitVec.updateSubrange w__1210 31 24 0b00000000#8)
  let w__1211 ← (( do readReg GICR_PARTIDR ) : SailM (BitVec 32) )
  writeReg GICR_PARTIDR (Sail.BitVec.updateSubrange w__1211 23 16 0b00000000#8)
  let w__1212 ← (( do readReg GICR_PARTIDR ) : SailM (BitVec 32) )
  writeReg GICR_PARTIDR (Sail.BitVec.updateSubrange w__1212 15 0 0b0000000000000000#16)
  let w__1213 ← (( do readReg EDDEVID1 ) : SailM (BitVec 32) )
  writeReg EDDEVID1 (Sail.BitVec.updateSubrange w__1213 31 8 0b000000000000000000000000#24)
  let w__1214 ← (( do readReg EDPRCR ) : SailM (BitVec 32) )
  writeReg EDPRCR (Sail.BitVec.updateSubrange w__1214 31 2 0b000000000000000000000000000000#30)
  let w__1215 ← (( do readReg EDPRCR ) : SailM (BitVec 32) )
  writeReg EDPRCR (Sail.BitVec.updateSubrange w__1215 31 4 0b0000000000000000000000000000#28)
  let w__1216 ← (( do readReg EDPRCR ) : SailM (BitVec 32) )
  writeReg EDPRCR (Sail.BitVec.updateSubrange w__1216 3 3 0#1)
  let w__1217 ← (( do readReg EDPRCR ) : SailM (BitVec 32) )
  writeReg EDPRCR (BitVec.update w__1217 2 (Bit 0#1))
  let w__1218 ← (( do readReg GICR_VSGIPENDR ) : SailM (BitVec 32) )
  writeReg GICR_VSGIPENDR (Sail.BitVec.updateSubrange w__1218 30 16 0b000000000000000#15)
  let w__1219 ← (( do readReg GICD_STATUSR ) : SailM (BitVec 32) )
  writeReg GICD_STATUSR (Sail.BitVec.updateSubrange w__1219 31 4 0b0000000000000000000000000000#28)
  let w__1220 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1220 31 31 0#1)
  let w__1221 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1221 30 30 0#1)
  let w__1222 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1222 29 29 0#1)
  let w__1223 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1223 28 28 0#1)
  let w__1224 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1224 27 27 0#1)
  let w__1225 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1225 26 26 0#1)
  let w__1226 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1226 25 25 0#1)
  let w__1227 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1227 24 24 0#1)
  let w__1228 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1228 23 23 0#1)
  let w__1229 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1229 22 22 0#1)
  let w__1230 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1230 21 21 0#1)
  let w__1231 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1231 20 20 0#1)
  let w__1232 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1232 19 19 0#1)
  let w__1233 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1233 18 18 0#1)
  let w__1234 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1234 17 17 0#1)
  let w__1235 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1235 16 16 0#1)
  let w__1236 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1236 15 15 0#1)
  let w__1237 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1237 14 14 0#1)
  let w__1238 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1238 13 13 0#1)
  let w__1239 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1239 12 12 0#1)
  let w__1240 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1240 11 11 0#1)
  let w__1241 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1241 10 10 0#1)
  let w__1242 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1242 9 9 0#1)
  let w__1243 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1243 8 8 0#1)
  let w__1244 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1244 7 7 0#1)
  let w__1245 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1245 6 6 0#1)
  let w__1246 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1246 5 5 0#1)
  let w__1247 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1247 4 4 0#1)
  let w__1248 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1248 3 3 0#1)
  let w__1249 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1249 2 2 0#1)
  let w__1250 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1250 1 1 0#1)
  let w__1251 ← (( do readReg GICR_ISENABLER0 ) : SailM (BitVec 32) )
  writeReg GICR_ISENABLER0 (Sail.BitVec.updateSubrange w__1251 0 0 0#1)
  let w__1252 ← (( do readReg CTICIDR2 ) : SailM (BitVec 32) )
  writeReg CTICIDR2 (Sail.BitVec.updateSubrange w__1252 31 8 0b000000000000000000000000#24)
  let w__1253 ← (( do readReg EDRCR ) : SailM (BitVec 32) )
  writeReg EDRCR (Sail.BitVec.updateSubrange w__1253 31 5 0b000000000000000000000000000#27)
  let w__1254 ← (( do readReg EDRCR ) : SailM (BitVec 32) )
  writeReg EDRCR (Sail.BitVec.updateSubrange w__1254 1 0 0b00#2)
  let w__1255 ← (( do readReg GICV_PMR ) : SailM (BitVec 32) )
  writeReg GICV_PMR (Sail.BitVec.updateSubrange w__1255 31 8 0b000000000000000000000000#24)
  let w__1256 ← (( do readReg EDDEVID ) : SailM (BitVec 32) )
  writeReg EDDEVID (Sail.BitVec.updateSubrange w__1256 31 28 0b0000#4)
  let w__1257 ← (( do readReg EDDEVID ) : SailM (BitVec 32) )
  writeReg EDDEVID (Sail.BitVec.updateSubrange w__1257 23 8 0b0000000000000000#16)
  let w__1258 ← (( do readReg GICC_DIR ) : SailM (BitVec 32) )
  writeReg GICC_DIR (Sail.BitVec.updateSubrange w__1258 31 24 0b00000000#8)
  let w__1259 ← (( do readReg EDCIDR0 ) : SailM (BitVec 32) )
  writeReg EDCIDR0 (Sail.BitVec.updateSubrange w__1259 31 8 0b000000000000000000000000#24)
  let w__1260 ← (( do readReg GITS_MPAMIDR ) : SailM (BitVec 32) )
  writeReg GITS_MPAMIDR (Sail.BitVec.updateSubrange w__1260 31 24 0b00000000#8)
  let w__1261 ← (( do readReg GICD_SGIR ) : SailM (BitVec 32) )
  writeReg GICD_SGIR (Sail.BitVec.updateSubrange w__1261 31 26 0b000000#6)
  let w__1262 ← (( do readReg GICD_SGIR ) : SailM (BitVec 32) )
  writeReg GICD_SGIR (Sail.BitVec.updateSubrange w__1262 14 4 0b00000000000#11)
  let w__1263 ← (( do readReg GICH_VMCR ) : SailM (BitVec 32) )
  writeReg GICH_VMCR (Sail.BitVec.updateSubrange w__1263 17 10 0b00000000#8)
  let w__1264 ← (( do readReg GICH_VMCR ) : SailM (BitVec 32) )
  writeReg GICH_VMCR (Sail.BitVec.updateSubrange w__1264 8 5 0b0000#4)
  let w__1265 ← (( do readReg EDLAR ) : SailM (BitVec 32) )
  writeReg EDLAR (Sail.BitVec.updateSubrange w__1265 31 0 0b00000000000000000000000000000000#32)
  let w__1266 ← (( do readReg GICC_AEOIR ) : SailM (BitVec 32) )
  writeReg GICC_AEOIR (Sail.BitVec.updateSubrange w__1266 31 24 0b00000000#8)
  let w__1267 ← (( do readReg GICC_AHPPIR ) : SailM (BitVec 32) )
  writeReg GICC_AHPPIR (Sail.BitVec.updateSubrange w__1267 31 24 0b00000000#8)
  let w__1268 ← (( do readReg GICR_SYNCR ) : SailM (BitVec 32) )
  writeReg GICR_SYNCR (Sail.BitVec.updateSubrange w__1268 31 1 0b0000000000000000000000000000000#31)
  let w__1269 ← (( do readReg GICC_ABPR ) : SailM (BitVec 32) )
  writeReg GICC_ABPR (Sail.BitVec.updateSubrange w__1269 31 3 0b00000000000000000000000000000#29)
  let w__1270 ← (( do readReg CTIPIDR4 ) : SailM (BitVec 32) )
  writeReg CTIPIDR4 (Sail.BitVec.updateSubrange w__1270 31 8 0b000000000000000000000000#24)
  let w__1271 ← (( do readReg CTIDEVID1 ) : SailM (BitVec 32) )
  writeReg CTIDEVID1 (Sail.BitVec.updateSubrange w__1271 31 0 0b00000000000000000000000000000000#32)
  let w__1272 ← (( do readReg GITS_MPIDR ) : SailM (BitVec 32) )
  writeReg GITS_MPIDR (Sail.BitVec.updateSubrange w__1272 7 0 0b00000000#8)
  let w__1273 ← (( do readReg EDCIDR2 ) : SailM (BitVec 32) )
  writeReg EDCIDR2 (Sail.BitVec.updateSubrange w__1273 31 8 0b000000000000000000000000#24)
  let w__1274 ← (( do readReg GICD_SETSPI_NSR ) : SailM (BitVec 32) )
  writeReg GICD_SETSPI_NSR (Sail.BitVec.updateSubrange w__1274 31 13 0b0000000000000000000#19)
  let w__1275 ← (( do readReg CNTID ) : SailM (BitVec 32) )
  writeReg CNTID (Sail.BitVec.updateSubrange w__1275 31 4 0b0000000000000000000000000000#28)
  let w__1276 ← (( do readReg GITS_IIDR ) : SailM (BitVec 32) )
  writeReg GITS_IIDR (Sail.BitVec.updateSubrange w__1276 23 20 0b0000#4)
  let w__1277 ← (( do readReg EDPIDR0 ) : SailM (BitVec 32) )
  writeReg EDPIDR0 (Sail.BitVec.updateSubrange w__1277 31 8 0b000000000000000000000000#24)
  let w__1278 ← (( do readReg CTIAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg CTIAUTHSTATUS (Sail.BitVec.updateSubrange w__1278 31 28 0b0000#4)
  let w__1279 ← (( do readReg CTIAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg CTIAUTHSTATUS (Sail.BitVec.updateSubrange w__1279 27 24 0b0000#4)
  let w__1280 ← (( do readReg CTIAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg CTIAUTHSTATUS (Sail.BitVec.updateSubrange w__1280 23 16 0b00000000#8)
  let w__1281 ← (( do readReg CTIAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg CTIAUTHSTATUS (Sail.BitVec.updateSubrange w__1281 15 12 0b0000#4)
  let w__1282 ← (( do readReg CTIAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg CTIAUTHSTATUS (Sail.BitVec.updateSubrange w__1282 11 8 0b0000#4)
  let w__1283 ← (( do readReg CTIAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg CTIAUTHSTATUS (Sail.BitVec.updateSubrange w__1283 7 4 0b0000#4)
  let w__1284 ← (( do readReg GICH_HCR ) : SailM (BitVec 32) )
  writeReg GICH_HCR (Sail.BitVec.updateSubrange w__1284 26 8 0b0000000000000000000#19)
  let w__1285 ← (( do readReg GICC_BPR ) : SailM (BitVec 32) )
  writeReg GICC_BPR (Sail.BitVec.updateSubrange w__1285 31 3 0b00000000000000000000000000000#29)
  let w__1286 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__1286 31 26 0b000000#6)
  let w__1287 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__1287 23 22 0b00#2)
  let w__1288 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__1288 15 14 0b00#2)
  let w__1289 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__1289 7 5 0b000#3)
  let w__1290 ← (( do readReg GICD_SETSPI_SR ) : SailM (BitVec 32) )
  writeReg GICD_SETSPI_SR (Sail.BitVec.updateSubrange w__1290 31 13 0b0000000000000000000#19)
  let w__1291 ← (( do readReg GICR_STATUSR ) : SailM (BitVec 32) )
  writeReg GICR_STATUSR (Sail.BitVec.updateSubrange w__1291 31 4 0b0000000000000000000000000000#28)
  let w__1292 ← (( do readReg GICC_EOIR ) : SailM (BitVec 32) )
  writeReg GICC_EOIR (Sail.BitVec.updateSubrange w__1292 31 24 0b00000000#8)
  let w__1293 ← (( do readReg EDPIDR2 ) : SailM (BitVec 32) )
  writeReg EDPIDR2 (Sail.BitVec.updateSubrange w__1293 31 8 0b000000000000000000000000#24)
  let w__1294 ← (( do readReg CNTNSAR ) : SailM (BitVec 32) )
  writeReg CNTNSAR (Sail.BitVec.updateSubrange w__1294 31 8 0b000000000000000000000000#24)
  let w__1295 ← (( do readReg EDITCTRL ) : SailM (BitVec 32) )
  writeReg EDITCTRL (Sail.BitVec.updateSubrange w__1295 31 1 0b0000000000000000000000000000000#31)
  let w__1296 ← (( do readReg GICD_IIDR ) : SailM (BitVec 32) )
  writeReg GICD_IIDR (Sail.BitVec.updateSubrange w__1296 23 20 0b0000#4)
  let w__1297 ← (( do readReg EDCIDR1 ) : SailM (BitVec 32) )
  writeReg EDCIDR1 (Sail.BitVec.updateSubrange w__1297 31 8 0b000000000000000000000000#24)
  let w__1298 ← (( do readReg GICC_AIAR ) : SailM (BitVec 32) )
  writeReg GICC_AIAR (Sail.BitVec.updateSubrange w__1298 31 24 0b00000000#8)
  let w__1299 ← (( do readReg AMPIDR2 ) : SailM (BitVec 32) )
  writeReg AMPIDR2 (Sail.BitVec.updateSubrange w__1299 31 8 0b000000000000000000000000#24)
  let w__1300 ← (( do readReg AMPIDR4 ) : SailM (BitVec 32) )
  writeReg AMPIDR4 (Sail.BitVec.updateSubrange w__1300 31 8 0b000000000000000000000000#24)
  let w__1301 ← (( do readReg AMPIDR3 ) : SailM (BitVec 32) )
  writeReg AMPIDR3 (Sail.BitVec.updateSubrange w__1301 31 8 0b000000000000000000000000#24)
  let w__1302 ← (( do readReg AMCIDR3 ) : SailM (BitVec 32) )
  writeReg AMCIDR3 (Sail.BitVec.updateSubrange w__1302 31 8 0b000000000000000000000000#24)
  let w__1303 ← (( do readReg AMPIDR0 ) : SailM (BitVec 32) )
  writeReg AMPIDR0 (Sail.BitVec.updateSubrange w__1303 31 8 0b000000000000000000000000#24)
  let w__1304 ← (( do readReg AMCIDR2 ) : SailM (BitVec 32) )
  writeReg AMCIDR2 (Sail.BitVec.updateSubrange w__1304 31 8 0b000000000000000000000000#24)
  let w__1305 ← (( do readReg AMCIDR0 ) : SailM (BitVec 32) )
  writeReg AMCIDR0 (Sail.BitVec.updateSubrange w__1305 31 8 0b000000000000000000000000#24)
  let w__1306 ← (( do readReg AMPIDR1 ) : SailM (BitVec 32) )
  writeReg AMPIDR1 (Sail.BitVec.updateSubrange w__1306 31 8 0b000000000000000000000000#24)
  let w__1307 ← (( do readReg AMCIDR1 ) : SailM (BitVec 32) )
  writeReg AMCIDR1 (Sail.BitVec.updateSubrange w__1307 31 8 0b000000000000000000000000#24)
  let w__1308 ← (( do readReg AMDEVTYPE ) : SailM (BitVec 32) )
  writeReg AMDEVTYPE (Sail.BitVec.updateSubrange w__1308 31 8 0b000000000000000000000000#24)
  let w__1309 ← (( do readReg PMAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg PMAUTHSTATUS (Sail.BitVec.updateSubrange w__1309 31 28 0b0000#4)
  let w__1310 ← (( do readReg PMAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg PMAUTHSTATUS (Sail.BitVec.updateSubrange w__1310 23 16 0b00000000#8)
  let w__1311 ← (( do readReg PMAUTHSTATUS ) : SailM (BitVec 32) )
  writeReg PMAUTHSTATUS (Sail.BitVec.updateSubrange w__1311 11 8 0b0000#4)
  let w__1312 ← (( do readReg PMCGCR0 ) : SailM (BitVec 32) )
  writeReg PMCGCR0 (Sail.BitVec.updateSubrange w__1312 31 16 0b0000000000000000#16)
  let w__1313 ← (( do readReg PMCIDR0 ) : SailM (BitVec 32) )
  writeReg PMCIDR0 (Sail.BitVec.updateSubrange w__1313 31 8 0b000000000000000000000000#24)
  let w__1314 ← (( do readReg PMCIDR1 ) : SailM (BitVec 32) )
  writeReg PMCIDR1 (Sail.BitVec.updateSubrange w__1314 31 8 0b000000000000000000000000#24)
  let w__1315 ← (( do readReg PMCIDR2 ) : SailM (BitVec 32) )
  writeReg PMCIDR2 (Sail.BitVec.updateSubrange w__1315 31 8 0b000000000000000000000000#24)
  let w__1316 ← (( do readReg PMCIDR3 ) : SailM (BitVec 32) )
  writeReg PMCIDR3 (Sail.BitVec.updateSubrange w__1316 31 8 0b000000000000000000000000#24)
  let w__1317 ← (( do readReg PMDEVID ) : SailM (BitVec 32) )
  writeReg PMDEVID (Sail.BitVec.updateSubrange w__1317 31 8 0b000000000000000000000000#24)
  let w__1318 ← (( do readReg PMDEVTYPE ) : SailM (BitVec 32) )
  writeReg PMDEVTYPE (Sail.BitVec.updateSubrange w__1318 31 8 0b000000000000000000000000#24)
  let w__1319 ← (( do readReg PMITCTRL ) : SailM (BitVec 32) )
  writeReg PMITCTRL (Sail.BitVec.updateSubrange w__1319 31 1 0b0000000000000000000000000000000#31)
  let w__1320 ← (( do readReg PMLAR ) : SailM (BitVec 32) )
  writeReg PMLAR (Sail.BitVec.updateSubrange w__1320 31 0 0b00000000000000000000000000000000#32)
  let w__1321 ← (( do readReg PMLSR ) : SailM (BitVec 32) )
  writeReg PMLSR (Sail.BitVec.updateSubrange w__1321 31 3 0b00000000000000000000000000000#29)
  let w__1322 ← (( do readReg PMLSR ) : SailM (BitVec 32) )
  writeReg PMLSR (Sail.BitVec.updateSubrange w__1322 1 1 1#1)
  let w__1323 ← (( do readReg PMPIDR0 ) : SailM (BitVec 32) )
  writeReg PMPIDR0 (Sail.BitVec.updateSubrange w__1323 31 8 0b000000000000000000000000#24)
  let w__1324 ← (( do readReg PMPIDR1 ) : SailM (BitVec 32) )
  writeReg PMPIDR1 (Sail.BitVec.updateSubrange w__1324 31 8 0b000000000000000000000000#24)
  let w__1325 ← (( do readReg PMPIDR2 ) : SailM (BitVec 32) )
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange w__1325 31 8 0b000000000000000000000000#24)
  let w__1326 ← (( do readReg PMPIDR3 ) : SailM (BitVec 32) )
  writeReg PMPIDR3 (Sail.BitVec.updateSubrange w__1326 31 8 0b000000000000000000000000#24)
  let w__1327 ← (( do readReg PMPIDR4 ) : SailM (BitVec 32) )
  writeReg PMPIDR4 (Sail.BitVec.updateSubrange w__1327 31 8 0b000000000000000000000000#24)
  let w__1328 ← (( do readReg PMVIDSR ) : SailM (BitVec 32) )
  writeReg PMVIDSR (Sail.BitVec.updateSubrange w__1328 31 16 0b0000000000000000#16)


end ArmFull.Functions
