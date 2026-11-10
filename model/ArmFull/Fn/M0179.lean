import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0087
import ArmFull.Fn.M0117
import ArmFull.Fn.M0124
import ArmFull.Fn.M0143
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0166
import ArmFull.Fn.M0171
import ArmFull.Fn.M0172
import ArmFull.Fn.M0173
import ArmFull.Fn.M0174
import ArmFull.Fn.M0175
import ArmFull.Fn.M0178

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

def AArch32_AbortSyndrome (exceptype : Exception) (fault : FaultRecord) (vaddress : (BitVec 32)) (target_el : (BitVec 2)) : SailM ExceptionRecord := do
  let except ← (( do (ExceptionSyndrome exceptype) ) : SailM ExceptionRecord )
  let d_side : Bool := (BEq.beq exceptype Exception_DataAbort)
  let w__0 ← (( do (AArch32_FaultSyndrome d_side fault) ) : SailM (BitVec 25) )
  let except := ({ except with syndrome := w__0 } : ExceptionRecord)
  let except : ExceptionRecord := { except with vaddress := (Sail.BitVec.zeroExtend vaddress 64) }
  let w__1 ← (( do (IPAValid fault) ) : SailM Bool )
  let except : ExceptionRecord :=
    if (w__1 : Bool)
    then
      (let except : ExceptionRecord := { except with ipavalid := true }
      let except : ExceptionRecord :=
        { except with NS := if ((BEq.beq fault.ipaddress.paspace PAS_NonSecure) : Bool)
          then 1#1
          else 0#1 }
      { except with ipaddress := (Sail.BitVec.zeroExtend fault.ipaddress.address 56) })
    else { except with ipavalid := false }
  (pure (except))


def AArch64_PACEffectiveTxSZ (regime : Regime) (walkparams : S1TTWParams) : SailM (BitVec 6) := SailME.run do
  let s1maxtxsz ← (( do (AArch64_MaxTxSZ walkparams.tgx) ) : SailME (BitVec 6) Int )
  let s1mintxsz ← (( do (AArch64_S1MinTxSZ regime walkparams.d128 walkparams.ds walkparams.tgx) )
    : SailME (BitVec 6) Int )
  let w__0 ← (( do (AArch64_S1TxSZFaults regime walkparams) ) : SailME (BitVec 6) Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (ConstrainUnpredictable Unpredictable_RESTnSZ) ) : SailME (BitVec 6)
        Constraint )
      if ((BEq.beq w__1 Constraint_FORCE) : Bool)
      then
        (do
          if (((BitVec.toNat walkparams.txsz) <b s1mintxsz) : Bool)
          then
            (do
              SailME.throw ((integer_subrange s1mintxsz 5 0) : (BitVec 6)))
          else
            (do
              if (((BitVec.toNat walkparams.txsz) >b s1maxtxsz) : Bool)
              then
                (do
                  SailME.throw ((integer_subrange s1maxtxsz 5 0) : (BitVec 6)))
              else (pure (()))))
      else (pure (())))
  else
    (do
      if (((BitVec.toNat walkparams.txsz) <b s1mintxsz) : Bool)
      then
        (do
          SailME.throw ((integer_subrange s1mintxsz 5 0) : (BitVec 6)))
      else
        (do
          if (((BitVec.toNat walkparams.txsz) >b s1maxtxsz) : Bool)
          then
            (do
              SailME.throw ((integer_subrange s1maxtxsz 5 0) : (BitVec 6)))
          else (pure (()))))
  (pure (walkparams.txsz))


def AArch64_S1DecodeTG0 (tg0_in : (BitVec 2)) : SailM TGx := do
  let tg0 : (BitVec 2) := tg0_in
  let tgx ← (( do (undefined_TGx (← occLabel 1253) ()) ) : SailM TGx )
  let tg0 ← (( do
    if ((tg0 == 0b11#2) : Bool)
    then
      (do
        (__IMPDEF_bits 2 "TG0 encoded granule size"))
    else (pure (tg0)) ) : SailM (BitVec 2) )
  let tgx : TGx :=
    match tg0 with
    | 0b00 => TGx_4KB
    | 0b01 => TGx_64KB
    | 0b10 => TGx_16KB
    | _ => tgx
  let w__1 ← (( do (AArch64_HaveS1TG tgx) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      let w__2 ← (( do (__IMPDEF_bits 2 "TG0 encoded granule size") ) : SailM (BitVec 2) )
      let tgx : TGx :=
        match w__2 with
        | 0b00 => TGx_4KB
        | 0b01 => TGx_64KB
        | 0b10 => TGx_16KB
        | _ => tgx
      (pure (tgx)))
  else (pure (tgx))


def AArch64_S1DecodeTG1 (tg1_in : (BitVec 2)) : SailM TGx := do
  let tg1 : (BitVec 2) := tg1_in
  let tgx ← (( do (undefined_TGx (← occLabel 1254) ()) ) : SailM TGx )
  let tg1 ← (( do
    if ((tg1 == 0b00#2) : Bool)
    then
      (do
        (__IMPDEF_bits 2 "TG1 encoded granule size"))
    else (pure (tg1)) ) : SailM (BitVec 2) )
  let tgx : TGx :=
    match tg1 with
    | 0b10 => TGx_4KB
    | 0b11 => TGx_64KB
    | 0b01 => TGx_16KB
    | _ => tgx
  let w__1 ← (( do (AArch64_HaveS1TG tgx) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      let w__2 ← (( do (__IMPDEF_bits 2 "TG1 encoded granule size") ) : SailM (BitVec 2) )
      let tgx : TGx :=
        match w__2 with
        | 0b10 => TGx_4KB
        | 0b11 => TGx_64KB
        | 0b01 => TGx_16KB
        | _ => tgx
      (pure (tgx)))
  else (pure (tgx))


def AArch64_HaveS2TG (tgx : TGx) : SailM Bool := do
  ArmFull.assert (HaveEL EL2) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:25703.22-25703.23"
  let w__0 ← (( do (HaveGTGExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      match tgx with
      | .TGx_4KB =>
        (do
          (__IMPDEF_boolean "Has Stage 2 4K Translation Granule"))
      | .TGx_16KB =>
        (do
          (__IMPDEF_boolean "Has Stage 2 16K Translation Granule"))
      | .TGx_64KB =>
        (do
          (__IMPDEF_boolean "Has Stage 2 64K Translation Granule")))
  else
    (do
      (AArch64_HaveS1TG tgx))


def S2TLBLookup (tlbcontext : TLBContext) : SailM TLBLine := do
  (__UNKNOWN_TLBLine ())


def S1TLBLookup (tlbcontext : TLBContext) : SailM TLBLine := do
  (__UNKNOWN_TLBLine ())


/-- Type quantifiers: ec : Int -/
def AArch64_SystemAccessTrapSyndrome (instr_in : (BitVec 32)) (ec : Int) : SailM ExceptionRecord := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2414) ()) ) : SailM ExceptionRecord
    )
  let instr : (BitVec 32) := instr_in
  match ec with
  | 0 =>
    (do
      (ExceptionSyndrome Exception_Uncategorized))
  | 7 =>
    (do
      let w__1 ← (( do (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap) ) : SailM ExceptionRecord
        )
      let except := (w__1 : ExceptionRecord)
      let w__2 ← (( do (ConditionSyndrome ()) ) : SailM (BitVec 5) )
      let except :=
        ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 20 w__2) } : ExceptionRecord)
      (pure (except)))
  | 20 =>
    (do
      let w__3 ← (( do (ExceptionSyndrome Exception_SystemRegister128Trap) ) : SailM
        ExceptionRecord )
      let except := (w__3 : ExceptionRecord)
      let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 21 20
            (Sail.BitVec.extractLsb instr 20 19)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 17
            (Sail.BitVec.extractLsb instr 7 5)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 16 14
            (Sail.BitVec.extractLsb instr 18 16)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 13 10
            (Sail.BitVec.extractLsb instr 15 12)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 6
            (Sail.BitVec.extractLsb instr 4 1)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 1
            (Sail.BitVec.extractLsb instr 11 8)) }
      let except : ExceptionRecord :=
        { except with syndrome := (BitVec.update except.syndrome 0
            (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 21)])))) }
      (pure (except)))
  | 24 =>
    (do
      let w__4 ← (( do (ExceptionSyndrome Exception_SystemRegisterTrap) ) : SailM ExceptionRecord
        )
      let except := (w__4 : ExceptionRecord)
      let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 21 20
            (Sail.BitVec.extractLsb instr 20 19)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 17
            (Sail.BitVec.extractLsb instr 7 5)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 16 14
            (Sail.BitVec.extractLsb instr 18 16)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 13 10
            (Sail.BitVec.extractLsb instr 15 12)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 9 5
            (Sail.BitVec.extractLsb instr 4 0)) }
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 4 1
            (Sail.BitVec.extractLsb instr 11 8)) }
      let except : ExceptionRecord :=
        { except with syndrome := (BitVec.update except.syndrome 0
            (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 21)])))) }
      (pure (except)))
  | 25 =>
    (do
      (ExceptionSyndrome Exception_SVEAccessTrap))
  | 29 =>
    (do
      (ExceptionSyndrome Exception_SMEAccessTrap))
  | _ =>
    (do
      (Unreachable ())
      (pure (except)))


/-- Type quantifiers: ec : Int -/
def AArch64_AArch32SystemAccessTrapSyndrome (instr : (BitVec 32)) (ec : Int) : SailM ExceptionRecord := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2415) ()) ) : SailM ExceptionRecord
    )
  let except ← (( do
    match ec with
    | 0 =>
      (do
        (ExceptionSyndrome Exception_Uncategorized))
    | 3 =>
      (do
        (ExceptionSyndrome Exception_CP15RTTrap))
    | 4 =>
      (do
        (ExceptionSyndrome Exception_CP15RRTTrap))
    | 5 =>
      (do
        (ExceptionSyndrome Exception_CP14RTTrap))
    | 6 =>
      (do
        (ExceptionSyndrome Exception_CP14DTTrap))
    | 7 =>
      (do
        (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap))
    | 8 =>
      (do
        (ExceptionSyndrome Exception_FPIDTrap))
    | 12 =>
      (do
        (ExceptionSyndrome Exception_CP14RRTTrap))
    | _ =>
      (do
        (Unreachable ())
        (pure (except))) ) : SailM ExceptionRecord )
  let iss : (BitVec 20) := (Zeros (n := 20))
  if ((BEq.beq except.exceptype Exception_Uncategorized) : Bool)
  then (pure (except))
  else
    (do
      let iss ← (( do
        if (((BEq.beq except.exceptype Exception_FPIDTrap) || ((BEq.beq except.exceptype
                 Exception_CP14RTTrap) || (BEq.beq except.exceptype Exception_CP15RTTrap))) : Bool)
        then
          (do
            let iss : (BitVec 20) :=
              if ((bne except.exceptype Exception_FPIDTrap) : Bool)
              then
                (let iss : (BitVec 20) :=
                  (Sail.BitVec.updateSubrange iss 19 17 (Sail.BitVec.extractLsb instr 7 5))
                let iss : (BitVec 20) :=
                  (Sail.BitVec.updateSubrange iss 16 14 (Sail.BitVec.extractLsb instr 23 21))
                let iss : (BitVec 20) :=
                  (Sail.BitVec.updateSubrange iss 13 10 (Sail.BitVec.extractLsb instr 19 16))
                (Sail.BitVec.updateSubrange iss 4 1 (Sail.BitVec.extractLsb instr 3 0)))
              else
                (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 17 0b000#3)
                let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 16 14 0b111#3)
                let iss : (BitVec 20) :=
                  (Sail.BitVec.updateSubrange iss 13 10 (Sail.BitVec.extractLsb instr 19 16))
                (Sail.BitVec.updateSubrange iss 4 1 0b0000#4))
            if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 20)])) == 1#1) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                     instr 15 12)) == 0b1111#4)) : Bool)
            then
              (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 9 5 0b11111#5)
              (pure (iss)))
            else
              (do
                if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 20)])) == 0#1) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                         instr 15 12)) == 0b1111#4)) : Bool)
                then
                  (do
                    let w__8 ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
                    let iss := ((Sail.BitVec.updateSubrange iss 9 5 w__8) : (BitVec 20))
                    (pure (iss)))
                else
                  (do
                    let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
                    let w__10 ← (( do
                      (LookUpRIndex (BitVec.toNat (Sail.BitVec.extractLsb instr 15 12)) w__9.M) ) :
                      SailM Int )
                    let iss :=
                      ((Sail.BitVec.updateSubrange iss 9 5 (integer_subrange w__10 4 0)) : (BitVec 20))
                    (pure (iss)))))
        else
          (do
            if (((BEq.beq except.exceptype Exception_CP14RRTTrap) || ((BEq.beq except.exceptype
                     Exception_AdvSIMDFPAccessTrap) || (BEq.beq except.exceptype
                     Exception_CP15RRTTrap))) : Bool)
            then
              (do
                let iss : (BitVec 20) :=
                  (Sail.BitVec.updateSubrange iss 19 16 (Sail.BitVec.extractLsb instr 7 4))
                let iss ← (( do
                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb instr 19 16)) == 0b1111#4) : Bool)
                  then
                    (do
                      let w__11 ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
                      let iss := ((Sail.BitVec.updateSubrange iss 14 10 w__11) : (BitVec 20))
                      (pure (iss)))
                  else
                    (do
                      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
                      let w__13 ← (( do
                        (LookUpRIndex (BitVec.toNat (Sail.BitVec.extractLsb instr 19 16)) w__12.M) )
                        : SailM Int )
                      let iss :=
                        ((Sail.BitVec.updateSubrange iss 14 10 (integer_subrange w__13 4 0)) : (BitVec 20))
                      (pure (iss))) ) : SailM (BitVec 20) )
                let iss ← (( do
                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb instr 15 12)) == 0b1111#4) : Bool)
                  then
                    (do
                      let w__14 ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
                      let iss := ((Sail.BitVec.updateSubrange iss 9 5 w__14) : (BitVec 20))
                      (pure (iss)))
                  else
                    (do
                      let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                      let w__16 ← (( do
                        (LookUpRIndex (BitVec.toNat (Sail.BitVec.extractLsb instr 15 12)) w__15.M) )
                        : SailM Int )
                      let iss :=
                        ((Sail.BitVec.updateSubrange iss 9 5 (integer_subrange w__16 4 0)) : (BitVec 20))
                      (pure (iss))) ) : SailM (BitVec 20) )
                let iss : (BitVec 20) :=
                  (Sail.BitVec.updateSubrange iss 4 1 (Sail.BitVec.extractLsb instr 3 0))
                (pure (iss)))
            else
              (do
                if ((BEq.beq except.exceptype Exception_CP14DTTrap) : Bool)
                then
                  (do
                    let iss : (BitVec 20) :=
                      (Sail.BitVec.updateSubrange iss 19 12 (Sail.BitVec.extractLsb instr 7 0))
                    let iss : (BitVec 20) :=
                      (BitVec.update iss 4
                        (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 23)]))))
                    let iss : (BitVec 20) :=
                      (Sail.BitVec.updateSubrange iss 2 1
                        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 24)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                              instr 21)]))))
                    if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb instr 19 16)) == 0b1111#4) : Bool)
                    then
                      (do
                        let w__17 ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
                        let iss := ((Sail.BitVec.updateSubrange iss 9 5 w__17) : (BitVec 20))
                        let iss : (BitVec 20) := (BitVec.update iss 3 (Bit 1#1))
                        (pure (iss)))
                    else (pure (iss)))
                else (pure (iss)))) ) : SailM (BitVec 20) )
      let iss : (BitVec 20) :=
        (BitVec.update iss 0 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 20)]))))
      let w__18 ← (( do (ConditionSyndrome ()) ) : SailM (BitVec 5) )
      let except :=
        ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 20 w__18) } : ExceptionRecord)
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 0 iss) }
      (pure (except)))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV87 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap7_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV86 enabled))
  else (pure (()))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV91 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap1_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV90 enabled)
      (__ConfigureV86 enabled))
  else (pure (()))


/-- Type quantifiers: ec : Int -/
def AArch32_SystemAccessTrapSyndrome (instr : (BitVec 32)) (ec : Int) : SailM ExceptionRecord := do
  let except ← (( do (undefined_ExceptionRecord (← occLabel 2708) ()) ) : SailM ExceptionRecord
    )
  let except ← (( do
    match ec with
    | 0 =>
      (do
        (ExceptionSyndrome Exception_Uncategorized))
    | 3 =>
      (do
        (ExceptionSyndrome Exception_CP15RTTrap))
    | 4 =>
      (do
        (ExceptionSyndrome Exception_CP15RRTTrap))
    | 5 =>
      (do
        (ExceptionSyndrome Exception_CP14RTTrap))
    | 6 =>
      (do
        (ExceptionSyndrome Exception_CP14DTTrap))
    | 7 =>
      (do
        (ExceptionSyndrome Exception_AdvSIMDFPAccessTrap))
    | 8 =>
      (do
        (ExceptionSyndrome Exception_FPIDTrap))
    | 12 =>
      (do
        (ExceptionSyndrome Exception_CP14RRTTrap))
    | _ =>
      (do
        (Unreachable ())
        (pure (except))) ) : SailM ExceptionRecord )
  let iss : (BitVec 20) := (Zeros (n := 20))
  if ((BEq.beq except.exceptype Exception_Uncategorized) : Bool)
  then (pure (except))
  else
    (do
      let iss ← (( do
        if (((BEq.beq except.exceptype Exception_FPIDTrap) || ((BEq.beq except.exceptype
                 Exception_CP14RTTrap) || (BEq.beq except.exceptype Exception_CP15RTTrap))) : Bool)
        then
          (let iss : (BitVec 20) :=
            (Sail.BitVec.updateSubrange iss 13 10 (Sail.BitVec.extractLsb instr 19 16))
          let iss : (BitVec 20) :=
            (Sail.BitVec.updateSubrange iss 8 5 (Sail.BitVec.extractLsb instr 15 12))
          let iss : (BitVec 20) := (BitVec.update iss 9 (Bit 0#1))
          let iss : (BitVec 20) :=
            if ((bne except.exceptype Exception_FPIDTrap) : Bool)
            then
              (let iss : (BitVec 20) :=
                (Sail.BitVec.updateSubrange iss 19 17 (Sail.BitVec.extractLsb instr 7 5))
              let iss : (BitVec 20) :=
                (Sail.BitVec.updateSubrange iss 16 14 (Sail.BitVec.extractLsb instr 23 21))
              (Sail.BitVec.updateSubrange iss 4 1 (Sail.BitVec.extractLsb instr 3 0)))
            else
              (let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 19 17 0b000#3)
              let iss : (BitVec 20) := (Sail.BitVec.updateSubrange iss 16 14 0b111#3)
              (Sail.BitVec.updateSubrange iss 4 1 0b0000#4))
          (pure (iss)))
        else
          (do
            if (((BEq.beq except.exceptype Exception_CP14RRTTrap) || ((BEq.beq except.exceptype
                     Exception_AdvSIMDFPAccessTrap) || (BEq.beq except.exceptype
                     Exception_CP15RRTTrap))) : Bool)
            then
              (let iss : (BitVec 20) :=
                (Sail.BitVec.updateSubrange iss 19 16 (Sail.BitVec.extractLsb instr 7 4))
              let iss : (BitVec 20) :=
                (Sail.BitVec.updateSubrange iss 13 10 (Sail.BitVec.extractLsb instr 19 16))
              let iss : (BitVec 20) :=
                (Sail.BitVec.updateSubrange iss 8 5 (Sail.BitVec.extractLsb instr 15 12))
              let iss : (BitVec 20) :=
                (Sail.BitVec.updateSubrange iss 4 1 (Sail.BitVec.extractLsb instr 3 0))
              (pure (iss)))
            else
              (do
                if ((BEq.beq except.exceptype Exception_CP14DTTrap) : Bool)
                then
                  (do
                    let iss : (BitVec 20) :=
                      (Sail.BitVec.updateSubrange iss 19 12 (Sail.BitVec.extractLsb instr 7 0))
                    let iss : (BitVec 20) :=
                      (BitVec.update iss 4
                        (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 23)]))))
                    let iss : (BitVec 20) :=
                      (Sail.BitVec.updateSubrange iss 2 1
                        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 24)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                              instr 21)]))))
                    if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb instr 19 16)) == 0b1111#4) : Bool)
                    then
                      (do
                        let w__8 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
                        let iss := ((Sail.BitVec.updateSubrange iss 8 5 w__8) : (BitVec 20))
                        let iss : (BitVec 20) := (BitVec.update iss 3 (Bit 1#1))
                        (pure (iss)))
                    else (pure (iss)))
                else (pure (iss)))) ) : SailM (BitVec 20) )
      let iss : (BitVec 20) :=
        (BitVec.update iss 0 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access instr 20)]))))
      let w__9 ← (( do (ConditionSyndrome ()) ) : SailM (BitVec 5) )
      let except :=
        ({ except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 24 20 w__9) } : ExceptionRecord)
      let except : ExceptionRecord :=
        { except with syndrome := (Sail.BitVec.updateSubrange except.syndrome 19 0 iss) }
      (pure (except)))


def decode_aarch32_instrs_SB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SETPAN_T1enc_A_txt (imm1 : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HavePANExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let value_name : (BitVec 1) := imm1
  (execute_aarch32_instrs_SETPAN_Op_A_txt value_name)


def decode_aarch32_instrs_TSB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (HaveSelfHostedTrace ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (EndOfInstruction ()))
      else (pure (()))
      let w__2 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__2 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (pure ((execute_aarch32_instrs_TSB_Op_A_txt ()))))
  else (pure (()))


def decode_aarch32_instrs_CSDB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_CSDB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_SSBB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_SSBB_Op_A_txt ()))
  else (pure (()))


def decode_aarch32_instrs_PSSBB_T1enc_A_txt (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (InITBlock ()) ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (pure ((execute_aarch32_instrs_PSSBB_Op_A_txt ()))))
  else (pure (()))


def GetNumEventCounters (_ : Unit) : SailM Int := do
  (__IMPDEF_integer "Number of event counters")


def IsSecureEL2Enabled (_ : Unit) : SailM Bool := do
  let w__1 ← (( do
    if (((HaveEL EL2) : Bool) : Bool)
    then
      (do
        (HaveSecureEL2Ext ()))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      if ((HaveEL EL3) : Bool)
      then
        (do
          let w__4 ← (( do
            if ((← do
                 let w__2 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                 (pure (((! w__2) : Bool)))) : Bool)
            then
              (do
                let w__3 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                (pure ((((_get_SCR_EL3_Type_EEL2 w__3) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          let w__5 : Bool :=
            if (w__4 : Bool)
            then true
            else false
          (pure (w__5)))
      else
        (do
          (SecureOnlyImplementation ())))
  else (pure (false))


end ArmFull.Functions
