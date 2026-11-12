import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0020
import ArmFull.Fn.M0024
import ArmFull.Fn.M0041
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0108
import ArmFull.Fn.M0113
import ArmFull.Fn.M0117
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0152
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155

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

def UsePrimarySpaceEL2 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  if (((_get_MPAM3_EL3_Type_ALTSP_HEN w__0) == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      (pure (((_get_MPAM3_EL3_Type_ALTSP_HFC w__1) == 0#1))))
  else
    (do
      if ((← do
           let w__2 ← (( do (MPAMisEnabled ()) ) : SailM Bool )
           (pure (((! w__2) : Bool)))) : Bool)
      then (pure true)
      else
        (do
          let w__3 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          (pure ((((_get_MPAM2_EL2_Type_ALTSP_EL2 w__3) == 0#1) : Bool)))))


def AdvSIMDExpandImm (op : (BitVec 1)) (cmode : (BitVec 4)) (imm8 : (BitVec 8)) : SailM (BitVec 64) := do
  let imm32 ← (( do (undefined_bitvector_at (← occLabel 827) 32) ) : SailM (BitVec 32) )
  let imm8a ← (( do (undefined_bitvector_at (← occLabel 828) 8) ) : SailM (BitVec 8) )
  let imm8b ← (( do (undefined_bitvector_at (← occLabel 829) 8) ) : SailM (BitVec 8) )
  let imm8c ← (( do (undefined_bitvector_at (← occLabel 830) 8) ) : SailM (BitVec 8) )
  let imm8d ← (( do (undefined_bitvector_at (← occLabel 831) 8) ) : SailM (BitVec 8) )
  let imm8e ← (( do (undefined_bitvector_at (← occLabel 832) 8) ) : SailM (BitVec 8) )
  let imm8f ← (( do (undefined_bitvector_at (← occLabel 833) 8) ) : SailM (BitVec 8) )
  let imm8g ← (( do (undefined_bitvector_at (← occLabel 834) 8) ) : SailM (BitVec 8) )
  let imm8h ← (( do (undefined_bitvector_at (← occLabel 835) 8) ) : SailM (BitVec 8) )
  let imm64 ← (( do (undefined_bitvector_at (← occLabel 836) 64) ) : SailM (BitVec 64) )
  match (BitVec.setWidth 3 (Sail.BitVec.extractLsb cmode 3 1)) with
  | 0b000 =>
    (let imm64 : (BitVec 64) := (BitVec.replicateBits ((Zeros (n := 24)) +++ imm8) 2)
    (pure (imm64)))
  | 0b001 =>
    (let imm64 : (BitVec 64) :=
      (BitVec.replicateBits (((Zeros (n := 16)) +++ imm8) +++ (Zeros (n := 8))) 2)
    (pure (imm64)))
  | 0b010 =>
    (let imm64 : (BitVec 64) :=
      (BitVec.replicateBits (((Zeros (n := 8)) +++ imm8) +++ (Zeros (n := 16))) 2)
    (pure (imm64)))
  | 0b011 =>
    (let imm64 : (BitVec 64) := (BitVec.replicateBits (imm8 +++ (Zeros (n := 24))) 2)
    (pure (imm64)))
  | 0b100 =>
    (let imm64 : (BitVec 64) := (BitVec.replicateBits ((Zeros (n := 8)) +++ imm8) 4)
    (pure (imm64)))
  | 0b101 =>
    (let imm64 : (BitVec 64) := (BitVec.replicateBits (imm8 +++ (Zeros (n := 8))) 4)
    (pure (imm64)))
  | 0b110 =>
    (let imm64 : (BitVec 64) :=
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 0#1) : Bool)
      then (BitVec.replicateBits (((Zeros (n := 16)) +++ imm8) +++ (Ones (n := 8))) 2)
      else (BitVec.replicateBits (((Zeros (n := 8)) +++ imm8) +++ (Ones (n := 16))) 2)
    (pure (imm64)))
  | _ =>
    (do
      let imm64 : (BitVec 64) :=
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 0#1) && (op == 0#1)) : Bool)
        then (BitVec.replicateBits imm8 8)
        else imm64
      let imm64 : (BitVec 64) :=
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 0#1) && (op == 1#1)) : Bool)
        then
          (let imm8a : (BitVec 8) :=
            (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 7)])) 8)
          let imm8b : (BitVec 8) :=
            (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])) 8)
          let imm8c : (BitVec 8) :=
            (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 5)])) 8)
          let imm8d : (BitVec 8) :=
            (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 4)])) 8)
          let imm8e : (BitVec 8) :=
            (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 3)])) 8)
          let imm8f : (BitVec 8) :=
            (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 2)])) 8)
          let imm8g : (BitVec 8) :=
            (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 1)])) 8)
          let imm8h : (BitVec 8) :=
            (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 0)])) 8)
          (((((((imm8a +++ imm8b) +++ imm8c) +++ imm8d) +++ imm8e) +++ imm8f) +++ imm8g) +++ imm8h))
        else imm64
      let imm64 : (BitVec 64) :=
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1) && (op == 0#1)) : Bool)
        then
          (let imm32 : (BitVec 32) :=
            (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 7)])) +++ (Complement.complement
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])))) +++ (BitVec.replicateBits
                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])) 5)) +++ (Sail.BitVec.extractLsb
                  imm8 5 0)) +++ (Zeros (n := 19)))
          (BitVec.replicateBits imm32 2))
        else imm64
      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access cmode 0)])) == 1#1) && (op == 1#1)) : Bool)
      then
        (do
          let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
          if (w__0 : Bool)
          then
            (do
              (ReservedEncoding ()))
          else (pure (()))
          let imm64 : (BitVec 64) :=
            (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 7)])) +++ (Complement.complement
                      (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])))) +++ (BitVec.replicateBits
                    (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)])) 8)) +++ (Sail.BitVec.extractLsb
                  imm8 5 0)) +++ (Zeros (n := 48)))
          (pure (imm64)))
      else (pure (imm64)))


/-- Type quantifiers: level : Int -/
def EncodeLDFSC (statuscode : Fault) (level : Int) : SailM (BitVec 6) := do
  let result ← (( do (undefined_bitvector_at (← occLabel 841) 6) ) : SailM (BitVec 6) )
  if ((level == (Neg.neg 2)) : Bool)
  then
    (do
      let w__0 ← (( do (Have56BitPAExt ()) ) : SailM Bool )
      ArmFull.assert w__0 "sail-arm/v8_base.sail:13478.31-13478.32"
      match statuscode with
      | .Fault_AddressSize => (pure (0b101100#6))
      | .Fault_Translation => (pure (0b101010#6))
      | .Fault_SyncExternalOnWalk => (pure (0b010010#6))
      | .Fault_SyncParityOnWalk =>
        (do
          let result : (BitVec 6) := 0b011010#6
          let w__1 ← (( do (HaveRASExt ()) ) : SailM Bool )
          ArmFull.assert (! w__1) "sail-arm/v8_base.sail:13491.43-13491.44"
          (pure (result)))
      | .Fault_GPCFOnWalk => (pure (0b100010#6))
      | _ =>
        (do
          (Unreachable ())
          (pure (result))))
  else
    (do
      if ((level == (Neg.neg 1)) : Bool)
      then
        (do
          let w__2 ← (( do (Have52BitIPAAndPASpaceExt ()) ) : SailM Bool )
          ArmFull.assert w__2 "sail-arm/v8_base.sail:13503.42-13503.43"
          match statuscode with
          | .Fault_AddressSize => (pure (0b101001#6))
          | .Fault_Translation => (pure (0b101011#6))
          | .Fault_SyncExternalOnWalk => (pure (0b010011#6))
          | .Fault_SyncParityOnWalk =>
            (do
              let result : (BitVec 6) := 0b011011#6
              let w__3 ← (( do (HaveRASExt ()) ) : SailM Bool )
              ArmFull.assert (! w__3) "sail-arm/v8_base.sail:13516.43-13516.44"
              (pure (result)))
          | .Fault_GPCFOnWalk => (pure (0b100011#6))
          | _ =>
            (do
              (Unreachable ())
              (pure (result))))
      else
        (do
          match statuscode with
          | .Fault_AddressSize =>
            (do
              let result : (BitVec 6) := (0b0000#4 +++ (integer_subrange level 1 0))
              ArmFull.assert ((level == 0) || ((level == 1) || ((level == 2) || (level == 3)))) "sail-arm/v8_base.sail:13530.66-13530.67"
              (pure (result)))
          | .Fault_AccessFlag =>
            (do
              let result : (BitVec 6) := (0b0010#4 +++ (integer_subrange level 1 0))
              ArmFull.assert ((level == 0) || ((level == 1) || ((level == 2) || (level == 3)))) "sail-arm/v8_base.sail:13534.66-13534.67"
              (pure (result)))
          | .Fault_Permission =>
            (do
              let result : (BitVec 6) := (0b0011#4 +++ (integer_subrange level 1 0))
              ArmFull.assert ((level == 0) || ((level == 1) || ((level == 2) || (level == 3)))) "sail-arm/v8_base.sail:13538.66-13538.67"
              (pure (result)))
          | .Fault_Translation =>
            (do
              let result : (BitVec 6) := (0b0001#4 +++ (integer_subrange level 1 0))
              ArmFull.assert ((level == 0) || ((level == 1) || ((level == 2) || (level == 3)))) "sail-arm/v8_base.sail:13542.66-13542.67"
              (pure (result)))
          | .Fault_SyncExternal => (pure (0b010000#6))
          | .Fault_SyncExternalOnWalk =>
            (do
              let result : (BitVec 6) := (0b0101#4 +++ (integer_subrange level 1 0))
              ArmFull.assert ((level == 0) || ((level == 1) || ((level == 2) || (level == 3)))) "sail-arm/v8_base.sail:13549.66-13549.67"
              (pure (result)))
          | .Fault_SyncParity => (pure (0b011000#6))
          | .Fault_SyncParityOnWalk =>
            (do
              let result : (BitVec 6) := (0b0111#4 +++ (integer_subrange level 1 0))
              ArmFull.assert ((level == 0) || ((level == 1) || ((level == 2) || (level == 3)))) "sail-arm/v8_base.sail:13556.66-13556.67"
              (pure (result)))
          | .Fault_AsyncParity => (pure (0b011001#6))
          | .Fault_AsyncExternal =>
            (do
              let result : (BitVec 6) := 0b010001#6
              let w__4 ← (( do (UsingAArch32 ()) ) : SailM Bool )
              ArmFull.assert w__4 "sail-arm/v8_base.sail:13563.31-13563.32"
              (pure (result)))
          | .Fault_TagCheck =>
            (do
              let result : (BitVec 6) := 0b010001#6
              let w__5 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
              ArmFull.assert w__5 "sail-arm/v8_base.sail:13567.30-13567.31"
              (pure (result)))
          | .Fault_Alignment => (pure (0b100001#6))
          | .Fault_Debug => (pure (0b100010#6))
          | .Fault_GPCFOnWalk =>
            (do
              let result : (BitVec 6) := (0b1001#4 +++ (integer_subrange level 1 0))
              ArmFull.assert ((level == 0) || ((level == 1) || ((level == 2) || (level == 3)))) "sail-arm/v8_base.sail:13577.66-13577.67"
              (pure (result)))
          | .Fault_GPCFOnOutput => (pure (0b101000#6))
          | .Fault_TLBConflict => (pure (0b110000#6))
          | .Fault_HWUpdateAccessFlag => (pure (0b110001#6))
          | .Fault_Lockdown => (pure (0b110100#6))
          | .Fault_Exclusive => (pure (0b110101#6))
          | _ =>
            (do
              (Unreachable ())
              (pure (result)))))


def NoFault (_ : Unit) : SailM FaultRecord := do
  let fault ← (( do (undefined_FaultRecord (← occLabel 884) ()) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := Fault_None }
  let w__0 ← (( do (__UNKNOWN_AccessDescriptor ()) ) : SailM AccessDescriptor )
  let fault := ({ fault with access := w__0 } : FaultRecord)
  let fault : FaultRecord := { fault with secondstage := false }
  let fault : FaultRecord := { fault with s2fs1walk := false }
  let fault : FaultRecord := { fault with dirtybit := false }
  let fault : FaultRecord := { fault with overlay := false }
  let fault : FaultRecord := { fault with toplevel := false }
  let fault : FaultRecord := { fault with assuredonly := false }
  let fault : FaultRecord := { fault with s1tagnotdata := false }
  let fault : FaultRecord := { fault with tagaccess := false }
  let fault : FaultRecord := { fault with gpcfs2walk := false }
  let w__1 ← (( do (GPCNoFault ()) ) : SailM GPCFRecord )
  let fault := ({ fault with gpcf := w__1 } : FaultRecord)
  (pure (fault))


def NoFault__1 (accdesc : AccessDescriptor) : SailM FaultRecord := do
  let fault ← (( do (undefined_FaultRecord (← occLabel 885) ()) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := Fault_None }
  let fault : FaultRecord := { fault with access := accdesc }
  let fault : FaultRecord := { fault with secondstage := false }
  let fault : FaultRecord := { fault with s2fs1walk := false }
  let fault : FaultRecord := { fault with dirtybit := false }
  let fault : FaultRecord := { fault with overlay := false }
  let fault : FaultRecord := { fault with toplevel := false }
  let fault : FaultRecord := { fault with assuredonly := false }
  let fault : FaultRecord := { fault with s1tagnotdata := false }
  let fault : FaultRecord := { fault with tagaccess := false }
  let fault : FaultRecord := { fault with write := ((! accdesc.read) && accdesc.write) }
  let fault : FaultRecord := { fault with gpcfs2walk := false }
  let w__0 ← (( do (GPCNoFault ()) ) : SailM GPCFRecord )
  let fault := ({ fault with gpcf := w__0 } : FaultRecord)
  (pure (fault))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPDefaultNaN__1 (fpcr : (BitVec 64)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:16128.38-16128.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let w__2 ← (( do
    if ((← do
         (HaveAltFP ())) : Bool)
    then
      (do
        let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let sign : (BitVec 1) :=
    if (w__2 : Bool)
    then (_get_FPCRType_AH fpcr)
    else 0#1
  let exp : (BitVec (Sail.Int.toNatChecked E)) := (Sail.BitVec.castWidth (Ones (n := E)))
  let frac : (BitVec (Sail.Int.toNatChecked (F : Int))) :=
    (Sail.BitVec.castWidth (1#1 +++ (Zeros (n := (Sail.Int.toNatChecked ((F -i 1)))))))
  (pure ((Sail.BitVec.castWidth ((sign +++ exp) +++ frac))))


/-- Type quantifiers: N : Nat, N ≥ 0 -/
def SPSR_read {N : _} : SailM (BitVec N) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1152)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (N == 32) "sail-arm/v8_base.sail:17954.22-17954.23"
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      let questionMark := w__1.M
      if ((questionMark == M32_FIQ) : Bool)
      then
        (do
          let w__2 ← (( do readReg SPSR_fiq ) : SailM (BitVec 64) )
          let result :=
            ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__2 (Sail.Int.toNatChecked ((N -i 1)))
              0)) : (BitVec N))
          (pure (result)))
      else
        (do
          if ((questionMark == M32_IRQ) : Bool)
          then
            (do
              let w__3 ← (( do readReg SPSR_irq ) : SailM (BitVec 64) )
              let result :=
                ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__3
                  (Sail.Int.toNatChecked ((N -i 1))) 0)) : (BitVec N))
              (pure (result)))
          else
            (do
              if ((questionMark == M32_Svc) : Bool)
              then
                (do
                  let w__4 ← (( do (SPSR_svc_read ()) ) : SailM (BitVec 32) )
                  let result :=
                    ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__4
                      (Sail.Int.toNatChecked ((N -i 1))) 0)) : (BitVec N))
                  (pure (result)))
              else
                (do
                  if ((questionMark == M32_Monitor) : Bool)
                  then
                    (do
                      let w__5 ← (( do readReg SPSR_mon ) : SailM (BitVec 32) )
                      let result :=
                        ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__5
                          (Sail.Int.toNatChecked ((N -i 1))) 0)) : (BitVec N))
                      (pure (result)))
                  else
                    (do
                      if ((questionMark == M32_Abort) : Bool)
                      then
                        (do
                          let w__6 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
                          let result :=
                            ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__6
                              (Sail.Int.toNatChecked ((N -i 1))) 0)) : (BitVec N))
                          (pure (result)))
                      else
                        (do
                          if ((questionMark == M32_Hyp) : Bool)
                          then
                            (do
                              let w__7 ← (( do (SPSR_hyp_read ()) ) : SailM (BitVec 32) )
                              let result :=
                                ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__7
                                  (Sail.Int.toNatChecked ((N -i 1))) 0)) : (BitVec N))
                              (pure (result)))
                          else
                            (do
                              if ((questionMark == M32_Undef) : Bool)
                              then
                                (do
                                  let w__8 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
                                  let result :=
                                    ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__8
                                      (Sail.Int.toNatChecked ((N -i 1))) 0)) : (BitVec N))
                                  (pure (result)))
                              else
                                (do
                                  (Unreachable ())
                                  (pure (result))))))))))
  else
    (do
      ArmFull.assert (N == 64) "sail-arm/v8_base.sail:17982.22-17982.23"
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      let questionMark := w__9.EL
      if ((questionMark == EL1) : Bool)
      then
        (do
          let w__10 ← (( do readReg SPSR_EL1 ) : SailM (BitVec 64) )
          let result :=
            ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__10 (Sail.Int.toNatChecked ((N -i 1)))
              0)) : (BitVec N))
          (pure (result)))
      else
        (do
          if ((questionMark == EL2) : Bool)
          then
            (do
              let w__11 ← (( do readReg SPSR_EL2 ) : SailM (BitVec 64) )
              let result :=
                ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__11
                  (Sail.Int.toNatChecked ((N -i 1))) 0)) : (BitVec N))
              (pure (result)))
          else
            (do
              if ((questionMark == EL3) : Bool)
              then
                (do
                  let w__12 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
                  let result :=
                    ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__12
                      (Sail.Int.toNatChecked ((N -i 1))) 0)) : (BitVec N))
                  (pure (result)))
              else
                (do
                  (Unreachable ())
                  (pure (result))))))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BranchToAddr (target : (BitVec k_N)) (branch_type : BranchType) : SailM Unit := do
  (Hint_Branch branch_type)
  if (((Sail.BitVec.length target) == 32) : Bool)
  then
    (do
      let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      ArmFull.assert w__0 "sail-arm/v8_base.sail:18006.29-18006.30"
      let _ : Unit := (sail_branch_announce 64 (ZeroExtend1 (m := 64) target))
      writeReg _PC (Sail.BitVec.zeroExtend target 64))
  else
    (do
      let w__2 ← (( do
        if ((((Sail.BitVec.length target) == 64) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
            (pure (((! w__1) : Bool))))
        else (pure false) ) : SailM Bool )
      ArmFull.assert w__2 "sail-arm/v8_base.sail:18010.50-18010.51"
      let _ : Unit := (sail_branch_announce 64 (Sail.BitVec.extractLsb target 63 0))
      writeReg _PC (Sail.BitVec.extractLsb target 63 0))
  writeReg __BranchTaken true


/-- Type quantifiers: k_ex10456163_ : Bool -/
def C27bMAIR (s1aarch64 : Bool) : SailM (BitVec 8) := do
  let allowed : (BitVec 256) := (Zeros (n := 256))
  let allowed ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 255
    (do
      let mut loop_vars := allowed
      for i in [loop_i_lower:loop_i_upper:1]i do
        let allowed := loop_vars
        loop_vars ← do
          let w__0 ← (( do (S1ConstrainUnpredictableRESMAIR (integer_subrange i 7 0) s1aarch64) )
            : SailM Bool )
          let allowed : (BitVec 256) :=
            if ((! w__0) : Bool)
            then (BitVec.update allowed (Sail.Int.toNatChecked (i)) 1#1)
            else allowed
          (pure (allowed))
      (pure loop_vars)) ) : SailM (BitVec 256) )
  let selected ← (( do (C27bSelect allowed) ) : SailM Int )
  (pure ((integer_subrange selected 7 0)))


/-- Type quantifiers: k_s2aarch64 : Bool -/
def S2CombineS1MemAttrs (s1_memattrs : MemoryAttributes) (s2_memattrs : MemoryAttributes) (s2aarch64 : Bool) : SailM MemoryAttributes := do
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1221) ()) ) : SailM
    MemoryAttributes )
  let memattrs ← (( do
    if (((BEq.beq s1_memattrs.memtype MemType_Device) && (BEq.beq s2_memattrs.memtype MemType_Device)) : Bool)
    then
      (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
      let memattrs : MemoryAttributes :=
        { memattrs with device := (S2CombineS1Device s1_memattrs.device s2_memattrs.device) }
      (pure (memattrs)))
    else
      (do
        if ((BEq.beq s1_memattrs.memtype MemType_Device) : Bool)
        then (pure (s1_memattrs))
        else
          (do
            if ((BEq.beq s2_memattrs.memtype MemType_Device) : Bool)
            then (pure (s2_memattrs))
            else
              (do
                let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
                let w__0 ← (( do (S2CombineS1AttrHints s1_memattrs.inner s2_memattrs.inner) ) :
                  SailM MemAttrHints )
                let memattrs := ({ memattrs with inner := w__0 } : MemoryAttributes)
                let w__1 ← (( do (S2CombineS1AttrHints s1_memattrs.outer s2_memattrs.outer) ) :
                  SailM MemAttrHints )
                let memattrs := ({ memattrs with outer := w__1 } : MemoryAttributes)
                (pure (memattrs))))) ) : SailM MemoryAttributes )
  let w__2 ← (( do (S2MemTagType memattrs s1_memattrs.tags) ) : SailM MemTagType )
  let memattrs := ({ memattrs with tags := w__2 } : MemoryAttributes)
  let w__3 ← (( do (HaveMTEPermExt ()) ) : SailM Bool )
  let memattrs : MemoryAttributes :=
    if ((! w__3) : Bool)
    then { memattrs with notagaccess := false }
    else
      { memattrs with notagaccess := (s2_memattrs.notagaccess && (BEq.beq s1_memattrs.tags
            MemTag_AllocationTagged)) }
  let memattrs : MemoryAttributes :=
    { memattrs with shareability := (S2CombineS1Shareability s1_memattrs.shareability
        s2_memattrs.shareability) }
  let memattrs : MemoryAttributes :=
    if ((((BEq.beq memattrs.memtype MemType_Normal) && (memattrs.inner.attrs == MemAttr_WB)) && (memattrs.outer.attrs == MemAttr_WB)) : Bool)
    then { memattrs with xs := 0#1 }
    else
      (if (s2aarch64 : Bool)
      then { memattrs with xs := (s2_memattrs.xs &&& s1_memattrs.xs) }
      else { memattrs with xs := s1_memattrs.xs })
  let memattrs : MemoryAttributes :=
    { memattrs with shareability := (EffectiveShareability memattrs) }
  (pure (memattrs))


def DecodeGPTBlock (pgs : PGSe) (entry : (BitVec 64)) : SailM (GPCF × GPTEntry) := do
  ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb entry 3 0)) == GPT_Block) "sail-arm/v8_base.sail:19559.37-19559.38"
  let result ← (( do (undefined_GPTEntry (← occLabel 1227) ()) ) : SailM GPTEntry )
  if ((! (IsZero (Sail.BitVec.extractLsb entry 63 8))) : Bool)
  then
    (do
      let w__0 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailM GPTEntry )
      (pure ((GPCF_Walk, w__0))))
  else
    (do
      let w__1 ← (( do (GPIValid (Sail.BitVec.extractLsb entry 7 4)) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          let w__2 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailM GPTEntry )
          (pure ((GPCF_Walk, w__2))))
      else
        (do
          let result : GPTEntry := { result with gpi := (Sail.BitVec.extractLsb entry 7 4) }
          let result : GPTEntry := { result with level := 0 }
          let result : GPTEntry :=
            match pgs with
            | .PGS_4KB => { result with size := GPTRange_4KB }
            | .PGS_16KB => { result with size := GPTRange_16KB }
            | .PGS_64KB => { result with size := GPTRange_64KB }
          let w__3 ← (( do (GPTL0Size ()) ) : SailM Int )
          let result := ({ result with contig_size := w__3 } : GPTEntry)
          (pure ((GPCF_None, result)))))


def DecodeGPTContiguous (pgs : PGSe) (entry : (BitVec 64)) : SailM (GPCF × GPTEntry) := SailME.run do
  ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb entry 3 0)) == GPT_Contig) "sail-arm/v8_base.sail:19590.38-19590.39"
  let result ← (( do (undefined_GPTEntry (← occLabel 1228) ()) ) : SailME (GPCF × GPTEntry)
    GPTEntry )
  if ((! (IsZero (Sail.BitVec.extractLsb entry 63 10))) : Bool)
  then (pure ((GPCF_Walk, result)))
  else
    (do
      let result : GPTEntry := { result with gpi := (Sail.BitVec.extractLsb entry 7 4) }
      let w__0 ← (( do (GPIValid result.gpi) ) : SailME (GPCF × GPTEntry) Bool )
      if ((! w__0) : Bool)
      then (pure ((GPCF_Walk, result)))
      else
        (do
          let result : GPTEntry :=
            match pgs with
            | .PGS_4KB => { result with size := GPTRange_4KB }
            | .PGS_16KB => { result with size := GPTRange_16KB }
            | .PGS_64KB => { result with size := GPTRange_64KB }
          let result ← (( do
            match (BitVec.setWidth 2 (Sail.BitVec.extractLsb entry 9 8)) with
            | 0b01 =>
              (let result : GPTEntry := { result with contig_size := GPTRange_2MB }
              (pure (result)))
            | 0b10 =>
              (let result : GPTEntry := { result with contig_size := GPTRange_32MB }
              (pure (result)))
            | 0b11 =>
              (let result : GPTEntry := { result with contig_size := GPTRange_512MB }
              (pure (result)))
            | _ =>
              (do
                let w__1 ← (( do (__UNKNOWN_GPTEntry ()) ) : SailME (GPCF × GPTEntry) GPTEntry )
                SailME.throw ((GPCF_Walk, w__1) : (GPCF × GPTEntry))
                (pure (result))) ) : SailME (GPCF × GPTEntry) GPTEntry )
          let result : GPTEntry := { result with level := 1 }
          (pure ((GPCF_None, result)))))


/-- Type quantifiers: index : Int -/
def DecodeGPTGranules (pgs : PGSe) (index : Int) (entry : (BitVec 64)) : SailM (GPCF × GPTEntry) := SailME.run do
  let result ← (( do (undefined_GPTEntry (← occLabel 1229) ()) ) : SailME (GPCF × GPTEntry)
    GPTEntry )
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 15
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let w__0 ← (( do (GPIValid (BitVec.slice entry (Sail.Int.toNatChecked ((i *i 4))) 4)) ) :
          SailME (GPCF × GPTEntry) Bool )
        if ((! w__0) : Bool)
        then
          (do
            SailME.throw ((GPCF_Walk, result) : (GPCF × GPTEntry)))
        else (pure (()))
    (pure loop_vars))
  let result : GPTEntry :=
    { result with gpi := (BitVec.slice entry (Sail.Int.toNatChecked ((index *i 4))) 4) }
  let result : GPTEntry :=
    match pgs with
    | .PGS_4KB => { result with size := GPTRange_4KB }
    | .PGS_16KB => { result with size := GPTRange_16KB }
    | .PGS_64KB => { result with size := GPTRange_64KB }
  let result : GPTEntry := { result with contig_size := result.size }
  let result : GPTEntry := { result with level := 1 }
  (pure ((GPCF_None, result)))


end ArmFull.Functions
