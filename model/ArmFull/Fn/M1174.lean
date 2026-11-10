import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0042
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0051
import ArmFull.Fn.M0082
import ArmFull.Fn.M0100
import ArmFull.Fn.M0111
import ArmFull.Fn.M0120
import ArmFull.Fn.M0121
import ArmFull.Fn.M0145
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0187
import ArmFull.Fn.M0238
import ArmFull.Fn.M0253
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255
import ArmFull.Fn.M0260
import ArmFull.Fn.M1142

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

/-- Type quantifiers: N : Nat, offset : Int, List.elem N [64, 128] -/
def NVMem_read__1 (offset : Int) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert (offset >b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:28763.21-28763.22"
  ArmFull.assert ((N == 64) || (N == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:28764.29-28764.30"
  let w__0 ← (( do readReg VNCR_EL2 ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    (sign_extend ((_get_VNCR_EL2_Type_BADDR w__0) +++ (integer_subrange offset 11 0)) 64)
  let accdesc ← (( do (CreateAccDescNV2 MemOp_LOAD) ) : SailM AccessDescriptor )
  ((Sail.BitVec.castWidth ) <$> (Mem_read address (Sail.Int.toNatChecked ((Int.ediv N 8))) accdesc))


/-- Type quantifiers: N : Nat, offset : Int, List.elem N [64, 128] -/
def NVMem_set__1 (offset : Int) (N : Nat) (value_name : (BitVec N)) : SailM Unit := do
  ArmFull.assert (offset >b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:28783.21-28783.22"
  ArmFull.assert ((N == 64) || (N == 128)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:28784.29-28784.30"
  let w__0 ← (( do readReg VNCR_EL2 ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    (sign_extend ((_get_VNCR_EL2_Type_BADDR w__0) +++ (integer_subrange offset 11 0)) 64)
  let accdesc ← (( do (CreateAccDescNV2 MemOp_STORE) ) : SailM AccessDescriptor )
  (Mem_set address (Sail.Int.toNatChecked ((Int.ediv N 8))) accdesc
    (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: k_M : Nat, k_N : Nat, k_esize : Nat, k_N ≥ 0 ∧ k_M ≥ 0 ∧ k_esize ≥ 0 -/
def ReducePredicated (op : ReduceOp) (input : (BitVec k_N)) (mask : (BitVec k_M)) (identity : (BitVec k_esize)) : SailM (BitVec k_esize) := do
  ArmFull.assert ((Sail.BitVec.length input) == ((Sail.BitVec.length mask) *i 8)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30871.23-30871.24"
  let p2bits ← (( do (CeilPow2 (Sail.BitVec.length input)) ) : SailM Nat )
  let operand ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1745)
      (Sail.Int.toNatChecked (p2bits)))) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
  let elements : Int := (fdiv_int p2bits (Sail.BitVec.length identity))
  let operand ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := operand
      for e in [loop_e_lower:loop_e_upper:1]i do
        let operand := loop_vars
        loop_vars ← do
          let w__1 ← (( do
            if ((((e *i (Sail.BitVec.length identity)) <b (Sail.BitVec.length input)) : Bool) : Bool)
            then
              (do
                (ActivePredicateElement mask e (Sail.BitVec.length identity)))
            else (pure false) ) : SailM Bool )
          if (w__1 : Bool)
          then
            (do
              ArmFull.assert ((Sail.BitVec.length input) ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30877.38-30877.39"
              ArmFull.assert ((Sail.BitVec.length identity) ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30878.42-30878.43"
              ArmFull.assert (((e *i (Sail.BitVec.length identity)) ≤b (((e *i (Sail.BitVec.length
                          identity)) +i (Sail.BitVec.length identity)) -i 1)) || (! ((e ≥b 0) && (((e +i 1) *i (Sail.BitVec.length
                          identity)) ≤b (Sail.BitVec.length input))))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30879.135-30879.136"
              let w__2 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_read input e (Sail.BitVec.length identity))) ) :
                SailM (BitVec k_esize) )
              (Elem_set operand e (Sail.BitVec.length identity) (Sail.BitVec.castWidth w__2)))
          else
            (do
              ArmFull.assert (p2bits ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30882.43-30882.44"
              ArmFull.assert ((Sail.BitVec.length identity) ≥b 0) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30883.42-30883.43"
              ArmFull.assert (((e *i (Sail.BitVec.length identity)) ≤b (((e +i 1) *i (Sail.BitVec.length
                        identity)) -i 1)) || (! ((e ≥b 0) && (((e +i 1) *i (Sail.BitVec.length
                          identity)) ≤b p2bits)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30884.137-30884.138"
              (Elem_set operand e (Sail.BitVec.length identity) (Sail.BitVec.castWidth identity)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
  ArmFull.assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && ((((((Sail.BitVec.length
                  identity) == 8) || ((Sail.BitVec.length identity) == 16)) || ((Sail.BitVec.length
                identity) == 32)) || ((Sail.BitVec.length identity) == 64)) && (p2bits ≥b (Sail.BitVec.length
            identity)))) || (! ((Sail.BitVec.length input) == ((Sail.BitVec.length mask) *i 8)))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:30888.143-30888.144"
  ((Sail.BitVec.castWidth ) <$> (Reduce op operand (Sail.BitVec.length identity)))


def AddGCSRecord (vaddress : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc ← (( do (CreateAccDescGCS w__0.EL MemOp_STORE) ) : SailM AccessDescriptor )
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  (Mem_set (BitVec.subInt ptr 8) 8 accdesc vaddress)
  let ptr : (BitVec 64) := (BitVec.subInt ptr 8)
  (SetCurrentGCSPointer ptr)


def AddGCSExRecord (elr : (BitVec 64)) (spsr : (BitVec 64)) (lr : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc ← (( do (CreateAccDescGCS w__0.EL MemOp_STORE) ) : SailM AccessDescriptor )
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  (Mem_set (BitVec.subInt ptr 8) 8 accdesc lr)
  (Mem_set (BitVec.subInt ptr 16) 8 accdesc spsr)
  (Mem_set (BitVec.subInt ptr 24) 8 accdesc elr)
  (Mem_set (BitVec.subInt ptr 32) 8 accdesc ((Zeros (n := 60)) +++ 0b1001#4))
  let ptr : (BitVec 64) := (BitVec.subInt ptr 32)
  (SetCurrentGCSPointer ptr)


def LoadCheckGCSRecord (vaddress : (BitVec 64)) (gcsinst_type : GCSInstruction) : SailM (BitVec 64) := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc ← (( do (CreateAccDescGCS w__0.EL MemOp_LOAD) ) : SailM AccessDescriptor )
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let recorded_va ← (( do (Mem_read ptr 8 accdesc) ) : SailM (BitVec 64) )
  let w__3 ← (( do
    (pure ((← do
          let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
          (GCSReturnValueCheckEnabled w__1.EL)) && ((recorded_va != vaddress) : Bool))) ) : SailM
    Bool )
  if (w__3 : Bool)
  then
    (do
      (GCSDataCheckException gcsinst_type))
  else (pure (()))
  (pure (recorded_va))


def CheckGCSExRecord (elr : (BitVec 64)) (spsr : (BitVec 64)) (lr : (BitVec 64)) (gcsinst_type : GCSInstruction) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc ← (( do (CreateAccDescGCS w__0.EL MemOp_LOAD) ) : SailM AccessDescriptor )
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let recorded_first_dword ← (( do (Mem_read ptr 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_first_dword != (Sail.BitVec.castWidth (m := 64) ((Zeros (n := 60)) +++ 0b1001#4))) : Bool)
  then
    (do
      (GCSDataCheckException gcsinst_type))
  else (pure (()))
  let recorded_elr ← (( do (Mem_read (BitVec.addInt ptr 8) 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_elr != elr) : Bool)
  then
    (do
      (GCSDataCheckException gcsinst_type))
  else (pure (()))
  let recorded_spsr ← (( do (Mem_read (BitVec.addInt ptr 16) 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_spsr != spsr) : Bool)
  then
    (do
      (GCSDataCheckException gcsinst_type))
  else (pure (()))
  let recorded_lr ← (( do (Mem_read (BitVec.addInt ptr 24) 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_lr != lr) : Bool)
  then
    (do
      (GCSDataCheckException gcsinst_type))
  else (pure (()))
  let ptr : (BitVec 64) := (BitVec.addInt ptr 32)
  (SetCurrentGCSPointer ptr)


def GCSSS2 (_ : Unit) : SailM (BitVec 64) := do
  let outgoing_pointer ← (( do (undefined_bitvector_at (← occLabel 1761) 64) ) : SailM
    (BitVec 64) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc_ld ← (( do (CreateAccDescGCS w__0.EL MemOp_LOAD) ) : SailM AccessDescriptor )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc_st ← (( do (CreateAccDescGCS w__1.EL MemOp_STORE) ) : SailM AccessDescriptor )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (GCSEnabled w__2.EL) ) : SailM Bool )
  if ((! w__3) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let incoming_pointer_name ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let outgoing_value ← (( do (Mem_read incoming_pointer_name 8 accdesc_ld) ) : SailM (BitVec 64) )
  if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb outgoing_value 2 0)) == 0b101#3) : Bool)
  then
    (do
      let outgoing_pointer : (BitVec 64) :=
        (Sail.BitVec.updateSubrange outgoing_pointer 63 3
          (BitVec.subInt (Sail.BitVec.extractLsb outgoing_value 63 3) 1))
      let outgoing_pointer : (BitVec 64) :=
        (Sail.BitVec.updateSubrange outgoing_pointer 2 0 0b000#3)
      let outgoing_value : (BitVec 64) :=
        ((Sail.BitVec.extractLsb outgoing_pointer 63 12) +++ 0b000000000001#12)
      (Mem_set outgoing_pointer 8 accdesc_st outgoing_value)
      (SetCurrentGCSPointer (BitVec.addInt incoming_pointer_name 8))
      (pure (let _ : Unit := (GCSSynchronizationBarrier ())
        outgoing_pointer)))
  else
    (do
      (GCSDataCheckException GCSInstType_SS2)
      (pure (outgoing_pointer)))


def GCSPOPM (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc ← (( do (CreateAccDescGCS w__0.EL MemOp_LOAD) ) : SailM AccessDescriptor )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (GCSEnabled w__1.EL) ) : SailM Bool )
  if ((! w__2) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let entry ← (( do (Mem_read ptr 8 accdesc) ) : SailM (BitVec 64) )
  if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb entry 1 0)) != 0b00#2) : Bool)
  then
    (do
      (GCSDataCheckException GCSInstType_POPM))
  else (pure (()))
  let ptr : (BitVec 64) := (BitVec.addInt ptr 8)
  (SetCurrentGCSPointer ptr)
  (pure (entry))


def GCSPOPX (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do (GCSEnabled w__0.EL) ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let accdesc ← (( do (CreateAccDescGCS w__2.EL MemOp_LOAD) ) : SailM AccessDescriptor )
  let ptr ← (( do (GetCurrentGCSPointer ()) ) : SailM (BitVec 64) )
  let recorded_first_dword ← (( do (Mem_read ptr 8 accdesc) ) : SailM (BitVec 64) )
  if ((recorded_first_dword != (Sail.BitVec.castWidth (m := 64) ((Zeros (n := 60)) +++ 0b1001#4))) : Bool)
  then
    (do
      (GCSDataCheckException GCSInstType_POPX))
  else (pure (()))
  let recorded_elr ← (( do (Mem_read (BitVec.addInt ptr 8) 8 accdesc) ) : SailM (BitVec 64) )
  let recorded_spsr ← (( do (Mem_read (BitVec.addInt ptr 16) 8 accdesc) ) : SailM (BitVec 64) )
  let recorded_lr ← (( do (Mem_read (BitVec.addInt ptr 24) 8 accdesc) ) : SailM (BitVec 64) )
  let ptr : (BitVec 64) := (BitVec.addInt ptr 32)
  (SetCurrentGCSPointer ptr)


def DBGDTRRXint_STC_521dc9133ebece9c (coproc : (BitVec 4)) (CRd : (BitVec 4)) (address : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_TDCC : (BitVec 1) := (_get_MDSCR_EL1_Type_TDCC w__1)
  let w__2 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  let __DBGDSCRext_UDCCdis : (BitVec 1) := (_get_DBGDSCRext_Type_UDCCdis w__2)
  let w__3 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDCC : (BitVec 1) := (_get_MDCR_EL2_Type_TDCC w__3)
  let w__4 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TDCC : (BitVec 1) := (_get_HDCR_Type_TDCC w__4)
  let w__5 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDCC : (BitVec 1) := (_get_MDCR_EL3_Type_TDCC w__5)
  let w__6 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  let __SDCR_TDCC : (BitVec 1) := (_get_SDCR_Type_TDCC w__6)
  let w__7 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__7)
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__8.M
  let w__9 ← (( do (Halted ()) ) : SailM Bool )
  if (w__9 : Bool)
  then
    (do
      let w__10 ← (( do (DBGDTRRXint_read ()) ) : SailM (BitVec 32) )
      (MemA_set address 4 w__10))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__12 ← (( do
            (pure ((← do
                  let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__11) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) ) : SailM
            Bool )
          if (w__12 : Bool)
          then
            (do
              let w__17 ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                         (pure (((! w__14) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_TGE w__16) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x06#8))))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__19 : Bool)
              then
                (do
                  let w__24 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__21) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__23) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__29 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__28 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_HCR_Type_TGE w__28) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__31 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__31) : Bool))))
                          else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                      else
                        (do
                          let w__45 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                     (pure (((! w__39) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                if ((← do
                                     let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure ((((_get_HCR_EL2_Type_TGE w__41) == 1#1) : Bool)))) : Bool)
                                then (pure true)
                                else
                                  (do
                                    let w__42 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                    let w__43 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_MDCR_EL2_Type_TDE w__42) +++ (_get_MDCR_EL2_Type_TDA
                                            w__43)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__45 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__53 ← (( do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         (ELUsingAArch32 EL2))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    if ((← do
                                         let w__49 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                         (pure ((((_get_HCR_Type_TGE w__49) == 1#1) : Bool)))) : Bool)
                                    then (pure true)
                                    else
                                      (do
                                        let w__50 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                        let w__51 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                        (pure (((((_get_HDCR_Type_TDE w__50) +++ (_get_HDCR_Type_TDA
                                                w__51)) != 0b00#2) : Bool)))))
                                else (pure false) ) : SailM Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                              else
                                (do
                                  let w__56 ← (( do
                                    (pure ((← do
                                          if (((HaveEL EL3) : Bool) : Bool)
                                          then
                                            (do
                                              let w__54 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__54) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__56 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                                  else
                                    (do
                                      let w__59 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL3))
                                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__59 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeMonitorTrapException ()))
                                      else
                                        (do
                                          let w__62 ← (( do
                                            (pure ((← do
                                                  if (((HaveEL EL3) : Bool) : Bool)
                                                  then
                                                    (do
                                                      let w__60 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__60) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__62 : Bool)
                                          then
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x06#8)))
                                          else
                                            (do
                                              let w__63 ← (( do (DBGDTRRXint_read ()) ) : SailM
                                                (BitVec 32) )
                                              (MemA_set address 4 w__63)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__67 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__65 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__65) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__67 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
              else
                (do
                  let w__71 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__71 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__77 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__73 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__73) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__75 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__76 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__75) +++ (_get_MDCR_EL2_Type_TDA
                                    w__76)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__77 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                      else
                        (do
                          let w__83 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__81 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                let w__82 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                (pure (((((_get_HDCR_Type_TDE w__81) +++ (_get_HDCR_Type_TDA w__82)) != 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__83 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__86 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__84 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__84) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__86 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                              else
                                (do
                                  let w__89 ← (( do
                                    (pure ((← do
                                          if (((HaveEL EL3) : Bool) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__89 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeMonitorTrapException ()))
                                  else
                                    (do
                                      let w__92 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__90 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__90) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__92 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                                      else
                                        (do
                                          let w__93 ← (( do (DBGDTRRXint_read ()) ) : SailM
                                            (BitVec 32) )
                                          (MemA_set address 4 w__93)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__96 ← (( do
                    (pure ((← do
                          if (((HaveEL EL3) : Bool) : Bool)
                          then
                            (do
                              let w__94 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__94) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__96 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__99 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__99 : Bool)
                      then
                        (do
                          (AArch32_TakeMonitorTrapException ()))
                      else
                        (do
                          let w__102 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__100 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__100) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__102 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__103 ← (( do (DBGDTRRXint_read ()) ) : SailM (BitVec 32) )
                              (MemA_set address 4 w__103)))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then
                        (do
                          (AArch32_TakeMonitorTrapException ()))
                      else
                        (do
                          let w__104 ← (( do (DBGDTRRXint_read ()) ) : SailM (BitVec 32) )
                          (MemA_set address 4 w__104)))
                  else (pure (()))))))


end ArmFull.Functions
