module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0111
public import ArmFull.Fn.M0120
public import ArmFull.Fn.M0121
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0237
public import ArmFull.Fn.M0251
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0258
public import ArmFull.Fn.M1197 set_option backward.proofsInPublic true @[expose] public section

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
  ArmFull.assert (offset >b 0) "sail-inputs/03-v8_base.sail:28773.21-28773.22"
  ArmFull.assert ((N == 64) || (N == 128)) "sail-inputs/03-v8_base.sail:28774.29-28774.30"
  let w__0 ← (( do readReg VNCR_EL2 ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    (sign_extend ((_get_VNCR_EL2_Type_BADDR w__0) +++ (integer_subrange offset 11 0)) 64)
  let accdesc ← (( do (CreateAccDescNV2 MemOp_LOAD) ) : SailM AccessDescriptor )
  ((Sail.BitVec.castWidth ) <$> (Mem_read address (Sail.Int.toNatChecked ((Int.ediv N 8))) accdesc))


/-- Type quantifiers: N : Nat, offset : Int, List.elem N [64, 128] -/
def NVMem_set__1 (offset : Int) (N : Nat) (value_name : (BitVec N)) : SailM Unit := do
  ArmFull.assert (offset >b 0) "sail-inputs/03-v8_base.sail:28793.21-28793.22"
  ArmFull.assert ((N == 64) || (N == 128)) "sail-inputs/03-v8_base.sail:28794.29-28794.30"
  let w__0 ← (( do readReg VNCR_EL2 ) : SailM (BitVec 64) )
  let address : (BitVec 64) :=
    (sign_extend ((_get_VNCR_EL2_Type_BADDR w__0) +++ (integer_subrange offset 11 0)) 64)
  let accdesc ← (( do (CreateAccDescNV2 MemOp_STORE) ) : SailM AccessDescriptor )
  (Mem_set address (Sail.Int.toNatChecked ((Int.ediv N 8))) accdesc
    (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: k_M : Nat, k_N : Nat, k_esize : Nat, k_N ≥ 0 ∧ k_M ≥ 0 ∧ k_esize ≥ 0 -/
def ReducePredicated (op : ReduceOp) (input : (BitVec k_N)) (mask : (BitVec k_M)) (identity : (BitVec k_esize)) : SailM (BitVec k_esize) := do
  ArmFull.assert ((Sail.BitVec.length input) == ((Sail.BitVec.length mask) *i 8)) "sail-inputs/03-v8_base.sail:30881.23-30881.24"
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
              ArmFull.assert ((Sail.BitVec.length input) ≥b 0) "sail-inputs/03-v8_base.sail:30887.38-30887.39"
              ArmFull.assert ((Sail.BitVec.length identity) ≥b 0) "sail-inputs/03-v8_base.sail:30888.42-30888.43"
              ArmFull.assert (((e *i (Sail.BitVec.length identity)) ≤b (((e *i (Sail.BitVec.length
                          identity)) +i (Sail.BitVec.length identity)) -i 1)) || (! ((e ≥b 0) && (((e +i 1) *i (Sail.BitVec.length
                          identity)) ≤b (Sail.BitVec.length input))))) "sail-inputs/03-v8_base.sail:30889.135-30889.136"
              let w__2 ← (( do
                ((Sail.BitVec.castWidth ) <$> (Elem_read input e (Sail.BitVec.length identity))) ) :
                SailM (BitVec k_esize) )
              (Elem_set operand e (Sail.BitVec.length identity) (Sail.BitVec.castWidth w__2)))
          else
            (do
              ArmFull.assert (p2bits ≥b 0) "sail-inputs/03-v8_base.sail:30892.43-30892.44"
              ArmFull.assert ((Sail.BitVec.length identity) ≥b 0) "sail-inputs/03-v8_base.sail:30893.42-30893.43"
              ArmFull.assert (((e *i (Sail.BitVec.length identity)) ≤b (((e +i 1) *i (Sail.BitVec.length
                        identity)) -i 1)) || (! ((e ≥b 0) && (((e +i 1) *i (Sail.BitVec.length
                          identity)) ≤b p2bits)))) "sail-inputs/03-v8_base.sail:30894.137-30894.138"
              (Elem_set operand e (Sail.BitVec.length identity) (Sail.BitVec.castWidth identity)))
      (pure loop_vars)) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
  ArmFull.assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && ((((((Sail.BitVec.length
                  identity) == 8) || ((Sail.BitVec.length identity) == 16)) || ((Sail.BitVec.length
                identity) == 32)) || ((Sail.BitVec.length identity) == 64)) && (p2bits ≥b (Sail.BitVec.length
            identity)))) || (! ((Sail.BitVec.length input) == ((Sail.BitVec.length mask) *i 8)))) "sail-inputs/03-v8_base.sail:30898.143-30898.144"
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
                                  let w__57 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__55 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__55) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__57 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                                  else
                                    (do
                                      let w__61 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL3))
                                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__61 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeMonitorTrapException ()))
                                      else
                                        (do
                                          let w__65 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__63 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__63) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__65 : Bool)
                                          then
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x06#8)))
                                          else
                                            (do
                                              let w__66 ← (( do (DBGDTRRXint_read ()) ) : SailM
                                                (BitVec 32) )
                                              (MemA_set address 4 w__66)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__70 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__68 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__68) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__70 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
              else
                (do
                  let w__74 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__74 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__80 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__76 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__76) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__78 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__79 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__78) +++ (_get_MDCR_EL2_Type_TDA
                                    w__79)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__80 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                      else
                        (do
                          let w__86 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__84 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                let w__85 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                (pure (((((_get_HDCR_Type_TDE w__84) +++ (_get_HDCR_Type_TDA w__85)) != 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__86 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__90 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__88 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__88) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__90 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                              else
                                (do
                                  let w__94 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__94 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeMonitorTrapException ()))
                                  else
                                    (do
                                      let w__98 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__96 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__96) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__98 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                                      else
                                        (do
                                          let w__99 ← (( do (DBGDTRRXint_read ()) ) : SailM
                                            (BitVec 32) )
                                          (MemA_set address 4 w__99)))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__103 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__101 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__101) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__103 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__107 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__107 : Bool)
                      then
                        (do
                          (AArch32_TakeMonitorTrapException ()))
                      else
                        (do
                          let w__111 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__109 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__109) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__111 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__112 ← (( do (DBGDTRRXint_read ()) ) : SailM (BitVec 32) )
                              (MemA_set address 4 w__112)))))
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
                          let w__113 ← (( do (DBGDTRRXint_read ()) ) : SailM (BitVec 32) )
                          (MemA_set address 4 w__113)))
                  else (pure (()))))))


end ArmFull.Functions
