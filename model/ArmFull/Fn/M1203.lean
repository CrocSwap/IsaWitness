module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0099
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0149
public import ArmFull.Fn.M0172
public import ArmFull.Fn.M1145
public import ArmFull.Fn.M1146
public import ArmFull.Fn.M1147
public import ArmFull.Fn.M1148 set_option backward.proofsInPublic true @[expose] public section

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

def decode_aarch32_instrs_VSUB_f_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let elements ← (( do (undefined_int_at (← occLabel 3761) ()) ) : SailM Int )
      let regs ← (( do (undefined_int_at (← occLabel 3762) ()) ) : SailM Int )
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
             (pure ((((_get_FPSCR_Type_length w__1) != 0b000#3) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_FPSCR_Type_Stride w__2) != 0b00#2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__6 ← (( do
        if (((size == 0b00#2) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((size == 0b01#2) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
                (pure (((! w__4) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__6 : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let w__8 ← (( do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            (InITBlock ()))
        else (pure false) ) : SailM Bool )
      if (w__8 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      let regs : Int := regs
      let elements : Int := elements
      let advsimd : Bool := false
      let esize : Int := 16
      let d ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3763) 0 31))) ) :
        SailM Nat )
      let n ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3764) 0 31))) ) :
        SailM Nat )
      let m ← (( do
        ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3765) 0 31))) ) :
        SailM Nat )
      let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
        match size with
        | 0b01 =>
          (let esize : Int := 16
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b10 =>
          (let esize : Int := 32
          let d : Nat := (BitVec.toNat (Vd +++ D))
          let n : Nat := (BitVec.toNat (Vn +++ N))
          let m : Nat := (BitVec.toNat (Vm +++ M))
          (d, esize, m, n))
        | 0b11 =>
          (let esize : Int := 64
          let d : Nat := (BitVec.toNat (D +++ Vd))
          let n : Nat := (BitVec.toNat (N +++ Vn))
          let m : Nat := (BitVec.toNat (M +++ Vm))
          (d, esize, m, n))
        | _ => (d, esize, m, n)
      let n : Int := n
      let m : Int := m
      let esize : Int := esize
      let d : Int := d
      (execute_aarch32_instrs_VSUB_f_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
        (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) regs))
  else (pure (()))


def decode_aarch32_instrs_VMAXNM_A1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__1 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        (pure (((! w__0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let maximum : Bool := (op == 0#1)
  let advsimd : Bool := true
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match sz with
    | 0 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))
    regs)


def decode_aarch32_instrs_VMAXNM_A2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let elements ← (( do (undefined_int_at (← occLabel 3809) ()) ) : SailM Int )
  let regs ← (( do (undefined_int_at (← occLabel 3810) ()) ) : SailM Int )
  let w__2 ← (( do
    if (((size == 0b00#2) : Bool) : Bool)
    then (pure true)
    else
      (do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            let w__0 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let regs : Int := regs
  let elements : Int := elements
  let advsimd : Bool := false
  let maximum : Bool := (op == 0#1)
  let esize : Int := 16
  let d ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3811) 0 31))) ) :
    SailM Nat )
  let n ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3812) 0 31))) ) :
    SailM Nat )
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3813) 0 31))) ) :
    SailM Nat )
  let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b10 =>
      (let esize : Int := 32
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b11 =>
      (let esize : Int := 64
      let d : Nat := (BitVec.toNat (D +++ Vd))
      let n : Nat := (BitVec.toNat (N +++ Vn))
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (d, esize, m, n))
    | _ => (d, esize, m, n)
  let n : Int := n
  let m : Int := m
  let esize : Int := esize
  let d : Int := d
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))
    regs)


def decode_aarch32_instrs_VMAXNM_T1enc_A_txt (D : (BitVec 1)) (op : (BitVec 1)) (sz : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__2 ← (( do
    if (((sz == 1#1) : Bool) : Bool)
    then
      (do
        let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let maximum : Bool := (op == 0#1)
  let advsimd : Bool := true
  let esize : Int := 16
  let elements : Int := 2
  let (elements, esize) : (Int × Int) :=
    match sz with
    | 0 =>
      (let esize : Int := 32
      let elements : Int := 2
      (elements, esize))
    | _ =>
      (let esize : Int := 16
      let elements : Int := 4
      (elements, esize))
  let esize : Int := esize
  let elements : Int := elements
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))
    regs)


def decode_aarch32_instrs_VMAXNM_T2enc_A_txt (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (size : (BitVec 2)) (N : (BitVec 1)) (op : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let elements ← (( do (undefined_int_at (← occLabel 3814) ()) ) : SailM Int )
  let regs ← (( do (undefined_int_at (← occLabel 3815) ()) ) : SailM Int )
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__3 ← (( do
    if (((size == 0b00#2) : Bool) : Bool)
    then (pure true)
    else
      (do
        if (((size == 0b01#2) : Bool) : Bool)
        then
          (do
            let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
            (pure (((! w__1) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__3 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let regs : Int := regs
  let elements : Int := elements
  let advsimd : Bool := false
  let maximum : Bool := (op == 0#1)
  let esize : Int := 16
  let d ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3816) 0 31))) ) :
    SailM Nat )
  let n ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3817) 0 31))) ) :
    SailM Nat )
  let m ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 3818) 0 31))) ) :
    SailM Nat )
  let (d, esize, m, n) : (Nat × Int × Nat × Nat) :=
    match size with
    | 0b01 =>
      (let esize : Int := 16
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b10 =>
      (let esize : Int := 32
      let d : Nat := (BitVec.toNat (Vd +++ D))
      let n : Nat := (BitVec.toNat (Vn +++ N))
      let m : Nat := (BitVec.toNat (Vm +++ M))
      (d, esize, m, n))
    | 0b11 =>
      (let esize : Int := 64
      let d : Nat := (BitVec.toNat (D +++ Vd))
      let n : Nat := (BitVec.toNat (N +++ Vn))
      let m : Nat := (BitVec.toNat (M +++ Vm))
      (d, esize, m, n))
    | _ => (d, esize, m, n)
  let n : Int := n
  let m : Int := m
  let esize : Int := esize
  let d : Int := d
  (execute_aarch32_instrs_VMAXNM_Op_A_txt advsimd (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) maximum (Sail.Int.toNatChecked (n))
    regs)


def decode_aarch32_instrs_VCMLA_A1enc_A_txt (rot : (BitVec 2)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  let w__2 ← (( do
    (pure ((← do
          let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
          (pure (((! w__1) : Bool)))) && ((esize == 16) : Bool))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  ArmFull.assert ((esize == 16) || (esize == 32)) "sail-inputs/14-instrs32.sail:46581.41-46581.42"
  (execute_aarch32_instrs_VCMLA_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCMLA_T1enc_A_txt (rot : (BitVec 2)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  let w__3 ← (( do
    (pure ((← do
          let w__2 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
          (pure (((! w__2) : Bool)))) && ((esize == 16) : Bool))) ) : SailM Bool )
  if (w__3 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  ArmFull.assert ((esize == 16) || (esize == 32)) "sail-inputs/14-instrs32.sail:46620.41-46620.42"
  (execute_aarch32_instrs_VCMLA_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCMLA_idx_A1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (rot : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int :=
    if ((S == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat Vm)
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  let w__2 ← (( do
    (pure ((← do
          let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
          (pure (((! w__1) : Bool)))) && ((esize == 16) : Bool))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let index : Int :=
    if ((S == 1#1) : Bool)
    then 0
    else (BitVec.toNat M)
  ArmFull.assert ((0 ≤b m) && ((m ≤b 31) && ((esize == 16) || (esize == 32)))) "sail-inputs/14-instrs32.sail:46716.64-46716.65"
  (execute_aarch32_instrs_VCMLA_idx_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCMLA_idx_T1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (rot : (BitVec 2)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
               Vn 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int :=
    if ((S == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat Vm)
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  let w__3 ← (( do
    (pure ((← do
          let w__2 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
          (pure (((! w__2) : Bool)))) && ((esize == 16) : Bool))) ) : SailM Bool )
  if (w__3 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  let index : Int :=
    if ((S == 1#1) : Bool)
    then 0
    else (BitVec.toNat M)
  ArmFull.assert ((0 ≤b m) && ((m ≤b 31) && ((esize == 16) || (esize == 32)))) "sail-inputs/14-instrs32.sail:46756.64-46756.65"
  (execute_aarch32_instrs_VCMLA_idx_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (index)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCADD_A1enc_A_txt (rot : (BitVec 1)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  let w__2 ← (( do
    (pure ((← do
          let w__1 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
          (pure (((! w__1) : Bool)))) && ((esize == 16) : Bool))) ) : SailM Bool )
  if (w__2 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  ArmFull.assert ((esize == 16) || (esize == 32)) "sail-inputs/14-instrs32.sail:46829.41-46829.42"
  (execute_aarch32_instrs_VCADD_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VCADD_T1enc_A_txt (rot : (BitVec 1)) (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFCADDExt ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 Vn 0)])) == 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 0)])) == 1#1))) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int := (BitVec.toNat (N +++ Vn))
  let m : Int := (BitVec.toNat (M +++ Vm))
  let esize : Int := (Int.shiftl 16 (BitVec.toNat S))
  let w__3 ← (( do
    (pure ((← do
          let w__2 ← (( do (HaveFP16Ext ()) ) : SailM Bool )
          (pure (((! w__2) : Bool)))) && ((esize == 16) : Bool))) ) : SailM Bool )
  if (w__3 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let elements : Int := (fdiv_int 64 esize)
  let regs : Int :=
    if ((Q == 0#1) : Bool)
    then 1
    else 2
  ArmFull.assert ((esize == 16) || (esize == 32)) "sail-inputs/14-instrs32.sail:46868.41-46868.42"
  (execute_aarch32_instrs_VCADD_Op_A_txt (Sail.Int.toNatChecked (d)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) rot)


def decode_aarch32_instrs_VFMAL_A1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat (Vm +++ M))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && (m ≤b 31)))) "sail-inputs/14-instrs32.sail:46936.64-46936.65"
  (execute_aarch32_instrs_VFMAL_Op_A_txt Q (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) sub_op)


def decode_aarch32_instrs_VFMAL_T1enc_A_txt (S : (BitVec 1)) (D : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (InITBlock ()) ) : SailM Bool )
  if (w__0 : Bool)
  then sailThrow ((Error_Unpredictable ()))
  else (pure (()))
  let w__1 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__1) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ Vm))
    else (BitVec.toNat (Vm +++ M))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && (m ≤b 31)))) "sail-inputs/14-instrs32.sail:46972.64-46972.65"
  (execute_aarch32_instrs_VFMAL_Op_A_txt Q (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (regs)) sub_op)


def decode_aarch32_instrs_VFMAL_i_A1enc_A_txt (D : (BitVec 1)) (S : (BitVec 1)) (Vn : (BitVec 4)) (Vd : (BitVec 4)) (N : (BitVec 1)) (Q : (BitVec 1)) (M : (BitVec 1)) (Vm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFP16MulNoRoundingToFP32Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  if (((Q == 1#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vd 0)])) == 1#1)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let d : Int := (BitVec.toNat (D +++ Vd))
  let n : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (N +++ Vn))
    else (BitVec.toNat (Vn +++ N))
  let m : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (Sail.BitVec.extractLsb Vm 2 0))
    else (BitVec.toNat ((Sail.BitVec.extractLsb Vm 2 0) +++ M))
  let index : Int :=
    if ((Q == 1#1) : Bool)
    then (BitVec.toNat (M +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)]))))
    else (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Vm 3)])))
  let esize : Nat := 32
  let regs : Int :=
    if ((Q == 1#1) : Bool)
    then 2
    else 1
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (S == 1#1)
  ArmFull.assert ((0 ≤b n) && ((n ≤b 31) && ((0 ≤b m) && ((m ≤b 15) && ((((index == 0) || (index == 1)) || (index == 2)) || (index == 3)))))) "sail-inputs/14-instrs32.sail:47039.89-47039.90"
  (execute_aarch32_instrs_VFMAL_i_Op_A_txt Q (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) esize (Sail.Int.toNatChecked (index))
    (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) (Sail.Int.toNatChecked (regs)) sub_op)


end ArmFull.Functions
