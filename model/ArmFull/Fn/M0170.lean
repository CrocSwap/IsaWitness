module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0012
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0039
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0062
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0150
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0156
public import ArmFull.Fn.M0158
public import ArmFull.Fn.M0159
public import ArmFull.Fn.M0166
public import ArmFull.Fn.M0167 set_option backward.proofsInPublic true @[expose] public section

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

def TLBIRange (regime : Regime) (Xt : (BitVec 64)) : SailM (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) := do
  let valid_name : Bool := true
  let start_address : (BitVec 64) := (Zeros (n := 64))
  let end_address_name : (BitVec 64) := (Zeros (n := 64))
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let tg_bits : Int := 12
  if ((tg == 0b00#2) : Bool)
  then (pure ((false, tg, start_address, end_address_name)))
  else
    (do
      let (start_address, tg_bits) ← (( do
        match tg with
        | 0b01 =>
          (do
            let tg_bits : Int := 12
            let w__0 ← (( do (HasLargeAddress regime) ) : SailM Bool )
            let start_address : (BitVec 64) :=
              if (w__0 : Bool)
              then
                (let start_address : (BitVec 64) :=
                  (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
                (Sail.BitVec.updateSubrange start_address 63 53
                  (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)]))
                    11)))
              else
                (let start_address : (BitVec 64) :=
                  (Sail.BitVec.updateSubrange start_address 48 12 (Sail.BitVec.extractLsb Xt 36 0))
                (Sail.BitVec.updateSubrange start_address 63 49
                  (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)]))
                    15)))
            (pure ((start_address, tg_bits))))
        | 0b10 =>
          (do
            let tg_bits : Int := 14
            let w__1 ← (( do (HasLargeAddress regime) ) : SailM Bool )
            let start_address : (BitVec 64) :=
              if (w__1 : Bool)
              then
                (let start_address : (BitVec 64) :=
                  (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
                (Sail.BitVec.updateSubrange start_address 63 53
                  (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)]))
                    11)))
              else
                (let start_address : (BitVec 64) :=
                  (Sail.BitVec.updateSubrange start_address 50 14 (Sail.BitVec.extractLsb Xt 36 0))
                (Sail.BitVec.updateSubrange start_address 63 51
                  (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)]))
                    13)))
            (pure ((start_address, tg_bits))))
        | 0b11 =>
          (let tg_bits : Int := 16
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 63 53
              (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)])) 11))
          (pure ((start_address, tg_bits))))
        | _ =>
          (do
            (Unreachable ())
            (pure ((start_address, tg_bits)))) ) : SailM ((BitVec 64) × Int) )
      let tg_bits : Int := tg_bits
      let range : Int :=
        (Int.shiftl (num +i 1) (Sail.Int.toNatChecked ((((5 *i scale) +i 1) +i tg_bits))))
      let end_address_name : (BitVec 64) :=
        (start_address + (Sail.BitVec.castWidth (m := 64) (integer_subrange range 63 0)))
      let end_address_name : (BitVec 64) :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access end_address_name 52)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 start_address 52)]))) : Bool)
        then
          ((BitVec.replicateBits
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access start_address 52)]))
              (Sail.Int.toNatChecked ((64 -i 52)))) +++ (Ones (n := 52)))
        else end_address_name
      (pure ((valid_name, tg, start_address, end_address_name))))


def AArch32_S1TTWParamsEL30 (va : (BitVec 32)) : SailM S1TTWParams := do
  let w__0 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
  ArmFull.assert ((_get_TTBCR_Type_EAE w__0) == 1#1) "sail-inputs/03-v8_base.sail:37254.30-37254.31"
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 2506) ()) ) : SailM S1TTWParams )
  let w__1 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with t0sz := (_get_TTBCR_Type_T0SZ w__1) } : S1TTWParams)
  let w__2 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with t1sz := (_get_TTBCR_Type_T1SZ w__2) } : S1TTWParams)
  let w__3 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_Type_EE w__3) } : S1TTWParams)
  let w__4 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_Type_WXN w__4) } : S1TTWParams)
  let w__5 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with uwxn := (_get_SCTLR_Type_UWXN w__5) } : S1TTWParams)
  let w__6 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
  let w__8 ← (( do
    if (w__6 : Bool)
    then
      (do
        let w__7 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
        (pure ((_get_SCTLR_Type_nTLSMD w__7))))
    else (pure (1#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ntlsmd := w__8 } : S1TTWParams)
  let w__9 ← (( do (MAIR1_S_read ()) ) : SailM (BitVec 32) )
  let w__10 ← (( do (MAIR0_S_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType (w__9 +++ w__10)) } : S1TTWParams)
  let w__11 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with sif := (_get_SCR_Type_SIF w__11) } : S1TTWParams)
  let varange ← (( do (AArch32_GetVARange va walkparams.t0sz walkparams.t1sz) ) : SailM VARange )
  if ((BEq.beq varange VARange_LOWER) : Bool)
  then
    (do
      let w__12 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with sh := (_get_TTBCR_Type_SH0 w__12) } : S1TTWParams)
      let w__13 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with irgn := (_get_TTBCR_Type_IRGN0 w__13) } : S1TTWParams)
      let w__14 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with orgn := (_get_TTBCR_Type_ORGN0 w__14) } : S1TTWParams)
      let w__15 ← (( do (AArch32_HaveHPDExt ()) ) : SailM Bool )
      let w__18 ← (( do
        if (w__15 : Bool)
        then
          (do
            let w__16 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
            let w__17 ← (( do readReg TTBCR2_S ) : SailM (BitVec 32) )
            (pure (((_get_TTBCR_Type_T2E w__16) &&& (_get_TTBCR2_Type_HPD0 w__17)))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let walkparams := ({ walkparams with hpd := w__18 } : S1TTWParams)
      (pure (walkparams)))
  else
    (do
      let w__19 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with sh := (_get_TTBCR_Type_SH1 w__19) } : S1TTWParams)
      let w__20 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with irgn := (_get_TTBCR_Type_IRGN1 w__20) } : S1TTWParams)
      let w__21 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with orgn := (_get_TTBCR_Type_ORGN1 w__21) } : S1TTWParams)
      let w__22 ← (( do (AArch32_HaveHPDExt ()) ) : SailM Bool )
      let w__25 ← (( do
        if (w__22 : Bool)
        then
          (do
            let w__23 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
            let w__24 ← (( do readReg TTBCR2_S ) : SailM (BitVec 32) )
            (pure (((_get_TTBCR_Type_T2E w__23) &&& (_get_TTBCR2_Type_HPD1 w__24)))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let walkparams := ({ walkparams with hpd := w__25 } : S1TTWParams)
      (pure (walkparams)))


def AArch32_TLBContextEL30 (va : (BitVec 32)) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 2533) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := SS_Secure }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL30 }
  let w__0 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
  let tlbcontext ← (( do
    if (((_get_TTBCR_Type_EAE w__0) == 1#1) : Bool)
    then
      (do
        let w__1 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
        let w__4 ← (( do
          if (((_get_TTBCR_Type_A1 w__1) == 0#1) : Bool)
          then
            (do
              let w__2 ← (( do readReg TTBR0_S ) : SailM (BitVec 64) )
              (pure ((_get_TTBR0_Type_ASID w__2))))
          else
            (do
              let w__3 ← (( do readReg TTBR1_S ) : SailM (BitVec 64) )
              (pure ((_get_TTBR1_Type_ASID w__3)))) ) : SailM (BitVec 8) )
        let tlbcontext :=
          ({ tlbcontext with asid := (Sail.BitVec.zeroExtend w__4 16) } : TLBContext)
        (pure (tlbcontext)))
    else
      (do
        let w__5 ← (( do readReg CONTEXTIDR_S ) : SailM (BitVec 32) )
        let tlbcontext :=
          ({ tlbcontext with asid := (Sail.BitVec.zeroExtend (_get_CONTEXTIDR_Type_ASID w__5) 16) } : TLBContext)
        (pure (tlbcontext))) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with tg := TGx_4KB }
  let tlbcontext : TLBContext := { tlbcontext with ia := (Sail.BitVec.zeroExtend va 64) }
  let w__8 ← (( do
    if ((← do
         (HaveCommonNotPrivateTransExt ())) : Bool)
    then
      (do
        let w__7 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
        (pure ((((_get_TTBCR_Type_EAE w__7) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__8 : Bool)
  then
    (do
      let w__9 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let w__10 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let w__11 ← (( do
        (AArch32_GetVARange va (_get_TTBCR_Type_T0SZ w__9) (_get_TTBCR_Type_T1SZ w__10)) ) : SailM
        VARange )
      if ((BEq.beq w__11 VARange_LOWER) : Bool)
      then
        (do
          let w__12 ← (( do readReg TTBR0_S ) : SailM (BitVec 64) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR0_Type_CnP w__12) } : TLBContext)
          (pure (tlbcontext)))
      else
        (do
          let w__13 ← (( do readReg TTBR1_S ) : SailM (BitVec 64) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR1_Type_CnP w__13) } : TLBContext)
          (pure (tlbcontext))))
  else
    (let tlbcontext : TLBContext := { tlbcontext with cnp := 0#1 }
    (pure (tlbcontext)))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV85 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap5_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV84 enabled))
  else (pure (()))


def A32ExpandImm (imm12 : (BitVec 12)) : SailM (BitVec 32) := do
  let imm32 ← (( do (undefined_bitvector_at (← occLabel 2699) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (__tup_0, _) ← (( do (A32ExpandImm_C imm12 w__0.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  (pure (__tup_0))


/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegReadCanWriteAPSR (cp_num : Int) (instr : (BitVec 32)) : SailM Bool := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-inputs/03-v8_base.sail:42713.25-42713.26"
  ArmFull.assert ((cp_num == 14) || (cp_num == 15)) "sail-inputs/03-v8_base.sail:42714.38-42714.39"
  ArmFull.assert (cp_num == (BitVec.toNat (Sail.BitVec.extractLsb instr 11 8))) "sail-inputs/03-v8_base.sail:42715.41-42715.42"
  let opc1 : Int := (BitVec.toNat (Sail.BitVec.extractLsb instr 23 21))
  let opc2 : Int := (BitVec.toNat (Sail.BitVec.extractLsb instr 7 5))
  let CRn : Int := (BitVec.toNat (Sail.BitVec.extractLsb instr 19 16))
  let CRm : Int := (BitVec.toNat (Sail.BitVec.extractLsb instr 3 0))
  (pure (if ((((((cp_num == 14) && (opc1 == 0)) && (CRn == 0)) && (CRm == 1)) && (opc2 == 0)) : Bool)
    then true
    else false))


def __set_MPAM1_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM1_EL1_Type := value_name
  let w__0 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 54 w__0 0 (BitVec.slice r 0 54))))
  let w__1 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 5 w__1 55 (BitVec.slice r 55 5))))
  let w__2 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 2 w__2 61 (BitVec.slice r 61 2))))
  let w__5 ← (( do
    if ((← do
         let w__3 ← (( do (HaveEL EL3) ) : SailM Bool )
         (pure (((! w__3) : Bool)))) : Bool)
    then
      (do
        let w__4 ← (( do (HaveEL EL2) ) : SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
      (MPAM1_EL1_write (_update_MPAM1_EL1_Type_MPAMEN w__6 (_get_MPAM1_EL1_Type_MPAMEN r))))
  else (pure (()))


/-- Type quantifiers: t : Int -/
def SCR_EL3_SysRegRead_b8dcdb7a98ef0967 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
                  let w__2 ← (( do (__get_SCR_EL3 w__1) ) : SailM (BitVec 64) )
                  (X_set t 64 w__2))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_PAALLOS_SysOpsWrite_b02935bd045e4472 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_TLBI_PAALL Shareability_OSH))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_PAALL_SysOpsWrite_30c81768c02bd90b (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  (AArch64_TLBI_PAALL Shareability_NSH))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RPALOS_SysOpsWrite_a11d11817d32a6eb (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RPA TLBILevel_Last w__1 Shareability_OSH))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def TLBI_RPAOS_SysOpsWrite_a15697b49d6ed58f (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__1 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_TLBI_RPA TLBILevel_Any w__1 Shareability_OSH))
              else (pure (())))))


def SetResetVector (value_name : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let w__1 ← (( do (HaveEL EL3) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          writeReg MVBAR (Mk_MVBAR_Type ((Sail.BitVec.extractLsb value_name 31 1) +++ 1#1)))
      else
        (do
          writeReg RVBAR ((Sail.BitVec.extractLsb value_name 31 1) +++ 1#1)))
  else
    (do
      let w__2 ← (( do (HighestEL ()) ) : SailM (BitVec 2) )
      if ((w__2 == EL3) : Bool)
      then
        (do
          writeReg RVBAR_EL3 (Mk_RVBAR_EL3_Type value_name))
      else
        (do
          let w__3 ← (( do (HighestEL ()) ) : SailM (BitVec 2) )
          if ((w__3 == EL2) : Bool)
          then
            (do
              writeReg RVBAR_EL2 (Mk_RVBAR_EL2_Type value_name))
          else
            (do
              writeReg RVBAR_EL1 (Mk_RVBAR_EL1_Type value_name))))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, k_setflags : Bool, shift_amount :
  Nat, k_sub_op : Bool, 0 ≤ shift_amount ∧
  shift_amount ≤ 63 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_shiftedreg (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (setflags : Bool) (shift_amount : Nat) (shift_type : ShiftType) (sub_op : Bool) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3918)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (ShiftReg m shift_type shift_amount datasize)) ) : SailM
    (BitVec datasize) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3919) 4) ) : SailM (BitVec 4) )
  let carry_in ← (( do (undefined_bitvector_at (← occLabel 3920) 1) ) : SailM (BitVec 1) )
  let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
    if (sub_op : Bool)
    then
      (let operand2 : (BitVec datasize) := (Complement.complement operand2)
      let carry_in : (BitVec 1) := 1#1
      (carry_in, operand2))
    else
      (let carry_in : (BitVec 1) := 0#1
      (carry_in, operand2))
  let (tup__0, tup__1) :=
    ((AddWithCarry operand1 operand2 carry_in) : ((BitVec datasize) × (BitVec 4)))
  let result : (BitVec datasize) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if (setflags : Bool)
  then
    (do
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, k_setflags : Bool, shift : Nat, k_sub_op
  : Bool, List.elem shift [0, 1, 2, 3, 4, 5, 6, 7] ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_add_sub_extendedreg (d : Nat) (datasize : Nat) (extend_type : ExtendType) (m : Nat) (n : Nat) (setflags : Bool) (shift : Nat) (sub_op : Bool) : SailM Unit := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3928)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        let w__0 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
        (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0
            (Sail.Int.toNatChecked ((datasize -i 1))) 0)))))
    else
      (do
        ((Sail.BitVec.castWidth ) <$> (X_read n datasize))) ) : SailM (BitVec datasize) )
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (ExtendReg m extend_type shift datasize)) ) :
    SailM (BitVec datasize) )
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 3929) 4) ) : SailM (BitVec 4) )
  let carry_in ← (( do (undefined_bitvector_at (← occLabel 3930) 1) ) : SailM (BitVec 1) )
  let (carry_in, operand2) : ((BitVec 1) × (BitVec datasize)) :=
    if (sub_op : Bool)
    then
      (let operand2 : (BitVec datasize) := (Complement.complement operand2)
      let carry_in : (BitVec 1) := 1#1
      (carry_in, operand2))
    else
      (let carry_in : (BitVec 1) := 0#1
      (carry_in, operand2))
  let (tup__0, tup__1) :=
    ((AddWithCarry operand1 operand2 carry_in) : ((BitVec datasize) × (BitVec 4)))
  let result : (BitVec datasize) := tup__0
  let nzcv : (BitVec 4) := tup__1
  if (setflags : Bool)
  then
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))
  if (((d == 31) && (! setflags)) : Bool)
  then
    (do
      (SP_set (Sail.BitVec.zeroExtend result 64)))
  else
    (do
      (X_set d datasize (Sail.BitVec.castWidth result)))


/-- Type quantifiers: d : Nat, datasize : Nat, k_invert : Bool, m : Nat, n : Nat, k_setflags : Bool, shift_amount
  : Nat, 0 ≤ shift_amount ∧
  shift_amount ≤ 63 ∧
  0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_logical_shiftedreg (d : Nat) (datasize : Nat) (invert : Bool) (m : Nat) (n : Nat) (op : LogicalOp) (setflags : Bool) (shift_amount : Nat) (shift_type : ShiftType) : SailM Unit := do
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let operand2 ← (( do
    ((Sail.BitVec.castWidth ) <$> (ShiftReg m shift_type shift_amount datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3957)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM (BitVec datasize) )
  let operand2 : (BitVec datasize) :=
    if (invert : Bool)
    then (Complement.complement operand2)
    else operand2
  let result : (BitVec datasize) :=
    match op with
    | .LogicalOp_AND => (operand1 &&& operand2)
    | .LogicalOp_ORR => (operand1 ||| operand2)
    | .LogicalOp_EOR => (operand1 ^^^ operand2)
  let result := result
  if (setflags : Bool)
  then
    (do
      let split_vec :=
        (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result
                (Sail.Int.toNatChecked ((datasize -i 1))))])) +++ (IsZeroBit result)) +++ 0b00#2)
      let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__0 with N := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with Z := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with C := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with V := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, m : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_shift_variable (d : Nat) (datasize : Nat) (m : Nat) (n : Nat) (shift_type : ShiftType) : SailM Unit := do
  let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read m datasize)) ) : SailM
    (BitVec datasize) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (ShiftReg n shift_type (Nat.mod (BitVec.toNat operand2) datasize)
      datasize)) ) : SailM (BitVec datasize) )
  (X_set d datasize (Sail.BitVec.castWidth result))


/-- Type quantifiers: d : Nat, datasize : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ List.elem datasize [32, 64] ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_arithmetic_cnt (d : Nat) (datasize : Nat) (n : Nat) (opcode : CountOp) : SailM Unit := do
  let result ← (( do (undefined_int_at (← occLabel 4031) ()) ) : SailM Int )
  let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (X_read n datasize)) ) : SailM
    (BitVec datasize) )
  let result : Int :=
    if ((BEq.beq opcode CountOp_CLZ) : Bool)
    then (CountLeadingZeroBits operand1)
    else (CountLeadingSignBits operand1)
  let result : Int := result
  (X_set d datasize (Sail.BitVec.castWidth (integer_subrange result (datasize -i 1) 0)))


def __UNKNOWN_AddressDescriptor (_ : Unit) : SailM AddressDescriptor := do
  (undefined_AddressDescriptor (← occLabel 388) ())


def __UNKNOWN_TLBLine (_ : Unit) : SailM TLBLine := do
  (undefined_TLBLine (← occLabel 468) ())


def __IMPDEF_boolean (x : String) : SailM Bool := do
  (ImpDefBool x)


def ImpDefInt (x : String) : SailM Int := do
  if ((x == "Number of breakpoints") : Bool)
  then
    (do
      (getNumBreakpoints ()))
  else
    (do
      if ((x == "Number of watchpoints") : Bool)
      then
        (do
          (getNumWatchpoints ()))
      else
        (do
          if ((x == "Number of event counters") : Bool)
          then
            (do
              readReg NUM_PMU_COUNTERS)
          else
            (do
              if ((x == "Number of context-aware breakpoints") : Bool)
              then
                (do
                  (getNumCtxBreakpoints ()))
              else
                (do
                  if ((x == "Max implemented VL") : Bool)
                  then
                    (do
                      readReg __max_implemented_sveveclen)
                  else
                    (do
                      if ((x == "Maximum bytes used in a single block of a copy") : Bool)
                      then (pure (1))
                      else
                        (do
                          if ((x == "Number of BRB records") : Bool)
                          then
                            (do
                              readReg NUM_BRBE_RECORDS)
                          else
                            (do
                              if ((x == "SPE Events packet payload size") : Bool)
                              then (pure (4))
                              else
                                (do
                                  if ((x == "SPE Data Source packet payload size") : Bool)
                                  then (pure (2))
                                  else
                                    (do
                                      if ((x == "Reserved Intermediate Physical Address size value") : Bool)
                                      then (pure (52))
                                      else
                                        (do
                                          if ((x == "Maximum Physical Address Size") : Bool)
                                          then
                                            (do
                                              readReg __supported_pa_size)
                                          else
                                            (do
                                              if ((x == "Block BBM support level") : Bool)
                                              then
                                                (do
                                                  readReg __block_bbm_implemented)
                                              else
                                                (do
                                                  if ((x == "SVE Extended BFloat16 instructions are implemented") : Bool)
                                                  then
                                                    (do
                                                      readReg __has_sve_extended_bf16)
                                                  else
                                                    (do
                                                      if ((x == "Max implemented SVL") : Bool)
                                                      then
                                                        (do
                                                          readReg __max_implemented_smeveclen)
                                                      else
                                                        (do
                                                          if ((x == "Data Cache Invalidate Watchpoint Size") : Bool)
                                                          then
                                                            (do
                                                              let w__10 ← (( do readReg CTR_EL0 )
                                                                : SailM (BitVec 64) )
                                                              (pure ((4 *i (2 ^i (BitVec.toNat
                                                                      (_get_CTR_EL0_Type_DminLine
                                                                        w__10)))))))
                                                          else
                                                            (do
                                                              if ((x == "Instruction Cache Invalidate by VA Size") : Bool)
                                                              then
                                                                (do
                                                                  let w__11 ← (( do
                                                                    readReg CTR_EL0 ) : SailM
                                                                    (BitVec 64) )
                                                                  (pure ((4 *i (2 ^i (BitVec.toNat
                                                                          (_get_CTR_EL0_Type_DminLine
                                                                            w__11)))))))
                                                              else
                                                                (do
                                                                  if ((x == "Linesize for DC SW instructions") : Bool)
                                                                  then
                                                                    (do
                                                                      let w__12 ← (( do
                                                                        readReg CTR_EL0 ) : SailM
                                                                        (BitVec 64) )
                                                                      (pure ((4 *i (2 ^i (BitVec.toNat
                                                                              (_get_CTR_EL0_Type_DminLine
                                                                                w__12)))))))
                                                                  else
                                                                    (do
                                                                      if ((x == "Associativity for DC SW instructions") : Bool)
                                                                      then (pure (2))
                                                                      else
                                                                        (do
                                                                          if ((x == "Numsets for DC SW instructions") : Bool)
                                                                          then (pure (2))
                                                                          else
                                                                            (do
                                                                              let _ : Unit :=
                                                                                (print_endline
                                                                                  (String.append x
                                                                                    " is an unrecognized Implementation defined bit."))
                                                                              ArmFull.assert false "sail-inputs/09-impdefs.sail:746.20-746.21"
                                                                              throw Error.Exit)))))))))))))))))))


end ArmFull.Functions
