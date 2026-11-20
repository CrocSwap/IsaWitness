module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0150
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0166
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0174
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0180
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0190
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0215
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0237
public import ArmFull.Fn.M0240
public import ArmFull.Fn.M0245 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: lr_offset : Int, vect_offset : Int -/
def AArch32_EnterMode (target_mode : (BitVec 5)) (preferred_exception_return : (BitVec 32)) (lr_offset : Int) (vect_offset : Int) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL1)) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL != EL2) : Bool))))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:14067.49-14067.50"
  let w__3 ← (( do (Halted ()) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (AArch32_EnterModeInDebugState target_mode))
  else
    (do
      let spsr ← (( do (GetPSRFromPSTATE AArch32_NonDebugState 32) ) : SailM (BitVec 32) )
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__4.M == M32_Monitor) : Bool)
      then
        (do
          let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
          writeReg SCR (Sail.BitVec.updateSubrange w__5 0 0 0#1))
      else (pure (()))
      (AArch32_WriteMode target_mode)
      (SPSR_set (N := 32) spsr)
      (R_set 14 (BitVec.addInt preferred_exception_return lr_offset))
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__7 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__6 with T := (_get_SCTLR_Type_TE w__7) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with SS := 0#1 }
      if ((target_mode == M32_FIQ) : Bool)
      then
        (do
          let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__9 with A := (Sail.BitVec.extractLsb 0b111#3 2 2) }
          let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__10 with I := (Sail.BitVec.extractLsb 0b111#3 1 1) }
          let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__11 with F := (Sail.BitVec.extractLsb 0b111#3 0 0) })
      else
        (do
          if (((target_mode == M32_Abort) || (target_mode == M32_IRQ)) : Bool)
          then
            (do
              let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__12 with A := (Sail.BitVec.extractLsb 0b11#2 1 1) }
              let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__13 with I := (Sail.BitVec.extractLsb 0b11#2 0 0) })
          else
            (do
              let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__14 with I := 1#1 }))
      let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__16 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__15 with E := (_get_SCTLR_Type_EE w__16) }
      let w__17 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__17 with IL := 0#1 }
      let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__18 with IT := 0b00000000#8 }
      let w__21 ← (( do
        if ((← do
             (HavePANExt ())) : Bool)
        then
          (do
            let w__20 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
            (pure ((((_get_SCTLR_Type_SPAN w__20) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__21 : Bool)
      then
        (do
          let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__22 with PAN := 1#1 })
      else (pure (()))
      let w__23 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__23 : Bool)
      then
        (do
          let w__24 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__25 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
          writeReg PSTATE { w__24 with SSBS := (_get_SCTLR_Type_DSSBS w__25) })
      else (pure (()))
      let branch_conditional : Bool := false
      let w__26 ← (( do (ExcVectorBase ()) ) : SailM (BitVec 32) )
      (BranchTo ((Sail.BitVec.extractLsb w__26 31 5) +++ (integer_subrange vect_offset 4 0))
        BranchType_EXCEPTION branch_conditional)
      (CheckExceptionCatch true)
      (EndOfInstruction ()))


/-- Type quantifiers: lr_offset : Int, vect_offset : Int -/
def AArch32_EnterMonitorMode (preferred_exception_return : (BitVec 32)) (lr_offset : Int) (vect_offset : Int) : SailM Unit := do
  let _ : Unit := (SynchronizeContext ())
  let w__2 ← (( do
    if ((← do
         (HaveEL EL3)) : Bool)
    then
      (do
        (ELUsingAArch32 EL3))
    else (pure false) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:14146.44-14146.45"
  let w__3 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let from_secure : Bool := (BEq.beq w__3 SS_Secure)
  let w__4 ← (( do (Halted ()) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (AArch32_EnterMonitorModeInDebugState ()))
  else
    (do
      let spsr ← (( do (GetPSRFromPSTATE AArch32_NonDebugState 32) ) : SailM (BitVec 32) )
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__5.M == M32_Monitor) : Bool)
      then
        (do
          let w__6 ← (( do readReg SCR ) : SailM (BitVec 32) )
          writeReg SCR (Sail.BitVec.updateSubrange w__6 0 0 0#1))
      else (pure (()))
      (AArch32_WriteMode M32_Monitor)
      (SPSR_set (N := 32) spsr)
      (R_set 14 (BitVec.addInt preferred_exception_return lr_offset))
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__8 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__7 with T := (_get_SCTLR_Type_TE w__8) }
      let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__9 with SS := 0#1 }
      let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__10 with A := (Sail.BitVec.extractLsb 0b111#3 2 2) }
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__11 with I := (Sail.BitVec.extractLsb 0b111#3 1 1) }
      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__12 with F := (Sail.BitVec.extractLsb 0b111#3 0 0) }
      let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
      let w__14 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
      writeReg PSTATE { w__13 with E := (_get_SCTLR_Type_EE w__14) }
      let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__15 with IL := 0#1 }
      let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__16 with IT := 0b00000000#8 }
      let w__17 ← (( do (HavePANExt ()) ) : SailM Bool )
      if (w__17 : Bool)
      then
        (do
          if ((! from_secure) : Bool)
          then
            (do
              let w__18 ← (( do readReg PSTATE ) : SailM ProcState )
              writeReg PSTATE { w__18 with PAN := 0#1 })
          else
            (do
              let w__19 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
              if (((_get_SCTLR_Type_SPAN w__19) == 0#1) : Bool)
              then
                (do
                  let w__20 ← (( do readReg PSTATE ) : SailM ProcState )
                  writeReg PSTATE { w__20 with PAN := 1#1 })
              else (pure (()))))
      else (pure (()))
      let w__21 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__21 : Bool)
      then
        (do
          let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
          let w__23 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
          writeReg PSTATE { w__22 with SSBS := (_get_SCTLR_Type_DSSBS w__23) })
      else (pure (()))
      let branch_conditional : Bool := false
      let w__24 ← (( do readReg MVBAR ) : SailM (BitVec 32) )
      (BranchTo ((Sail.BitVec.extractLsb w__24 31 5) +++ (integer_subrange vect_offset 4 0))
        BranchType_EXCEPTION branch_conditional)
      (CheckExceptionCatch true)
      (EndOfInstruction ()))


/-- Type quantifiers: size : Int -/
def AArch64_CheckDebug (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) (size : Int) : SailM FaultRecord := do
  let mask ← (( do (undefined_bitvector_at (← occLabel 1403) 1) ) : SailM (BitVec 1) )
  let ss ← (( do (undefined_SecurityState (← occLabel 1404) ()) ) : SailM SecurityState )
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let generate_exception ← (( do (undefined_bool_at (← occLabel 1405) ()) ) : SailM Bool )
  let d_side : Bool := ((IsDataAccess accdesc.acctype) || (BEq.beq accdesc.acctype AccessType_DC))
  let i_side : Bool := (BEq.beq accdesc.acctype AccessType_IFETCH)
  let generate_exception ← (( do
    if ((BEq.beq accdesc.acctype AccessType_NV2) : Bool)
    then
      (do
        let mask : (BitVec 1) := 0#1
        let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        if ((← do
             (AArch64_GenerateDebugExceptionsFrom EL2 ss mask)) : Bool)
        then
          (do
            let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
            (pure ((((_get_MDSCR_EL1_Type_MDE w__1) == 1#1) : Bool))))
        else (pure false))
    else
      (do
        if ((← do
             (AArch64_GenerateDebugExceptions ())) : Bool)
        then
          (do
            let w__4 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
            (pure ((((_get_MDSCR_EL1_Type_MDE w__4) == 1#1) : Bool))))
        else (pure false)) ) : SailM Bool )
  let halt ← (( do (HaltOnBreakpointOrWatchpoint ()) ) : SailM Bool )
  if ((generate_exception || halt) : Bool)
  then
    (do
      if (d_side : Bool)
      then
        (do
          (AArch64_CheckWatchpoint fault vaddress accdesc size))
      else
        (do
          if (i_side : Bool)
          then
            (do
              (AArch64_CheckBreakpoint fault vaddress accdesc size))
          else (pure (fault))))
  else (pure (fault))


/-- Type quantifiers: N : Nat, List.elem N [32, 64, 128] -/
def AArch64_S2Walk (fault_in : FaultRecord) (ipa : AddressDescriptor) (walkparams : S2TTWParams) (accdesc : AccessDescriptor) (s1level : (Option Int)) (N : Nat) : SailM (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) := SailME.run do
  let fault : FaultRecord := fault_in
  let ipa_64 : (BitVec 64) := (Sail.BitVec.zeroExtend ipa.paddress.address 64)
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1574) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBContext )
  let tlbrecord ← (( do (undefined_TLBRecord (← occLabel 1575) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBRecord )
  let w__0 ← (( do readReg __tlb_enabled ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
  let (fault, tlbcontext, tlbrecord) ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (AArch64_GetS2TLBContext accdesc.ss ipa.paddress walkparams.tgx) ) :
          SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBContext )
        let tlbcontext := (w__1 : TLBContext)
        let tlbentry ← (( do (S2TLBLookup tlbcontext) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBLine )
        let tlbrecord : TLBRecord := tlbentry.tlbrecord
        let oa ← (( do (StageOA ipa_64 walkparams.d128 walkparams.tgx tlbrecord.walkstate) ) :
          SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FullAddress )
        let w__4 ← (( do
          (pure ((← do
                if ((tlbentry.valid_name : Bool) : Bool)
                then
                  (do
                    let w__2 ← (( do
                      (AArch64_OAOutOfRange oa.address walkparams.d128 walkparams.ps walkparams.tgx)
                      ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                    (pure (((! w__2) : Bool))))
                else (pure false)) && ((! ((((((walkparams.ha +++ walkparams.hd) == 0b11#2) && ((walkparams.s2pie == 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                tlbrecord.s2descriptor 51)])) == 1#1))) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                            tlbrecord.s2descriptor 7)])) == 0#1)) && accdesc.write) && (! ((BEq.beq
                        accdesc.acctype AccessType_AT) || ((BEq.beq accdesc.acctype AccessType_IC) || (BEq.beq
                          accdesc.acctype AccessType_DC)))))) : Bool))) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
        let (fault, tlbrecord) ← (( do
          if (w__4 : Bool)
          then
            (do
              let tlbrecord ← (( do
                if ((walkparams.fwb == 1#1) : Bool)
                then
                  (do
                    let w__5 ← (( do
                      (AArch64_S2ApplyFWBMemAttrs ipa.memattrs walkparams tlbrecord.s2descriptor) )
                      : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                      MemoryAttributes )
                    let tlbrecord :=
                      ({ tlbrecord with walkstate := { tlbrecord.walkstate with memattrs := w__5 } } : TLBRecord)
                    let tlbrecord : TLBRecord :=
                      if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             tlbrecord.s2descriptor 5 3)) == 0b111#3) : Bool)
                      then
                        { tlbrecord with walkstate := { tlbrecord.walkstate with permissions := { tlbrecord.walkstate.permissions with s2tag_na := 1#1 } } }
                      else
                        { tlbrecord with walkstate := { tlbrecord.walkstate with permissions := { tlbrecord.walkstate.permissions with s2tag_na := 0#1 } } }
                    (pure (tlbrecord)))
                else (pure (tlbrecord)) ) : SailME
                (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBRecord )
              let fault : FaultRecord := { fault with level := tlbrecord.walkstate.level }
              let w__6 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
              SailME.throw ((fault, w__6, tlbrecord.walkstate, (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                  tlbrecord.s2descriptor (Sail.Int.toNatChecked ((N -i 1))) 0))) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
              (pure ((fault, tlbrecord))))
          else (pure ((fault, tlbrecord))) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (FaultRecord × TLBRecord) )
        (pure ((fault, tlbcontext, tlbrecord))))
    else (pure ((fault, tlbcontext, tlbrecord))) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
    (FaultRecord × TLBContext × TLBRecord) )
  let walkstate ← (( do (undefined_TTWState (← occLabel 1576) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
  let walkstate ← (( do
    if ((BEq.beq accdesc.ss SS_Secure) : Bool)
    then
      (do
        (AArch64_SS2InitialTTWState walkparams ipa.paddress.paspace))
    else
      (do
        (AArch64_S2InitialTTWState accdesc.ss walkparams)) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
  let startlevel : Int := walkstate.level
  let descriptor ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1577)
      (Sail.Int.toNatChecked (N)))) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
  let walkaccess ← (( do (CreateAccDescS2TTW accdesc) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AccessDescriptor )
  let walkaddress ← (( do (undefined_AddressDescriptor (← occLabel 1578) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
  let skl : (BitVec 2) := 0b00#2
  let walkaddress : AddressDescriptor := { walkaddress with vaddress := ipa.vaddress }
  let w__9 ← (( do (AArch64_TTWalkMECID walkparams.emec Regime_EL10 accdesc.ss) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec 16) )
  let walkaddress := ({ walkaddress with mecid := w__9 } : AddressDescriptor)
  let w__10 ← (( do readReg HCR_EL2 ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec 64) )
  let walkaddress ← (( do
    if (((_get_HCR_EL2_Type_CD w__10) == 1#1) : Bool)
    then
      (do
        let w__11 ← (( do (NormalNCMemAttr ()) ) : SailME
          (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) MemoryAttributes )
        let walkaddress := ({ walkaddress with memattrs := w__11 } : AddressDescriptor)
        let walkaddress : AddressDescriptor :=
          { walkaddress with memattrs := { walkaddress.memattrs with xs := walkstate.memattrs.xs } }
        (pure (walkaddress)))
    else
      (let walkaddress : AddressDescriptor := { walkaddress with memattrs := walkstate.memattrs }
      (pure (walkaddress))) ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
    AddressDescriptor )
  let walkaddress : AddressDescriptor :=
    { walkaddress with memattrs := { walkaddress.memattrs with shareability := (EffectiveShareability
          walkaddress.memattrs) } }
  let walkaddress : AddressDescriptor := { walkaddress with tlbcontext := tlbcontext }
  let desctype ← (( do (undefined_DescriptorType (← occLabel 1579) ()) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) DescriptorType )
  let descaddress ← (( do
    (AArch64_S2SLTTEntryAddress walkparams ipa.paddress.address walkstate.baseaddress) ) : SailME
    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FullAddress )
  let w__12 ← (( do
    (AArch64_OAOutOfRange descaddress.address walkparams.d128 walkparams.ps walkparams.tgx) ) :
    SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
  if (w__12 : Bool)
  then
    (do
      let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
      let fault : FaultRecord := { fault with level := 0 }
      let w__13 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
      let w__14 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
      let w__15 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
      (pure ((fault, w__13, w__14, w__15))))
  else
    (do
      let (descaddress, descriptor, desctype, fault, skl, walkaddress, walkstate) ← (( do
        let loop_vars ← sailUntilFuelM (fuel := 1048576) (fun (descaddress, descriptor, desctype, fault, skl, walkaddress, walkstate) => (pure (BEq.beq
            desctype DescriptorType_Leaf))) (descaddress, descriptor, desctype, fault, skl, walkaddress, walkstate)
          fun (descaddress, descriptor, desctype, fault, skl, walkaddress, walkstate) => do
            let fault : FaultRecord := { fault with level := walkstate.level }
            let walkaddress : AddressDescriptor := { walkaddress with paddress := descaddress }
            let w__16 ← (( do (VMID_read ()) ) : SailME
              (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec 16) )
            let translation_info : TranslationInfo :=
              { regime := Regime_EL10
                vmid := (some w__16)
                asid := none
                va := walkaddress.vaddress
                s1level := s1level
                s2info := (some (ipa_64, walkstate.level))
                s1params := none
                s2params := (some walkparams)
                memattrs := walkaddress.memattrs }
            let w__17 ← (( do
              ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (FetchDescriptor walkparams.ee
                walkaddress walkaccess fault N translation_info)) ) : SailME
              (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
              (FaultRecord × (BitVec N)) )
            let (tup__0, tup__1) := (w__17 : (FaultRecord × (BitVec N)))
            let fault : FaultRecord := tup__0
            let descriptor : (BitVec N) := tup__1
            let (descaddress, descriptor, desctype, fault, skl, walkstate) ← (( do
              if ((bne fault.statuscode Fault_None) : Bool)
              then
                (do
                  let w__18 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) AddressDescriptor )
                  let w__19 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TTWState )
                  let w__20 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
                  SailME.throw ((fault, w__18, w__19, w__20) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                  (pure ((descaddress, descriptor, desctype, fault, skl, walkstate))))
              else
                (do
                  let new_descriptor ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1581)
                      (Sail.Int.toNatChecked (N)))) ) : SailME
                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) (BitVec N) )
                  let (descaddress, descriptor, desctype, fault, new_descriptor, skl, walkstate) ← (( do
                    let loop_vars_1 ← sailUntilFuelM (fuel := 1048576) (fun (descaddress, descriptor, desctype, fault, new_descriptor, skl, walkstate) => (pure (new_descriptor == descriptor))) (descaddress, descriptor, desctype, fault, new_descriptor, skl, walkstate)
                      fun (descaddress, descriptor, desctype, fault, new_descriptor, skl, walkstate) => do
                        let new_descriptor : (BitVec N) := descriptor
                        let w__21 ← (( do
                          (AArch64_DecodeDescriptorType descriptor walkparams.d128 walkparams.ds
                            walkparams.tgx walkstate.level) ) : SailME
                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                          DescriptorType )
                        let desctype := (w__21 : DescriptorType)
                        let (descaddress, fault, new_descriptor, skl, walkstate) ← (( do
                          match desctype with
                          | .DescriptorType_Table =>
                            (do
                              let w__22 ← (( do
                                (AArch64_S2NextWalkStateTable walkstate walkparams descriptor) ) :
                                SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                TTWState )
                              let walkstate := (w__22 : TTWState)
                              let w__23 ← (( do
                                if ((walkparams.d128 == 1#1) : Bool)
                                then
                                  (do
                                    ArmFull.assert (110 <b N) "sail-inputs/03-v8_base.sail:27125.49-27125.50"
                                    (pure ((Sail.BitVec.extractLsb descriptor 110 109))))
                                else (pure (0b00#2)) ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                (BitVec 2) )
                              let skl := (w__23 : (BitVec 2))
                              let w__24 ← (( do
                                (AArch64_TTEntryAddress walkstate.level walkparams.d128 skl
                                  walkparams.tgx walkparams.txsz ipa_64 walkstate.baseaddress) ) :
                                SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                FullAddress )
                              let descaddress := (w__24 : FullAddress)
                              let w__25 ← (( do
                                (AArch64_OAOutOfRange descaddress.address walkparams.d128
                                  walkparams.ps walkparams.tgx) ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                              let (fault, new_descriptor) ← (( do
                                if (w__25 : Bool)
                                then
                                  (do
                                    let fault : FaultRecord :=
                                      { fault with statuscode := Fault_AddressSize }
                                    let w__26 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                                      (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                      AddressDescriptor )
                                    let w__27 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                      (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                      TTWState )
                                    let w__28 ← (( do
                                      ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
                                      (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                      (BitVec N) )
                                    SailME.throw ((fault, w__26, w__27, w__28) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                                    (pure ((fault, new_descriptor))))
                                else
                                  (do
                                    let new_descriptor : (BitVec N) :=
                                      if ((walkparams.haft == 1#1) : Bool)
                                      then (BitVec.update new_descriptor 10 (Bit 1#1))
                                      else new_descriptor
                                    let w__30 ← (( do
                                      if ((((walkparams.d128 == 1#1) && (skl != 0b00#2)) : Bool) : Bool)
                                      then
                                        (do
                                          (AArch64_BlocknTFaults walkparams.d128 descriptor))
                                      else (pure false) ) : SailME
                                      (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                      Bool )
                                    let fault ← (( do
                                      if (w__30 : Bool)
                                      then
                                        (do
                                          let fault : FaultRecord :=
                                            { fault with statuscode := Fault_Translation }
                                          let w__31 ← (( do (__UNKNOWN_AddressDescriptor ()) ) :
                                            SailME
                                            (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                            AddressDescriptor )
                                          let w__32 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                            (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                            TTWState )
                                          let w__33 ← (( do
                                            ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) :
                                            SailME
                                            (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                            (BitVec N) )
                                          SailME.throw ((fault, w__31, w__32, w__33) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                                          (pure (fault)))
                                      else (pure (fault)) ) : SailME
                                      (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                      FaultRecord )
                                    (pure ((fault, new_descriptor)))) ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                (FaultRecord × (BitVec N)) )
                              (pure ((descaddress, fault, new_descriptor, skl, walkstate))))
                          | .DescriptorType_Leaf =>
                            (do
                              ArmFull.assert (52 <b N) "sail-inputs/03-v8_base.sail:27143.44-27143.45"
                              let w__34 ← (( do
                                (AArch64_S2NextWalkStateLeaf walkstate accdesc.ss walkparams ipa
                                  descriptor) ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                TTWState )
                              let walkstate := (w__34 : TTWState)
                              (pure ((descaddress, fault, new_descriptor, skl, walkstate))))
                          | .DescriptorType_Invalid =>
                            (do
                              let fault : FaultRecord :=
                                { fault with statuscode := Fault_Translation }
                              let w__35 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                AddressDescriptor )
                              let w__36 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                TTWState )
                              let w__37 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N))
                                ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                (BitVec N) )
                              SailME.throw ((fault, w__35, w__36, w__37) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N)))
                              (pure ((descaddress, fault, new_descriptor, skl, walkstate)))) ) :
                          SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                          (FullAddress × FaultRecord × (BitVec N) × (BitVec 2) × TTWState) )
                        let (descriptor, fault) ← (( do
                          if ((new_descriptor != descriptor) : Bool)
                          then
                            (do
                              let descaccess ← (( do (CreateAccDescTTEUpdate accdesc) ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                AccessDescriptor )
                              ArmFull.assert ((N == 64) || (N == 128)) "sail-inputs/03-v8_base.sail:27156.50-27156.51"
                              let w__38 ← (( do
                                (AArch64_MemSwapTableDesc fault descriptor new_descriptor
                                  walkparams.ee descaccess walkaddress translation_info) ) : SailME
                                (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                (FaultRecord × (BitVec N)) )
                              let (tup__0, tup__1) := (w__38 : (FaultRecord × (BitVec N)))
                              let fault : FaultRecord := tup__0
                              let descriptor : (BitVec N) := tup__1
                              if ((bne fault.statuscode Fault_None) : Bool)
                              then
                                (do
                                  let w__39 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    AddressDescriptor )
                                  let w__40 ← (( do (__UNKNOWN_TTWState ()) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    TTWState )
                                  let w__41 ← (( do
                                    ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
                                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                                    (BitVec N) )
                                  SailME.throw ((fault, w__39, w__40, w__41) : (FaultRecord × AddressDescriptor × TTWState × (BitVec N))))
                              else (pure (()))
                              (pure ((descriptor, fault))))
                          else (pure ((descriptor, fault))) ) : SailME
                          (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                          ((BitVec N) × FaultRecord) )
                        (pure ((descaddress, descriptor, desctype, fault, new_descriptor, skl, walkstate)))
                    (pure loop_vars_1) ) : SailME
                    (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
                    (FullAddress × (BitVec N) × DescriptorType × FaultRecord × (BitVec N) × (BitVec 2) × TTWState)
                    )
                  (pure ((descaddress, descriptor, desctype, fault, skl, walkstate)))) ) : SailME
              (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
              (FullAddress × (BitVec N) × DescriptorType × FaultRecord × (BitVec 2) × TTWState)
              )
            (pure ((descaddress, descriptor, desctype, fault, skl, walkaddress, walkstate)))
        (pure loop_vars) ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
        (FullAddress × (BitVec N) × DescriptorType × FaultRecord × (BitVec 2) × AddressDescriptor × TTWState)
        )
      let oa ← (( do (StageOA ipa_64 walkparams.d128 walkparams.tgx walkstate) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FullAddress )
      let w__43 ← (( do
        if (((walkstate.contiguous == 1#1) : Bool) : Bool)
        then
          (do
            (AArch64_ContiguousBitFaults walkparams.d128 walkparams.txsz walkparams.tgx
              walkstate.level))
        else (pure false) ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N))
        Bool )
      let fault ← (( do
        if (w__43 : Bool)
        then
          (let fault : FaultRecord := { fault with statuscode := Fault_Translation }
          (pure (fault)))
        else
          (do
            let w__45 ← (( do
              if ((((BEq.beq desctype DescriptorType_Leaf) && (walkstate.level <b FINAL_LEVEL)) : Bool) : Bool)
              then
                (do
                  (AArch64_BlocknTFaults walkparams.d128 descriptor))
              else (pure false) ) : SailME
              (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
            if (w__45 : Bool)
            then
              (let fault : FaultRecord := { fault with statuscode := Fault_Translation }
              (pure (fault)))
            else
              (do
                let w__46 ← (( do
                  (AArch64_OAOutOfRange oa.address walkparams.d128 walkparams.ps walkparams.tgx) ) :
                  SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                if (w__46 : Bool)
                then
                  (let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
                  (pure (fault)))
                else
                  (do
                    let w__49 ← (( do
                      if (((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 10)])) == 0#1) && (walkparams.ha == 0#1)) : Bool) : Bool)
                      then
                        (do
                          let w__48 ← (( do
                            if ((((BEq.beq accdesc.acctype AccessType_DC) || (BEq.beq
                                   accdesc.acctype AccessType_IC)) : Bool) : Bool)
                            then
                              (do
                                let w__47 ← (( do
                                  (__IMPDEF_boolean "Generate access flag fault on IC/DC operations")
                                  ) : SailME
                                  (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool
                                  )
                                (pure (((! w__47) : Bool))))
                            else (pure false) ) : SailME
                            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                          (pure (((! w__48) : Bool))))
                      else (pure false) ) : SailME
                      (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
                    let fault : FaultRecord :=
                      if (w__49 : Bool)
                      then { fault with statuscode := Fault_AccessFlag }
                      else fault
                    (pure (fault))))) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) FaultRecord )
      let w__52 ← (( do
        (pure ((← do
              (pure ((← do
                    readReg __tlb_enabled) && ((BEq.beq fault.statuscode Fault_None) : Bool)))) && (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                  descriptor 10)])) == 1#1) : Bool))) ) : SailME
        (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Bool )
      if (w__52 : Bool)
      then
        (do
          let tlbcontext : TLBContext := { tlbcontext with xs := walkstate.memattrs.xs }
          let tlbcontext : TLBContext := { tlbcontext with level := walkstate.level }
          let tlbcontext : TLBContext := { tlbcontext with isd128 := (walkparams.d128 == 1#1) }
          let tlbrecord : TLBRecord := { tlbrecord with context := tlbcontext }
          let tlbrecord : TLBRecord := { tlbrecord with walkstate := walkstate }
          let tlbrecord : TLBRecord :=
            { tlbrecord with blocksize := (TranslationSize walkparams.d128 walkparams.tgx
                walkstate.level) }
          let tlbrecord ← (( do
            if ((walkparams.d128 == 1#1) : Bool)
            then
              (do
                ArmFull.assert (127 <b N) "sail-inputs/03-v8_base.sail:27184.39-27184.40"
                let tlbrecord : TLBRecord :=
                  { tlbrecord with s2descriptor := (Sail.BitVec.extractLsb descriptor 127 0) }
                (pure (tlbrecord)))
            else
              (do
                ArmFull.assert (63 <b N) "sail-inputs/03-v8_base.sail:27187.38-27187.39"
                let tlbrecord : TLBRecord :=
                  { tlbrecord with s2descriptor := (Sail.BitVec.updateSubrange
                      tlbrecord.s2descriptor 63 0 (Sail.BitVec.extractLsb descriptor 63 0)) }
                let tlbrecord : TLBRecord :=
                  { tlbrecord with s2descriptor := (Sail.BitVec.updateSubrange
                      tlbrecord.s2descriptor 127 64 (Zeros (n := 64))) }
                (pure (tlbrecord))) ) : SailME
            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBRecord )
          let tlbrecord ← (( do
            if ((walkstate.contiguous == 1#1) : Bool)
            then
              (do
                let w__53 ← (( do (ContiguousSize walkparams.d128 walkparams.tgx walkstate.level)
                  ) : SailME (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) Int )
                let tlbrecord := ({ tlbrecord with contigsize := w__53 } : TLBRecord)
                (pure (tlbrecord)))
            else
              (let tlbrecord : TLBRecord := { tlbrecord with contigsize := 0 }
              (pure (tlbrecord))) ) : SailME
            (FaultRecord × AddressDescriptor × TTWState × (BitVec N)) TLBRecord )
          (pure ((S2TLBCache tlbrecord))))
      else (pure (()))
      (pure ((fault, walkaddress, walkstate, descriptor))))


end ArmFull.Functions
