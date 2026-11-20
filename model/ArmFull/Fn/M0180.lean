module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0155
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_ex10380617_ : Bool -/
def C27bReservedControl (ssc_in : (BitVec 2)) (ssce_in : (BitVec 1)) (hmc_in : (BitVec 1)) (pxc_in : (BitVec 2)) (isbreakpnt : Bool) : SailM Bool := SailME.run do
  let w__0 ← (( do (HaveRME ()) ) : SailME Bool Bool )
  if ((! w__0) : Bool)
  then
    (do
      if ((ssce_in != 0#1) : Bool)
      then
        (do
          SailME.throw (true : Bool))
      else (pure (())))
  else (pure (()))
  let reserved : Bool := false
  let ssc : (BitVec 2) := ssc_in
  let ssce : (BitVec 1) := ssce_in
  let hmc : (BitVec 1) := hmc_in
  let pxc : (BitVec 2) := pxc_in
  let reserved ← (( do
    match (BitVec.setWidth 6 (((hmc +++ ssce) +++ ssc) +++ pxc)) with
    | 0b001110 => (pure (true))
    | b__0 =>
      (do
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b001#3 : (BitVec 3))) : Bool)
        then
          (do
            let w__1 ← (( do (HaveSecureState ()) ) : SailME Bool Bool )
            let reserved := ((! w__1) : Bool)
            (pure (reserved)))
        else
          (let reserved : Bool :=
            if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 5 2)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
            then true
            else
              (match b__0 with
              | 0b100110 => true
              | b__0 =>
                (if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 5 3)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                then true
                else
                  (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (1#1 : (BitVec 1))) : Bool)
                  then
                    ((ssc != 0b01#2) || (((hmc +++ pxc) == 0b000#3) || ((hmc +++ pxc) == 0b110#3)))
                  else false)))
          (pure (reserved)))) ) : SailME Bool Bool )
  let w__5 ← (( do
    (pure (((← if ((! isbreakpnt) : Bool)
            then (pure true)
            else
              (do
                let w__2 ← (( do (HaveAArch32EL EL1) ) : SailME Bool Bool )
                (pure (((! w__2) : Bool))))) && (((hmc +++ pxc) == 0b000#3) : Bool)) && ((ssc != 0b11#2) : Bool)))
    ) : SailME Bool Bool )
  let reserved : Bool :=
    if (w__5 : Bool)
    then true
    else reserved
  let w__9 ← (( do
    (pure ((← do
          if ((← do
               let w__6 ← (( do (HaveEL EL3) ) : SailME Bool Bool )
               (pure (((! w__6) : Bool)))) : Bool)
          then
            (do
              let w__7 ← (( do (HaveEL EL2) ) : SailME Bool Bool )
              (pure (((! w__7) : Bool))))
          else (pure false)) && (((hmc != 0#1) || (ssc != 0b00#2)) : Bool))) ) : SailME Bool Bool )
  let reserved : Bool :=
    if (w__9 : Bool)
    then true
    else reserved
  let w__12 ← (( do
    (pure ((← do
          (pure ((← do
                let w__10 ← (( do (HaveEL EL3) ) : SailME Bool Bool )
                (pure (((! w__10) : Bool)))) && (((ssc == 0b01#2) || (ssc == 0b10#2)) : Bool)))) && ((((hmc +++ ssc) +++ pxc) != 0b10100#5) : Bool)))
    ) : SailME Bool Bool )
  let reserved : Bool :=
    if (w__12 : Bool)
    then true
    else reserved
  let w__16 ← (( do
    (pure ((← do
          if ((← do
               let w__13 ← (( do (HaveEL EL3) ) : SailME Bool Bool )
               (pure (((! w__13) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__14 ← (( do (HaveAArch64 ()) ) : SailME Bool Bool )
              (pure (((! w__14) : Bool))))) && ((((hmc +++ ssc) +++ pxc) == 0b11000#5) : Bool))) ) :
    SailME Bool Bool )
  let reserved : Bool :=
    if (w__16 : Bool)
    then true
    else reserved
  let w__18 ← (( do
    (pure ((← do
          let w__17 ← (( do (HaveEL EL2) ) : SailME Bool Bool )
          (pure (((! w__17) : Bool)))) && ((((hmc +++ ssc) +++ pxc) == 0b11100#5) : Bool))) ) :
    SailME Bool Bool )
  let reserved : Bool :=
    if (w__18 : Bool)
    then true
    else reserved
  let w__20 ← (( do
    (pure ((← do
          let w__19 ← (( do (HaveSecureEL2Ext ()) ) : SailME Bool Bool )
          (pure (((! w__19) : Bool)))) && (match (BitVec.setWidth 5 ((hmc +++ ssc) +++ pxc)) with
        | 0b01100 => true
        | 0b10100 => true
        | b__4 =>
          (if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__4 3 2)) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   b__4 0 0)) == (1#1 : (BitVec 1)))) : Bool)
          then true
          else false) : Bool))) ) : SailME Bool Bool )
  let reserved : Bool :=
    if (w__20 : Bool)
    then true
    else reserved
  (pure (reserved))


def ContextMatchingBreakpointRange (_ : Unit) : SailM (Int × Int) := do
  let b ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  let c ← (( do (NumContextAwareBreakpointsImplemented b) ) : SailM Int )
  (pure (if ((b ≤b 16) : Bool)
    then ((b -i c), (b -i 1))
    else
      (if ((c ≤b 16) : Bool)
      then ((16 -i c), 15)
      else (0, (c -i 1)))))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_BlocknTFaults (d128 : (BitVec 1)) (descriptor : (BitVec k_N)) : SailM Bool := do
  let w__0 ← (( do (HaveBlockBBM ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let nT ← (( do
        if ((d128 == 1#1) : Bool)
        then
          (do
            ArmFull.assert (6 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:24863.33-24863.34"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 6)])))))
        else
          (do
            ArmFull.assert (16 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:24866.34-24866.35"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 16)]))))) ) : SailM
        (BitVec 1) )
      let bbm_level ← (( do (AArch64_BlockBBMSupportLevel ()) ) : SailM Int )
      let nT_faults ← (( do
        (__IMPDEF_boolean "BBM level 1 or 2 support nT bit causes Translation Fault") ) : SailM Bool
        )
      (pure (((((bbm_level == 1) || (bbm_level == 2)) && (nT == 1#1)) && nT_faults))))


/-- Type quantifiers: level : Int -/
def AArch64_BlockDescSupported (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) (level : Int) : SailM Bool := SailME.run do
  let w__4 ← (( do
    match tgx with
    | .TGx_4KB =>
      (pure (((((level == 0) && ((ds == 1#1) || (d128 == 1#1))) || (level == 1)) || (level == 2))))
    | .TGx_16KB => (pure ((((level == 1) && ((ds == 1#1) || (d128 == 1#1))) || (level == 2))))
    | .TGx_64KB =>
      (do
        (pure ((← do
              if (((level == 1) : Bool) : Bool)
              then
                (do
                  if (((d128 == 1#1) : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__0 ← (( do (AArch64_PAMax ()) ) : SailME Bool Int )
                      (pure (((w__0 ≥b 52) : Bool)))))
              else (pure false)) || ((level == 2) : Bool)))) ) : SailME Bool Bool )
  SailME.throw (w__4 : Bool)
  (pure (false))


def AArch64_PhysicalAddressSize (d128 : (BitVec 1)) (encoded_ps : (BitVec 3)) (tgx : TGx) : SailM Int := do
  let ps : Int := 32
  let max_ps ← (( do (undefined_int_at (← occLabel 1478) ()) ) : SailM Int )
  let ps : Int :=
    match encoded_ps with
    | 0b000 => 32
    | 0b001 => 36
    | 0b010 => 40
    | 0b011 => 42
    | 0b100 => 44
    | 0b101 => 48
    | 0b110 => 52
    | _ => 56
  let ps : Int := ps
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do (Have56BitPAExt ()) ) : SailM Bool )
          (pure (((! w__0) : Bool)))) || ((d128 == 0#1) : Bool))) ) : SailM Bool )
  let max_ps ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__3 ← (( do
          if (((bne tgx TGx_64KB) : Bool) : Bool)
          then
            (do
              let w__2 ← (( do (Have52BitIPAAndPASpaceExt ()) ) : SailM Bool )
              (pure (((! w__2) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do (AArch64_PAMax ()) ) : SailM Int )
            let max_ps : Int := ((Min.min 48 w__4) : Int)
            (pure (max_ps)))
        else
          (do
            let w__5 ← (( do (Have52BitPAExt ()) ) : SailM Bool )
            if ((! w__5) : Bool)
            then
              (do
                let w__6 ← (( do (AArch64_PAMax ()) ) : SailM Int )
                let max_ps : Int := ((Min.min 48 w__6) : Int)
                (pure (max_ps)))
            else
              (do
                let w__7 ← (( do (AArch64_PAMax ()) ) : SailM Int )
                let max_ps : Int := ((Min.min 52 w__7) : Int)
                (pure (max_ps)))))
    else
      (do
        (AArch64_PAMax ())) ) : SailM Int )
  let max_ps : Int := max_ps
  (pure ((Min.min ps max_ps)))


def AArch64_S2DecodeTG0 (tg0_in : (BitVec 2)) : SailM TGx := do
  let tg0 : (BitVec 2) := tg0_in
  let tgx ← (( do (undefined_TGx (← occLabel 1502) ()) ) : SailM TGx )
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
  let w__1 ← (( do (AArch64_HaveS2TG tgx) ) : SailM Bool )
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


def AArch64_S2CheckPermissions (fault_in : FaultRecord) (walkstate : TTWState) (walkparams : S2TTWParams) (ipa : AddressDescriptor) (accdesc : AccessDescriptor) : SailM (FaultRecord × Bool) := do
  let memtype : MemType := walkstate.memattrs.memtype
  let permissions : Permissions := walkstate.permissions
  let fault : FaultRecord := fault_in
  let s2perms ← (( do (AArch64_S2ComputePermissions permissions walkparams accdesc) ) : SailM
    S2AccessControls )
  let r ← (( do (undefined_bitvector_at (← occLabel 1537) 1) ) : SailM (BitVec 1) )
  let w ← (( do (undefined_bitvector_at (← occLabel 1538) 1) ) : SailM (BitVec 1) )
  let or ← (( do (undefined_bitvector_at (← occLabel 1539) 1) ) : SailM (BitVec 1) )
  let ow ← (( do (undefined_bitvector_at (← occLabel 1540) 1) ) : SailM (BitVec 1) )
  let (or, ow, r, w) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
    if ((BEq.beq accdesc.acctype AccessType_TTW) : Bool)
    then
      (let r : (BitVec 1) := s2perms.r_mmu
      let w : (BitVec 1) := s2perms.w_mmu
      let or : (BitVec 1) := s2perms.or_mmu
      let ow : (BitVec 1) := s2perms.ow_mmu
      (or, ow, r, w))
    else
      (let (or, ow, r, w) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
        if (accdesc.rcw : Bool)
        then
          (let r : (BitVec 1) := s2perms.r_rcw
          let w : (BitVec 1) := s2perms.w_rcw
          let or : (BitVec 1) := s2perms.or_rcw
          let ow : (BitVec 1) := s2perms.ow_rcw
          (or, ow, r, w))
        else
          (let r : (BitVec 1) := s2perms.r
          let w : (BitVec 1) := s2perms.w
          let or : (BitVec 1) := s2perms.or
          let ow : (BitVec 1) := s2perms.ow
          (or, ow, r, w))
      (or, ow, r, w))
  let fault ← (( do
    if ((BEq.beq accdesc.acctype AccessType_TTW) : Bool)
    then
      (let fault : FaultRecord :=
        if (((accdesc.toplevel && (BEq.beq accdesc.varange VARange_LOWER)) && (((walkparams.tl0 == 1#1) && (s2perms.toplevel0 == 0#1)) || ((walkparams.tl1 == 1#1) && ((s2perms.toplevel1 +++ s2perms.toplevel0) == 0b10#2)))) : Bool)
        then
          (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
          { fault with toplevel := true })
        else
          (if (((accdesc.toplevel && (BEq.beq accdesc.varange VARange_UPPER)) && (((walkparams.tl1 == 1#1) && (s2perms.toplevel1 == 0#1)) || ((walkparams.tl0 == 1#1) && ((s2perms.toplevel1 +++ s2perms.toplevel0) == 0b01#2)))) : Bool)
          then
            (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
            { fault with toplevel := true })
          else
            (if (((walkparams.ptw == 1#1) && (BEq.beq memtype MemType_Device)) : Bool)
            then { fault with statuscode := Fault_Permission }
            else
              (if ((s2perms.overlay && (or == 0#1)) : Bool)
              then
                (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                { fault with overlay := true })
              else
                (if (((accdesc.write && s2perms.overlay) && (ow == 0#1)) : Bool)
                then
                  (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                  { fault with overlay := true })
                else
                  (if (((BEq.beq accdesc.ss SS_Realm) && (bne walkstate.baseaddress.paspace
                         PAS_Realm)) : Bool)
                  then { fault with statuscode := Fault_Permission }
                  else
                    (if ((r == 0#1) : Bool)
                    then { fault with statuscode := Fault_Permission }
                    else
                      (if ((accdesc.write && (w == 0#1)) : Bool)
                      then { fault with statuscode := Fault_Permission }
                      else
                        (if ((((accdesc.write && (! ((walkparams.ha +++ walkparams.hd) == 0b11#2))) && (walkparams.s2pie == 1#1)) && (permissions.s2dirty == 0#1)) : Bool)
                        then
                          (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                          { fault with dirtybit := true })
                        else fault))))))))
      (pure (fault)))
    else
      (do
        let w__6 ← (( do
          if ((((walkstate.s2assuredonly == 1#1) && (! ipa.s1assured)) : Bool) : Bool)
          then (pure true)
          else
            (do
              (pure ((← do
                    (pure ((← do
                          if ((← do
                               if (((walkstate.s2assuredonly != 1#1) : Bool) : Bool)
                               then
                                 (do
                                   (HaveGCS ()))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__2 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
                              (pure ((((_get_VTCR_EL2_Type_GCSH w__2) == 1#1) : Bool))))
                          else (pure false)) && ((BEq.beq accdesc.acctype AccessType_GCS) : Bool)))) && ((accdesc.el != EL0) : Bool))))
          ) : SailM Bool )
        if (w__6 : Bool)
        then
          (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
          let fault : FaultRecord := { fault with assuredonly := true }
          (pure (fault)))
        else
          (do
            if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
            then
              (do
                if ((s2perms.overlay && (s2perms.ox == 0#1)) : Bool)
                then
                  (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                  let fault : FaultRecord := { fault with overlay := true }
                  (pure (fault)))
                else
                  (do
                    let w__8 ← (( do
                      if (((BEq.beq memtype MemType_Device) : Bool) : Bool)
                      then
                        (do
                          let w__7 ← (( do (ConstrainUnpredictable Unpredictable_INSTRDEVICE) ) :
                            SailM Constraint )
                          (pure (((BEq.beq w__7 Constraint_FAULT) : Bool))))
                      else (pure false) ) : SailM Bool )
                    let fault : FaultRecord :=
                      if (w__8 : Bool)
                      then { fault with statuscode := Fault_Permission }
                      else
                        (if (((BEq.beq accdesc.ss SS_Realm) && (bne walkstate.baseaddress.paspace
                               PAS_Realm)) : Bool)
                        then { fault with statuscode := Fault_Permission }
                        else
                          (if ((s2perms.x == 0#1) : Bool)
                          then { fault with statuscode := Fault_Permission }
                          else fault))
                    (pure (fault))))
            else
              (do
                if ((BEq.beq accdesc.acctype AccessType_DC) : Bool)
                then
                  (do
                    if ((BEq.beq accdesc.cacheop CacheOp_Invalidate) : Bool)
                    then
                      (do
                        let w__11 ← (( do
                          (pure ((← do
                                (pure ((← do
                                      let w__9 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                      (pure (((! w__9) : Bool)))) && (s2perms.overlay : Bool)))) && ((ow == 0#1) : Bool)))
                          ) : SailM Bool )
                        let fault : FaultRecord :=
                          if (w__11 : Bool)
                          then
                            (let fault : FaultRecord :=
                              { fault with statuscode := Fault_Permission }
                            { fault with overlay := true })
                          else fault
                        let w__13 ← (( do
                          (pure ((← do
                                let w__12 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                                (pure (((! w__12) : Bool)))) && ((w == 0#1) : Bool))) ) : SailM Bool
                          )
                        let fault : FaultRecord :=
                          if (w__13 : Bool)
                          then { fault with statuscode := Fault_Permission }
                          else fault
                        (pure (fault)))
                    else
                      (do
                        let w__17 ← (( do
                          (pure ((← do
                                (pure ((← do
                                      (pure ((← do
                                            let w__14 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool
                                              )
                                            (pure (((! w__14) : Bool)))) && ((accdesc.el == EL0) : Bool)))) && (s2perms.overlay : Bool)))) && ((or == 0#1) : Bool)))
                          ) : SailM Bool )
                        if (w__17 : Bool)
                        then
                          (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                          let fault : FaultRecord := { fault with overlay := true }
                          (pure (fault)))
                        else
                          (do
                            if ((((((walkparams.cmow == 1#1) && (BEq.beq accdesc.opscope
                                         CacheOpScope_PoC)) && (BEq.beq accdesc.cacheop
                                       CacheOp_CleanInvalidate)) && s2perms.overlay) && (ow == 0#1)) : Bool)
                            then
                              (let fault : FaultRecord :=
                                { fault with statuscode := Fault_Permission }
                              let fault : FaultRecord := { fault with overlay := true }
                              (pure (fault)))
                            else
                              (do
                                let w__20 ← (( do
                                  (pure ((← do
                                        (pure ((← do
                                              let w__18 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                Bool )
                                              (pure (((! w__18) : Bool)))) && ((accdesc.el == EL0) : Bool)))) && ((r == 0#1) : Bool)))
                                  ) : SailM Bool )
                                let fault : FaultRecord :=
                                  if (w__20 : Bool)
                                  then { fault with statuscode := Fault_Permission }
                                  else
                                    (if (((((walkparams.cmow == 1#1) && (BEq.beq accdesc.opscope
                                               CacheOpScope_PoC)) && (BEq.beq accdesc.cacheop
                                             CacheOp_CleanInvalidate)) && (w == 0#1)) : Bool)
                                    then { fault with statuscode := Fault_Permission }
                                    else fault)
                                (pure (fault))))))
                else
                  (do
                    if ((BEq.beq accdesc.acctype AccessType_IC) : Bool)
                    then
                      (do
                        let w__26 ← (( do
                          if ((← do
                               (pure ((← do
                                     (pure ((← do
                                           (pure ((← do
                                                 let w__21 ← (( do (ELUsingAArch32 EL1) ) : SailM
                                                   Bool )
                                                 (pure (((! w__21) : Bool)))) && ((accdesc.el == EL0) : Bool)))) && (s2perms.overlay : Bool)))) && ((or == 0#1) : Bool)))) : Bool)
                          then
                            (do
                              (__IMPDEF_boolean "Permission fault on EL0 IC_IVAU execution"))
                          else (pure false) ) : SailM Bool )
                        if (w__26 : Bool)
                        then
                          (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                          let fault : FaultRecord := { fault with overlay := true }
                          (pure (fault)))
                        else
                          (do
                            if ((((walkparams.cmow == 1#1) && s2perms.overlay) && (ow == 0#1)) : Bool)
                            then
                              (let fault : FaultRecord :=
                                { fault with statuscode := Fault_Permission }
                              let fault : FaultRecord := { fault with overlay := true }
                              (pure (fault)))
                            else
                              (do
                                let w__31 ← (( do
                                  if ((← do
                                       (pure ((← do
                                             (pure ((← do
                                                   let w__27 ← (( do (ELUsingAArch32 EL1) ) :
                                                     SailM Bool )
                                                   (pure (((! w__27) : Bool)))) && ((accdesc.el == EL0) : Bool)))) && ((r == 0#1) : Bool)))) : Bool)
                                  then
                                    (do
                                      (__IMPDEF_boolean "Permission fault on EL0 IC_IVAU execution"))
                                  else (pure false) ) : SailM Bool )
                                let fault : FaultRecord :=
                                  if (w__31 : Bool)
                                  then { fault with statuscode := Fault_Permission }
                                  else
                                    (if (((walkparams.cmow == 1#1) && (w == 0#1)) : Bool)
                                    then { fault with statuscode := Fault_Permission }
                                    else fault)
                                (pure (fault)))))
                    else
                      (let fault : FaultRecord :=
                        if (((accdesc.read && s2perms.overlay) && (or == 0#1)) : Bool)
                        then
                          (let fault : FaultRecord := { fault with statuscode := Fault_Permission }
                          let fault : FaultRecord := { fault with overlay := true }
                          { fault with write := false })
                        else
                          (if (((accdesc.write && s2perms.overlay) && (ow == 0#1)) : Bool)
                          then
                            (let fault : FaultRecord :=
                              { fault with statuscode := Fault_Permission }
                            let fault : FaultRecord := { fault with overlay := true }
                            { fault with write := true })
                          else
                            (if ((accdesc.read && (r == 0#1)) : Bool)
                            then
                              (let fault : FaultRecord :=
                                { fault with statuscode := Fault_Permission }
                              { fault with write := false })
                            else
                              (if ((accdesc.write && (w == 0#1)) : Bool)
                              then
                                (let fault : FaultRecord :=
                                  { fault with statuscode := Fault_Permission }
                                { fault with write := true })
                              else
                                (if ((((accdesc.tagaccess || accdesc.tagchecked) && (BEq.beq
                                         ipa.memattrs.tags MemTag_AllocationTagged)) && (permissions.s2tag_na == 1#1)) : Bool)
                                then
                                  (let fault : FaultRecord :=
                                    { fault with statuscode := Fault_Permission }
                                  let fault : FaultRecord := { fault with tagaccess := true }
                                  { fault with write := (accdesc.tagaccess && accdesc.write) })
                                else
                                  (if ((((accdesc.write && (! ((walkparams.ha +++ walkparams.hd) == 0b11#2))) && (walkparams.s2pie == 1#1)) && (permissions.s2dirty == 0#1)) : Bool)
                                  then
                                    (let fault : FaultRecord :=
                                      { fault with statuscode := Fault_Permission }
                                    let fault : FaultRecord := { fault with dirtybit := true }
                                    { fault with write := true })
                                  else fault)))))
                      (pure (fault))))))) ) : SailM FaultRecord )
  let mro ← (( do (undefined_bool_at (← occLabel 1541) ()) ) : SailM Bool )
  let mro : Bool :=
    if (s2perms.overlay : Bool)
    then
      (((s2perms.w +++ (s2perms.w_rcw +++ s2perms.w_mmu)) &&& (s2perms.ow +++ (s2perms.ow_rcw +++ s2perms.ow_mmu))) == 0b011#3)
    else ((s2perms.w +++ (s2perms.w_rcw +++ s2perms.w_mmu)) == 0b011#3)
  (pure ((fault, mro)))


def AArch64_S2InvalidSL (walkparams : S2TTWParams) : SailM Bool := do
  match walkparams.tgx with
  | .TGx_4KB =>
    (do
      let b__0 := (walkparams.sl2 +++ walkparams.sl0)
      if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
      then (pure (true))
      else
        (do
          if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b11#2 : (BitVec 2))) : Bool)
          then (pure (true))
          else
            (do
              match b__0 with
              | 0b010 =>
                (do
                  let w__0 ← (( do (AArch64_PAMax ()) ) : SailM Int )
                  (pure ((w__0 <b 44))))
              | 0b011 =>
                (do
                  let w__1 ← (( do (HaveSmallTranslationTableExt ()) ) : SailM Bool )
                  (pure ((! w__1))))
              | _ => (pure (false)))))
  | .TGx_16KB =>
    (do
      match walkparams.sl0 with
      | 0b11 => (pure ((walkparams.ds == 0#1)))
      | 0b10 =>
        (do
          let w__5 ← (( do (AArch64_PAMax ()) ) : SailM Int )
          (pure ((w__5 <b 42))))
      | _ => (pure (false)))
  | .TGx_64KB =>
    (do
      match walkparams.sl0 with
      | 0b11 => (pure (true))
      | 0b10 =>
        (do
          let w__7 ← (( do (AArch64_PAMax ()) ) : SailM Int )
          (pure ((w__7 <b 44))))
      | _ => (pure (false)))


end ArmFull.Functions
