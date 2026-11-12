import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0050
import ArmFull.Fn.M0116
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0147
import ArmFull.Fn.M0152
import ArmFull.Fn.M0156
import ArmFull.Fn.M0157
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180

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


def MaxBlockSizeCopiedBytes (_ : Unit) : SailM Nat := do
  let nbytes ← (( do (__IMPDEF_integer "Maximum bytes used in a single block of a copy") ) : SailM
    Int )
  ArmFull.assert (nbytes ≥b 0) "sail-arm/v8_base.sail:31968.22-31968.23"
  (pure ((Sail.Int.toNatChecked (nbytes))))


/-- Type quantifiers: k_N : Nat, k_N = 16 -/
def BFMulH (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec (2 * k_N)) := do
  let inf1 ← (( do (undefined_bool_at (← occLabel 1772) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1773) ()) ) : SailM Bool )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1774) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1775) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1776) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1777) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1778) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1779) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1780) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1781) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length op2) == 16) "sail-arm/v8_base.sail:32106.19-32106.20"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1782)
      (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))) ) : SailM (BitVec (2 * k_N)) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let w__0 ← (( do (BFUnpack op1) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (BFUnpack op2) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  if (((BEq.beq type1 FPType_QNaN) || (BEq.beq type2 FPType_QNaN)) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr
        (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
  else
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr
            (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
      else
        (do
          if ((inf1 || inf2) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity (sign1 ^^^ sign2)
                (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
          else
            (do
              if ((zero1 || zero2) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPZero (sign1 ^^^ sign2)
                    (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2)))))))
              else
                (do
                  ((Sail.BitVec.castWidth ) <$> (BFRound (mult_real value1_name value2_name)
                    (Sail.Int.toNatChecked ((2 *i (Sail.BitVec.length op2))))))))))


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def FPAdd_BF16 (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let inf1 ← (( do (undefined_bool_at (← occLabel 1783) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 1784) ()) ) : SailM Bool )
  let result_value ← (( do (undefined_real_at (← occLabel 1785) ()) ) : SailM real )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 1786) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 1787) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 1788) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 1789) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 1790) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 1791) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 1792) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 1793) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length op2) == 32) "sail-arm/v8_base.sail:32145.19-32145.20"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1794)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let fpcr ← (( do (FPCR_read ()) ) : SailM FPCRType )
  let w__0 ← (( do (BFUnpack op1) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (BFUnpack op2) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  if (((BEq.beq type1 FPType_QNaN) || (BEq.beq type2 FPType_QNaN)) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))))
  else
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      if (((inf1 && inf2) && (sign1 == (Complement.complement sign2))) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN__1 fpcr (Sail.BitVec.length result))))
      else
        (do
          if (((inf1 && (sign1 == 0#1)) || (inf2 && (sign2 == 0#1))) : Bool)
          then
            (do
              ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 (Sail.BitVec.length result))))
          else
            (do
              if (((inf1 && (sign1 == 1#1)) || (inf2 && (sign2 == 1#1))) : Bool)
              then
                (do
                  ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 (Sail.BitVec.length result))))
              else
                (do
                  if (((zero1 && zero2) && (sign1 == sign2)) : Bool)
                  then
                    (do
                      ((Sail.BitVec.castWidth ) <$> (FPZero sign1 (Sail.BitVec.length result))))
                  else
                    (do
                      let result_value : real := (add_real value1_name value2_name)
                      if ((eq_real result_value (0)) : Bool)
                      then
                        (do
                          ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 (Sail.BitVec.length result))))
                      else
                        (do
                          ((Sail.BitVec.castWidth ) <$> (BFRound result_value
                            (Sail.BitVec.length result)))))))))


def SPEGetDataSourcePayloadSize (_ : Unit) : SailM Int := do
  (__IMPDEF_integer "SPE Data Source packet payload size")


def SPEGetEventsPayloadSize (_ : Unit) : SailM Int := do
  let size ← (( do (__IMPDEF_integer "SPE Events packet payload size") ) : SailM Int )
  (pure (size))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV88 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap8_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV87 enabled))
  else (pure (()))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV92 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap2_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV91 enabled)
      (__ConfigureV87 enabled))
  else (pure (()))


def EL2Enabled (_ : Unit) : SailM Bool := do
  if (((HaveEL EL2) : Bool) : Bool)
  then
    (do
      if ((← do
           if (((! (HaveEL EL3)) : Bool) : Bool)
           then (pure true)
           else
             (do
               let w__0 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
               (pure ((((_get_SCRType_NS w__0) == 1#1) : Bool))))) : Bool)
      then (pure true)
      else
        (do
          (IsSecureEL2Enabled ())))
  else (pure false)


/-- Type quantifiers: n : Int -/
def PMUCounterIsHyp (n : Int) : SailM Bool := do
  if ((n == INSTRUCTION_COUNTER_ID) : Bool)
  then (pure (false))
  else
    (do
      if ((n == CYCLE_COUNTER_ID) : Bool)
      then (pure (false))
      else
        (do
          let resvd_for_el2 ← (( do (undefined_bool_at (← occLabel 515) ()) ) : SailM Bool )
          if ((HaveEL EL2) : Bool)
          then
            (do
              let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
              let hpmn_bits ← (( do
                if (w__0 : Bool)
                then
                  (do
                    let w__1 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((_get_MDCR_EL2_Type_HPMN w__1))))
                else
                  (do
                    let w__2 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                    (pure ((_get_HDCR_Type_HPMN w__2)))) ) : SailM (BitVec 5) )
              let resvd_for_el2 : Bool := (n ≥b (BitVec.toNat hpmn_bits))
              let w__6 ← (( do
                if ((← do
                     let w__3 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                     (pure ((((BitVec.toNat hpmn_bits) >b w__3) : Bool)))) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__4 ← (( do (HaveFeatHPMN0 ()) ) : SailM Bool )
                          (pure (((! w__4) : Bool)))) && ((IsZero hpmn_bits) : Bool)))) ) : SailM
                Bool )
              if (w__6 : Bool)
              then
                (do
                  (ConstrainUnpredictableBool Unpredictable_CounterReservedForEL2))
              else (pure (resvd_for_el2)))
          else (pure (false))))


def UpdateBranchRecordBuffer (ccu : (BitVec 1)) (cc : (BitVec 14)) (lastfailed : (BitVec 1)) (transactional : (BitVec 1)) (branch_type : (BitVec 6)) (el : (BitVec 2)) (mispredict : (BitVec 1)) (valid_name : (BitVec 2)) (source_address : (BitVec 64)) (target_address : (BitVec 64)) : SailM Unit := do
  let w__0 ← (( do (GetBRBENumRecords ()) ) : SailM Int )
  let loop_i_lower : Nat := 1
  let loop_i_upper : Int := (w__0 -i 1)
  (do
    let mut loop_vars := ()
    for i in [loop_i_upper:loop_i_lower:-1]i do
      let () := loop_vars
      loop_vars ← do
        ArmFull.assert (i <b 64) "sail-arm/v8_base.sail:6440.39-6440.40"
        let w__1 ← (( do readReg Records_SRC ) : SailM (Vector (BitVec 64) 64) )
        let w__2 ← (( do readReg Records_SRC ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_SRC (vectorUpdate w__1 (Sail.Int.toNatChecked (i))
          (GetElem?.getElem! w__2 (Sail.Int.toNatChecked ((i -i 1)))))
        let w__3 ← (( do readReg Records_TGT ) : SailM (Vector (BitVec 64) 64) )
        let w__4 ← (( do readReg Records_TGT ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_TGT (vectorUpdate w__3 (Sail.Int.toNatChecked (i))
          (GetElem?.getElem! w__4 (Sail.Int.toNatChecked ((i -i 1)))))
        let w__5 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
        let w__6 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_INF (vectorUpdate w__5 (Sail.Int.toNatChecked (i))
          (GetElem?.getElem! w__6 (Sail.Int.toNatChecked ((i -i 1)))))
    (pure loop_vars))
  let w__7 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__8 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__7 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__8 0) 46 46 ccu))
  let w__9 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__10 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__9 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__10 0) 45 32 cc))
  let w__11 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__12 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__11 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__12 0) 7 6 el))
  let w__13 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__14 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__13 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__14 0) 1 0 valid_name))
  let w__15 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__16 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__15 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__16 0) 16 16 transactional))
  let w__17 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__18 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__17 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__18 0) 17 17 lastfailed))
  let w__19 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__20 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__19 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__20 0) 5 5 mispredict))
  let w__21 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  let w__22 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_INF (vectorUpdate w__21 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__22 0) 13 8 branch_type))
  let w__23 ← (( do readReg Records_SRC ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_SRC (vectorUpdate w__23 0 (Mk_BRBSRCType source_address))
  let w__24 ← (( do readReg Records_TGT ) : SailM (Vector (BitVec 64) 64) )
  writeReg Records_TGT (vectorUpdate w__24 0 (Mk_BRBTGTType target_address))


def ProfilingBufferOwner (_ : Unit) : SailM (SecurityState × (BitVec 2)) := do
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 583) ()) ) : SailM SecurityState )
  let owning_ss ← (( do
    if ((HaveEL EL3) : Bool)
    then
      (do
        let state_bits ← (( do (undefined_bitvector_at (← occLabel 584) 3) ) : SailM (BitVec 3)
          )
        let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
        let state_bits ← (( do
          if (w__0 : Bool)
          then
            (do
              let w__1 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              let state_bits :=
                (((_get_MDCR_EL3_Type_NSPBE w__1) +++ (_get_MDCR_EL3_Type_NSPB w__2)) : (BitVec 3))
              let w__5 ← (( do
                if ((let b__0 := state_bits
                   (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b10#2 : (BitVec 2))) : Bool)
                   then true
                   else false : Bool)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__3 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                          (pure (((! w__3) : Bool)))) && (let b__1 := state_bits
                        (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 2 1)) == (0b00#2 : (BitVec 2))) : Bool)
                        then true
                        else false : Bool))))) ) : SailM Bool )
              if (w__5 : Bool)
              then
                (do
                  let (_, __tup_1) ← (( do
                    (ConstrainUnpredictableBits Unpredictable_RESERVEDNSxB 3) ) : SailM
                    (Constraint × (BitVec 3)) )
                  (pure (__tup_1)))
              else (pure (state_bits)))
          else
            (do
              let w__6 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              let state_bits := ((0#1 +++ (_get_MDCR_EL3_Type_NSPB w__6)) : (BitVec 3))
              (pure (state_bits))) ) : SailM (BitVec 3) )
        let b__2 := state_bits
        let owning_ss : SecurityState :=
          if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 2 1)) == (0b00#2 : (BitVec 2))) : Bool)
          then SS_Secure
          else
            (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 2 1)) == (0b01#2 : (BitVec 2))) : Bool)
            then SS_NonSecure
            else
              (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__2 2 1)) == (0b11#2 : (BitVec 2))) : Bool)
              then SS_Realm
              else owning_ss))
        (pure (owning_ss)))
    else
      (do
        let w__7 ← (( do (SecureOnlyImplementation ()) ) : SailM Bool )
        let w__8 : SecurityState :=
          if (w__7 : Bool)
          then SS_Secure
          else SS_NonSecure
        (pure ((w__8 : SecurityState)))) ) : SailM SecurityState )
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 585) 2) ) : SailM (BitVec 2) )
  let w__11 ← (( do
    if (((HaveEL EL2) : Bool) : Bool)
    then
      (do
        if (((bne owning_ss SS_Secure) : Bool) : Bool)
        then (pure true)
        else
          (do
            (IsSecureEL2Enabled ())))
    else (pure false) ) : SailM Bool )
  let owning_el ← (( do
    if (w__11 : Bool)
    then
      (do
        let w__12 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        let w__13 : (BitVec 2) :=
          if (((_get_MDCR_EL2_Type_E2PB w__12) == 0b00#2) : Bool)
          then EL2
          else EL1
        (pure ((w__13 : (BitVec 2)))))
    else (pure (EL1)) ) : SailM (BitVec 2) )
  (pure ((owning_ss, owning_el)))


end ArmFull.Functions
