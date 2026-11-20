module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0155
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0173
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0179 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_S2MinTxSZ (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) (s1aarch64 : Bool) : SailM Int := do
  let ips ← (( do (AArch64_PAMax ()) ) : SailM Int )
  let ips ← (( do
    if ((d128 == 0#1) : Bool)
    then
      (do
        let w__2 ← (( do
          (pure ((← do
                (pure ((← do
                      (Have52BitPAExt ())) && ((bne tgx TGx_64KB) : Bool)))) && ((ds == 0#1) : Bool)))
          ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do (AArch64_PAMax ()) ) : SailM Int )
            let ips : Int := ((Min.min 48 w__3) : Int)
            (pure (ips)))
        else
          (do
            let w__4 ← (( do (AArch64_PAMax ()) ) : SailM Int )
            let ips : Int := ((Min.min 52 w__4) : Int)
            (pure (ips))))
    else (pure (ips)) ) : SailM Int )
  let ips : Int := ips
  let min_txsz : Int := (64 -i ips)
  let min_txsz : Int :=
    if ((! s1aarch64) : Bool)
    then (Min.min min_txsz 24)
    else min_txsz
  let min_txsz : Int := min_txsz
  (pure (min_txsz))


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
  ArmFull.assert ((Sail.BitVec.length op2) == 16) "sail-inputs/03-v8_base.sail:32116.19-32116.20"
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
  ArmFull.assert ((Sail.BitVec.length op2) == 32) "sail-inputs/03-v8_base.sail:32155.19-32155.20"
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


def BRB_IALL (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (GetBRBENumRecords ()) ) : SailM Int )
  let loop_i_lower : Nat := 0
  let loop_i_upper : Int := (w__0 -i 1)
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        ArmFull.assert (i <b 64) "sail-inputs/03-v8_base.sail:35665.39-35665.40"
        let w__1 ← (( do readReg Records_SRC ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_SRC (vectorUpdate w__1 (Sail.Int.toNatChecked (i))
          (Mk_BRBSRCType (Zeros (n := 64))))
        let w__2 ← (( do readReg Records_TGT ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_TGT (vectorUpdate w__2 (Sail.Int.toNatChecked (i))
          (Mk_BRBTGTType (Zeros (n := 64))))
        let w__3 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_INF (vectorUpdate w__3 (Sail.Int.toNatChecked (i))
          (Mk_BRBINFType (Zeros (n := 64))))
    (pure loop_vars))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV89 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap9_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV88 enabled))
  else (pure (()))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV93 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap3_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV92 enabled)
      (__ConfigureV88 enabled))
  else (pure (()))


def EL2Enabled (_ : Unit) : SailM Bool := do
  if ((← do
       (HaveEL EL2)) : Bool)
  then
    (do
      if ((← do
           if ((← do
                let w__1 ← (( do (HaveEL EL3) ) : SailM Bool )
                (pure (((! w__1) : Bool)))) : Bool)
           then (pure true)
           else
             (do
               let w__2 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
               (pure ((((_get_SCRType_NS w__2) == 1#1) : Bool))))) : Bool)
      then (pure true)
      else
        (do
          (IsSecureEL2Enabled ())))
  else (pure false)


/-- Type quantifiers: k_check_cnten : Bool, k_check_e : Bool, k_check_inten : Bool, k_exclude_cyc :
  Bool, k_exclude_sync : Bool, k_include_hi_name : Bool, k_include_lo_name : Bool -/
def PMUOverflowCondition (check_e : Bool) (check_cnten : Bool) (check_inten : Bool) (include_hi_name : Bool) (include_lo_name : Bool) (exclude_cyc : Bool) (exclude_sync : Bool) : SailM Bool := do
  let counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let ovsf ← (( do (undefined_bitvector_at (← occLabel 516) 64) ) : SailM (BitVec 64) )
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  let ovsf ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
        let ovsf := (w__1 : (BitVec 64))
        let ovsf : (BitVec 64) := (Sail.BitVec.updateSubrange ovsf 63 33 (Zeros (n := 31)))
        let w__2 ← (( do (HavePMUv3ICNTR ()) ) : SailM Bool )
        let ovsf : (BitVec 64) :=
          if ((! w__2) : Bool)
          then (BitVec.update ovsf INSTRUCTION_COUNTER_ID (Bit 0#1))
          else ovsf
        (pure (ovsf)))
    else
      (do
        let w__3 ← (( do (PMOVSR_read ()) ) : SailM (BitVec 32) )
        let ovsf := ((Sail.BitVec.zeroExtend w__3 64) : (BitVec 64))
        (pure (ovsf))) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if ((counters <b 31) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b counters) && (counters ≤b 30)) "sail-inputs/03-v8_base.sail:4603.61-4603.62"
        let ovsf : (BitVec 64) :=
          (Sail.BitVec.castWidth (Sail.BitVec.updateSubrange ovsf 30
            (Sail.Int.toNatChecked (counters))
            (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked ((31 -i counters))))))))
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    let loop_idx_lower : Nat := 0
    let loop_idx_upper : Int := (counters -i 1)
    (do
      let mut loop_vars := ovsf
      for idx in [loop_idx_lower:loop_idx_upper:1]i do
        let ovsf := loop_vars
        loop_vars ← do
          let E ← (( do (undefined_bitvector_at (← occLabel 517) 1) ) : SailM (BitVec 1) )
          let is_hyp ← (( do (PMUCounterIsHyp idx) ) : SailM Bool )
          let w__4 ← (( do (HaveAArch64 ()) ) : SailM Bool )
          let E ← (( do
            if (w__4 : Bool)
            then
              (do
                if (is_hyp : Bool)
                then
                  (do
                    let w__5 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((_get_MDCR_EL2_Type_HPME w__5))))
                else
                  (do
                    let w__6 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
                    (pure ((_get_PMCR_EL0_Type_E w__6)))))
            else
              (do
                if (is_hyp : Bool)
                then
                  (do
                    let w__8 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                    (pure ((_get_HDCR_Type_HPME w__8))))
                else
                  (do
                    let w__9 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                    (pure ((_get_PMCR_Type_E w__9))))) ) : SailM (BitVec 1) )
          let ovsf ← (( do
            if (check_e : Bool)
            then
              (do
                ArmFull.assert ((0 ≤b idx) && (idx <b 64)) "sail-inputs/03-v8_base.sail:4615.64-4615.65"
                let ovsf : (BitVec 64) :=
                  (BitVec.update ovsf (Sail.Int.toNatChecked (idx))
                    (Bit
                      ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf
                            (Sail.Int.toNatChecked (idx)))])) &&& E)))
                (pure (ovsf)))
            else (pure (ovsf)) ) : SailM (BitVec 64) )
          if ((((! is_hyp) && (! include_lo_name)) || (is_hyp && (! include_hi_name))) : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b idx) && (idx <b 64)) "sail-inputs/03-v8_base.sail:4619.64-4619.65"
              let ovsf : (BitVec 64) := (BitVec.update ovsf (Sail.Int.toNatChecked (idx)) (Bit 0#1))
              (pure (ovsf)))
          else (pure (ovsf))
      (pure loop_vars)) ) : SailM (BitVec 64) )
  let ovsf : (BitVec 64) :=
    if ((exclude_cyc || (! include_lo_name)) : Bool)
    then (BitVec.update ovsf CYCLE_COUNTER_ID (Bit 0#1))
    else ovsf
  let ovsf ← (( do
    if (check_e : Bool)
    then
      (do
        let w__11 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
        let ovsf :=
          ((BitVec.update ovsf CYCLE_COUNTER_ID
            (Bit
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf CYCLE_COUNTER_ID)])) &&& (_get_PMCR_EL0_Type_E
                  w__11)))) : (BitVec 64))
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let w__14 ← (( do
    if ((← do
         (HaveAArch64 ())) : Bool)
    then
      (do
        (HavePMUv3ICNTR ()))
    else (pure false) ) : SailM Bool )
  let ovsf ← (( do
    if (w__14 : Bool)
    then
      (do
        let ovsf : (BitVec 64) :=
          if ((! include_lo_name) : Bool)
          then (BitVec.update ovsf INSTRUCTION_COUNTER_ID (Bit 0#1))
          else ovsf
        if (check_e : Bool)
        then
          (do
            let w__15 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
            let ovsf :=
              ((BitVec.update ovsf INSTRUCTION_COUNTER_ID
                (Bit
                  ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access ovsf INSTRUCTION_COUNTER_ID)])) &&& (_get_PMCR_EL0_Type_E
                      w__15)))) : (BitVec 64))
            (pure (ovsf)))
        else (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if (check_cnten : Bool)
    then
      (do
        let w__16 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let cnten ← (( do
          if (w__16 : Bool)
          then
            (do
              readReg PMCNTENCLR_EL0)
          else
            (do
              let w__18 ← (( do (PMCNTENCLR_read ()) ) : SailM (BitVec 32) )
              (pure ((Sail.BitVec.zeroExtend w__18 64)))) ) : SailM (BitVec 64) )
        let ovsf : (BitVec 64) := (ovsf &&& cnten)
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  let ovsf ← (( do
    if (check_inten : Bool)
    then
      (do
        let w__19 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        let inten ← (( do
          if (w__19 : Bool)
          then
            (do
              readReg PMINTENCLR_EL1)
          else
            (do
              let w__21 ← (( do (PMINTENCLR_read ()) ) : SailM (BitVec 32) )
              (pure ((Sail.BitVec.zeroExtend w__21 64)))) ) : SailM (BitVec 64) )
        let ovsf : (BitVec 64) := (ovsf &&& inten)
        (pure (ovsf)))
    else (pure (ovsf)) ) : SailM (BitVec 64) )
  (pure ((! (IsZero ovsf))))


def ProfilingBufferOwner (_ : Unit) : SailM (SecurityState × (BitVec 2)) := do
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 583) ()) ) : SailM SecurityState )
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  let owning_ss ← (( do
    if (w__0 : Bool)
    then
      (do
        let state_bits ← (( do (undefined_bitvector_at (← occLabel 584) 3) ) : SailM (BitVec 3)
          )
        let w__1 ← (( do (HaveRME ()) ) : SailM Bool )
        let state_bits ← (( do
          if (w__1 : Bool)
          then
            (do
              let w__2 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              let w__3 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              let state_bits :=
                (((_get_MDCR_EL3_Type_NSPBE w__2) +++ (_get_MDCR_EL3_Type_NSPB w__3)) : (BitVec 3))
              let w__6 ← (( do
                if ((let b__0 := state_bits
                   (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b10#2 : (BitVec 2))) : Bool)
                   then true
                   else false : Bool)) : Bool)
                then (pure true)
                else
                  (do
                    (pure ((← do
                          let w__4 ← (( do (HaveSecureEL2Ext ()) ) : SailM Bool )
                          (pure (((! w__4) : Bool)))) && (let b__1 := state_bits
                        (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__1 2 1)) == (0b00#2 : (BitVec 2))) : Bool)
                        then true
                        else false : Bool))))) ) : SailM Bool )
              if (w__6 : Bool)
              then
                (do
                  let (_, __tup_1) ← (( do
                    (ConstrainUnpredictableBits Unpredictable_RESERVEDNSxB 3) ) : SailM
                    (Constraint × (BitVec 3)) )
                  (pure (__tup_1)))
              else (pure (state_bits)))
          else
            (do
              let w__7 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
              let state_bits := ((0#1 +++ (_get_MDCR_EL3_Type_NSPB w__7)) : (BitVec 3))
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
        let w__8 ← (( do (SecureOnlyImplementation ()) ) : SailM Bool )
        let w__9 : SecurityState :=
          if (w__8 : Bool)
          then SS_Secure
          else SS_NonSecure
        (pure ((w__9 : SecurityState)))) ) : SailM SecurityState )
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 585) 2) ) : SailM (BitVec 2) )
  let w__13 ← (( do
    if ((← do
         (HaveEL EL2)) : Bool)
    then
      (do
        if (((bne owning_ss SS_Secure) : Bool) : Bool)
        then (pure true)
        else
          (do
            (IsSecureEL2Enabled ())))
    else (pure false) ) : SailM Bool )
  let owning_el ← (( do
    if (w__13 : Bool)
    then
      (do
        let w__14 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
        let w__15 : (BitVec 2) :=
          if (((_get_MDCR_EL2_Type_E2PB w__14) == 0b00#2) : Bool)
          then EL2
          else EL1
        (pure ((w__15 : (BitVec 2)))))
    else (pure (EL1)) ) : SailM (BitVec 2) )
  (pure ((owning_ss, owning_el)))


def ELFromM32 (mode : (BitVec 5)) : SailM (Bool × (BitVec 2)) := do
  let el ← (( do (undefined_bitvector_at (← occLabel 630) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do (BadMode mode) ) : SailM Bool )
  let valid_name : Bool := (! w__0)
  let w__1 ← (( do (EffectiveSCR_EL3_NSE ()) ) : SailM (BitVec 1) )
  let w__2 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailM (BitVec 1) )
  let effective_nse_ns : (BitVec 2) := (w__1 +++ w__2)
  let questionMark := mode
  let (el, valid_name) ← (( do
    if ((questionMark == M32_Monitor) : Bool)
    then
      (let el : (BitVec 2) := EL3
      (pure ((el, valid_name))))
    else
      (do
        if ((questionMark == M32_Hyp) : Bool)
        then
          (let el : (BitVec 2) := EL2
          (pure ((el, valid_name))))
        else
          (do
            if ((questionMark == M32_FIQ) : Bool)
            then
              (do
                let w__7 ← (( do
                  if ((← do
                       if ((← do
                            (HaveEL EL3)) : Bool)
                       then
                         (do
                           let w__4 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                           (pure (((! w__4) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__6 ← (( do readReg SCR ) : SailM (BitVec 32) )
                      (pure ((((_get_SCR_Type_NS w__6) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let w__8 : (BitVec 2) :=
                  if (w__7 : Bool)
                  then EL3
                  else EL1
                let el := (w__8 : (BitVec 2))
                (pure ((el, valid_name))))
            else
              (do
                if ((questionMark == M32_IRQ) : Bool)
                then
                  (do
                    let w__13 ← (( do
                      if ((← do
                           if ((← do
                                (HaveEL EL3)) : Bool)
                           then
                             (do
                               let w__10 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                               (pure (((! w__10) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__12 ← (( do readReg SCR ) : SailM (BitVec 32) )
                          (pure ((((_get_SCR_Type_NS w__12) == 0#1) : Bool))))
                      else (pure false) ) : SailM Bool )
                    let w__14 : (BitVec 2) :=
                      if (w__13 : Bool)
                      then EL3
                      else EL1
                    let el := (w__14 : (BitVec 2))
                    (pure ((el, valid_name))))
                else
                  (do
                    if ((questionMark == M32_Svc) : Bool)
                    then
                      (do
                        let w__19 ← (( do
                          if ((← do
                               if ((← do
                                    (HaveEL EL3)) : Bool)
                               then
                                 (do
                                   let w__16 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                   (pure (((! w__16) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__18 ← (( do readReg SCR ) : SailM (BitVec 32) )
                              (pure ((((_get_SCR_Type_NS w__18) == 0#1) : Bool))))
                          else (pure false) ) : SailM Bool )
                        let w__20 : (BitVec 2) :=
                          if (w__19 : Bool)
                          then EL3
                          else EL1
                        let el := (w__20 : (BitVec 2))
                        (pure ((el, valid_name))))
                    else
                      (do
                        if ((questionMark == M32_Abort) : Bool)
                        then
                          (do
                            let w__25 ← (( do
                              if ((← do
                                   if ((← do
                                        (HaveEL EL3)) : Bool)
                                   then
                                     (do
                                       let w__22 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                       (pure (((! w__22) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__24 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                  (pure ((((_get_SCR_Type_NS w__24) == 0#1) : Bool))))
                              else (pure false) ) : SailM Bool )
                            let w__26 : (BitVec 2) :=
                              if (w__25 : Bool)
                              then EL3
                              else EL1
                            let el := (w__26 : (BitVec 2))
                            (pure ((el, valid_name))))
                        else
                          (do
                            if ((questionMark == M32_Undef) : Bool)
                            then
                              (do
                                let w__31 ← (( do
                                  if ((← do
                                       if ((← do
                                            (HaveEL EL3)) : Bool)
                                       then
                                         (do
                                           let w__28 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                           (pure (((! w__28) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__30 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                      (pure ((((_get_SCR_Type_NS w__30) == 0#1) : Bool))))
                                  else (pure false) ) : SailM Bool )
                                let w__32 : (BitVec 2) :=
                                  if (w__31 : Bool)
                                  then EL3
                                  else EL1
                                let el := (w__32 : (BitVec 2))
                                (pure ((el, valid_name))))
                            else
                              (do
                                if ((questionMark == M32_System) : Bool)
                                then
                                  (do
                                    let w__37 ← (( do
                                      if ((← do
                                           if ((← do
                                                (HaveEL EL3)) : Bool)
                                           then
                                             (do
                                               let w__34 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                               (pure (((! w__34) : Bool))))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          let w__36 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                          (pure ((((_get_SCR_Type_NS w__36) == 0#1) : Bool))))
                                      else (pure false) ) : SailM Bool )
                                    let w__38 : (BitVec 2) :=
                                      if (w__37 : Bool)
                                      then EL3
                                      else EL1
                                    let el := (w__38 : (BitVec 2))
                                    (pure ((el, valid_name))))
                                else
                                  (let (el, valid_name) : ((BitVec 2) × Bool) :=
                                    if ((questionMark == M32_User) : Bool)
                                    then
                                      (let el : (BitVec 2) := EL0
                                      (el, valid_name))
                                    else
                                      (let valid_name : Bool := false
                                      (el, valid_name))
                                  (pure ((el, valid_name))))))))))) ) : SailM ((BitVec 2) × Bool) )
  let w__42 ← (( do
    if ((← do
         if (((valid_name && (el == EL2)) : Bool) : Bool)
         then
           (do
             (HaveEL EL3))
         else (pure false)) : Bool)
    then
      (do
        let w__41 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
        (pure ((((_get_SCRType_NS w__41) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let valid_name ← (( do
    if (w__42 : Bool)
    then (pure (false))
    else
      (do
        let w__45 ← (( do
          (pure ((← do
                if ((valid_name : Bool) : Bool)
                then
                  (do
                    (HaveRME ()))
                else (pure false)) && ((effective_nse_ns == 0b10#2) : Bool))) ) : SailM Bool )
        let valid_name : Bool :=
          if (w__45 : Bool)
          then false
          else valid_name
        (pure (valid_name))) ) : SailM Bool )
  let el ← (( do
    if ((! valid_name) : Bool)
    then
      (do
        (__UNKNOWN_bits 2))
    else (pure (el)) ) : SailM (BitVec 2) )
  let el := el
  (pure ((valid_name, el)))


end ArmFull.Functions
