import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0044
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0113
import ArmFull.Fn.M0116
import ArmFull.Fn.M0121
import ArmFull.Fn.M0145
import ArmFull.Fn.M0147

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

/-- Type quantifiers: N : Nat, N = 32 -/
def BFRound (op : real) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert (N == 32) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:32006.18-32006.19"
  ArmFull.assert (bne op (0)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:32007.20-32007.21"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1764)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  let minimum_exp : Int := (Neg.neg 126)
  let E : Nat := 8
  let F : Nat := 23
  let sign ← (( do (undefined_bitvector_at (← occLabel 1765) 1) ) : SailM (BitVec 1) )
  let mantissa ← (( do (undefined_real_at (← occLabel 1766) ()) ) : SailM real )
  let (mantissa, sign) : (real × (BitVec 1)) :=
    if ((lt_real op (0)) : Bool)
    then
      (let sign : (BitVec 1) := 1#1
      let mantissa : real := (neg_real op)
      (mantissa, sign))
    else
      (let sign : (BitVec 1) := 0#1
      let mantissa : real := op
      (mantissa, sign))
  let exponent : Int := 0
  let (exponent, mantissa) ← (( do
    let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (exponent, mantissa) => (pure (lt_real
        mantissa (1)))) (exponent, mantissa)
      fun (exponent, mantissa) => do
        (pure (let mantissa : real := (mult_real mantissa (2))
          let exponent : Int := (exponent -i 1)
          (exponent, mantissa) : (Int × real)))
    (pure loop_vars) ) : SailM (Int × real) )
  let (exponent, mantissa) ← (( do
    let loop_vars_1 ← sailWhileFuelM (fuel := 1048576) (fun (exponent, mantissa) => (pure (gteq_real
        mantissa (2)))) (exponent, mantissa)
      fun (exponent, mantissa) => do
        (pure (let mantissa : real := (div_real mantissa (2))
          let exponent : Int := (exponent +i 1)
          (exponent, mantissa) : (Int × real)))
    (pure loop_vars_1) ) : SailM (Int × real) )
  let exponent : Int := exponent
  if ((exponent <b minimum_exp) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPZero sign N)))
  else
    (do
      let biased_exp : Int := (Max.max ((exponent -i minimum_exp) +i 1) 0)
      let mantissa := mantissa
      let int_mant : Int := (round_down (mult_real mantissa (real_power (2) F)))
      let error : real := (sub_real (mult_real mantissa (real_power (2) F)) (to_real int_mant))
      let int_mant : Int :=
        if ((bne error (0)) : Bool)
        then (integer_update_subrange int_mant 0 0 1#1)
        else int_mant
      let int_mant : Int := int_mant
      if ((biased_exp ≥b ((2 ^i E) -i 1)) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPInfinity sign N)))
      else
        (let result : (BitVec N) :=
          (Sail.BitVec.castWidth ((sign +++ (integer_subrange biased_exp ((N -i 2) -i F) 0)) +++ (integer_subrange
              int_mant (F -i 1) 0)))
        (pure (result))))


/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset__seg4 (cold : Bool) : SailM Bool := do
  let w__1250 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1250 5 5 0#1)
  let w__1251 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1251 4 4 0#1)
  let w__1252 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1252 3 3 0#1)
  let w__1253 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1253 2 2 0#1)
  let w__1254 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1254 1 1 0#1)
  let w__1255 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1255 0 0 0#1)
  let w__1256 ← (( do readReg CNTPS_TVAL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTPS_TVAL_EL1 (Sail.BitVec.updateSubrange w__1256 63 32
    0b00000000000000000000000000000000#32)
  let w__1257 ← (( do readReg ID_AA64AFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64AFR1_EL1 (Sail.BitVec.updateSubrange w__1257 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1258 ← (( do readReg LOREA_EL1 ) : SailM (BitVec 64) )
  writeReg LOREA_EL1 (Sail.BitVec.updateSubrange w__1258 63 56 0b00000000#8)
  let w__1259 ← (( do readReg LOREA_EL1 ) : SailM (BitVec 64) )
  writeReg LOREA_EL1 (Sail.BitVec.updateSubrange w__1259 15 0 0b0000000000000000#16)
  let w__1260 ← (( do readReg CNTV_TVAL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTV_TVAL_EL0 (Sail.BitVec.updateSubrange w__1260 63 32
    0b00000000000000000000000000000000#32)
  let w__1261 ← (( do readReg ICV_DIR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_DIR_EL1 (Sail.BitVec.updateSubrange w__1261 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1262 ← (( do readReg ICC_IAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IAR1_EL1 (Sail.BitVec.updateSubrange w__1262 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1263 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPIDR_EL1 (Sail.BitVec.updateSubrange w__1263 63 40 0b000000000000000000000000#24)
  let w__1264 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPIDR_EL1 (BitVec.update w__1264 31 (Bit 1#1))
  let w__1265 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPIDR_EL1 (Sail.BitVec.updateSubrange w__1265 29 25 0b00000#5)
  let w__1266 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange w__1266 63 32
    0b00000000000000000000000000000000#32)
  let w__1267 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
  writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange w__1267 31 8 0b000000000000000000000000#24)
  if (cold : Bool)
  then
    (do
      let w__1268 ← (( do readReg DBGCLAIMCLR_EL1 ) : SailM (BitVec 64) )
      writeReg DBGCLAIMCLR_EL1 (Sail.BitVec.updateSubrange w__1268 7 0 0b00000000#8))
  else (pure (()))
  let w__1269 ← (( do readReg ICV_HPPIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_HPPIR1_EL1 (Sail.BitVec.updateSubrange w__1269 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1270 ← (( do readReg ID_AA64AFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64AFR0_EL1 (Sail.BitVec.updateSubrange w__1270 63 32
    0b00000000000000000000000000000000#32)
  let w__1271 ← (( do readReg ID_PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange w__1271 63 12
    0b0000000000000000000000000000000000000000000000000000#52)
  let w__1272 ← (( do readReg ID_PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange w__1272 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1273 ← (( do readReg CNTHV_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHV_CTL_EL2 (Sail.BitVec.updateSubrange w__1273 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__1274 ← (( do readReg ICC_EOIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_EOIR0_EL1 (Sail.BitVec.updateSubrange w__1274 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1275 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1275 63 60 0b0000#4)
  let w__1276 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1276 51 48 0b0000#4)
  let w__1277 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1277 39 36 0b0000#4)
  let w__1278 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1278 31 28 0b0000#4)
  let w__1279 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__1279 15 8 0b00000000#8)
  let w__1280 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
  writeReg ZCR_EL3 (Sail.BitVec.updateSubrange w__1280 63 9
    0b0000000000000000000000000000000000000000000000000000000#55)
  let w__1281 ← (( do readReg ZCR_EL3 ) : SailM (BitVec 64) )
  writeReg ZCR_EL3 (Sail.BitVec.updateSubrange w__1281 8 4 0b00000#5)
  let w__1282 ← (( do readReg ZCR_EL1 ) : SailM (BitVec 64) )
  writeReg ZCR_EL1 (Sail.BitVec.updateSubrange w__1282 63 9
    0b0000000000000000000000000000000000000000000000000000000#55)
  let w__1283 ← (( do readReg ZCR_EL1 ) : SailM (BitVec 64) )
  writeReg ZCR_EL1 (Sail.BitVec.updateSubrange w__1283 8 4 0b00000#5)
  let w__1284 ← (( do readReg ZCR_EL2 ) : SailM (BitVec 64) )
  writeReg ZCR_EL2 (Sail.BitVec.updateSubrange w__1284 63 9
    0b0000000000000000000000000000000000000000000000000000000#55)
  let w__1285 ← (( do readReg ZCR_EL2 ) : SailM (BitVec 64) )
  writeReg ZCR_EL2 (Sail.BitVec.updateSubrange w__1285 8 4 0b00000#5)
  let w__1286 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
  writeReg SMCR_EL3 (Sail.BitVec.updateSubrange w__1286 63 32 0b00000000000000000000000000000000#32)
  let w__1287 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
  writeReg SMCR_EL3 (Sail.BitVec.updateSubrange w__1287 29 9 0b000000000000000000000#21)
  let w__1288 ← (( do readReg SMCR_EL3 ) : SailM (BitVec 64) )
  writeReg SMCR_EL3 (Sail.BitVec.updateSubrange w__1288 8 4 0b00000#5)
  let w__1289 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
  writeReg SMCR_EL1 (Sail.BitVec.updateSubrange w__1289 63 32 0b00000000000000000000000000000000#32)
  let w__1290 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
  writeReg SMCR_EL1 (Sail.BitVec.updateSubrange w__1290 29 9 0b000000000000000000000#21)
  let w__1291 ← (( do readReg SMCR_EL1 ) : SailM (BitVec 64) )
  writeReg SMCR_EL1 (Sail.BitVec.updateSubrange w__1291 8 4 0b00000#5)
  let w__1292 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
  writeReg SMCR_EL2 (Sail.BitVec.updateSubrange w__1292 63 32 0b00000000000000000000000000000000#32)
  let w__1293 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
  writeReg SMCR_EL2 (Sail.BitVec.updateSubrange w__1293 29 9 0b000000000000000000000#21)
  let w__1294 ← (( do readReg SMCR_EL2 ) : SailM (BitVec 64) )
  writeReg SMCR_EL2 (Sail.BitVec.updateSubrange w__1294 8 4 0b00000#5)
  let w__1295 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__1295 62 60 0b000#3)
  let w__1296 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__1296 51 49 0b000#3)
  let w__1297 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__1297 41 40 0b00#2)
  let w__1298 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__1298 31 0
    0b00000000000000000000000000000000#32)
  let w__1299 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
  writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1299 63 32
    0b00000000000000000000000000000000#32)
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__1300 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
      let w__1301 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1300 31 31 w__1301))
  else
    (do
      if (((! cold) && (! (HaveEL EL3))) : Bool)
      then
        (do
          let w__1302 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
          writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1302 31 31 1#1))
      else (pure (())))
  let w__1303 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
  writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1303 30 9 0b0000000000000000000000#22)
  let w__1304 ← (( do readReg MPAMHCR_EL2 ) : SailM (BitVec 64) )
  writeReg MPAMHCR_EL2 (Sail.BitVec.updateSubrange w__1304 7 2 0b000000#6)
  let w__1305 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__1305 63 62 0b00#2)
  let w__1306 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__1306 56 40 0b00000000000000000#17)
  let w__1307 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__1307 31 21 0b00000000000#11)
  let w__1308 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMIDR_EL1 (BitVec.update w__1308 16 (Bit 0#1))
  let w__1309 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1309 63 63 0#1)
  let w__1310 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1310 62 59 0b0000#4)
  let w__1311 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (BitVec.update w__1311 57 (Bit 0#1))
  let w__1312 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
  writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1312 53 51 0b000#3)
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__1313 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      let w__1314 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1313 49 49 w__1314))
  else
    (do
      if (((! cold) && (! (HaveEL EL3))) : Bool)
      then
        (do
          let w__1315 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1315 49 49 1#1))
      else (pure (())))
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__1316 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      let w__1317 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1316 48 48 w__1317))
  else
    (do
      if (((! cold) && (! (HaveEL EL3))) : Bool)
      then
        (do
          let w__1318 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          writeReg MPAM2_EL2 (Sail.BitVec.updateSubrange w__1318 48 48 1#1))
      else (pure (())))
  let w__1319 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (_update_MPAM3_EL3_Type_MPAMEN w__1319 0#1))
  let w__1320 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (_update_MPAM3_EL3_Type_TRAPLOWER w__1320 1#1))
  let w__1321 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 2 w__1321 58 0b00#2)))
  let w__1322 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 2 w__1322 53 0b00#2)))
  let w__1323 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 4 w__1323 48 0b0000#4)))
  let w__1324 ← (( do readReg MPAM0_EL1 ) : SailM (BitVec 64) )
  writeReg MPAM0_EL1 (Sail.BitVec.updateSubrange w__1324 63 48 0b0000000000000000#16)
  let w__1325 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMSM_EL1 (Sail.BitVec.updateSubrange w__1325 63 48 0b0000000000000000#16)
  let w__1326 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMSM_EL1 (Sail.BitVec.updateSubrange w__1326 39 32 0b00000000#8)
  let w__1327 ← (( do readReg MPAMSM_EL1 ) : SailM (BitVec 64) )
  writeReg MPAMSM_EL1 (Sail.BitVec.updateSubrange w__1327 15 0 0b0000000000000000#16)
  let w__1328 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (_update_MPAM1_EL1_Type_MPAMEN w__1328 0#1))
  let w__1329 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 2 w__1329 61 0b00#2)))
  let w__1330 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 5 w__1330 55 0b00000#5)))
  let w__1331 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
  (MPAM1_EL1_write (Mk_MPAM1_EL1_Type (set_slice 6 w__1331 48 0b000000#6)))
  let w__1332 ← (( do readReg MPAMVPMV_EL2 ) : SailM (BitVec 64) )
  writeReg MPAMVPMV_EL2 (Sail.BitVec.updateSubrange w__1332 63 32
    0b00000000000000000000000000000000#32)
  let w__1333 ← (( do readReg GMID_EL1 ) : SailM (BitVec 64) )
  writeReg GMID_EL1 (Sail.BitVec.updateSubrange w__1333 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__1334 ← (( do readReg TFSR_EL3 ) : SailM (BitVec 64) )
  writeReg TFSR_EL3 (Sail.BitVec.updateSubrange w__1334 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1335 ← (( do readReg TFSRE0_EL1 ) : SailM (BitVec 64) )
  writeReg TFSRE0_EL1 (Sail.BitVec.updateSubrange w__1335 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__1336 ← (( do readReg TFSR_EL2 ) : SailM (BitVec 64) )
  writeReg TFSR_EL2 (Sail.BitVec.updateSubrange w__1336 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__1337 ← (( do readReg TFSR_EL1 ) : SailM (BitVec 64) )
  writeReg TFSR_EL1 (Sail.BitVec.updateSubrange w__1337 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__1338 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__1338 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1339 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__1339 7 4 0b0000#4)
  let w__1340 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__1340 63 56 0b00000000#8)
  let w__1341 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__1341 7 4 0b0000#4)
  let w__1342 ← (( do readReg GCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCR_EL1 (Sail.BitVec.updateSubrange w__1342 63 17
    0b00000000000000000000000000000000000000000000000#47)
  let w__1343 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCR_EL0 (Sail.BitVec.updateSubrange w__1343 63 18
    0b0000000000000000000000000000000000000000000000#46)
  let w__1344 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCR_EL0 (Sail.BitVec.updateSubrange w__1344 16 11 0b000000#6)
  let w__1345 ← (( do readReg AMCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCR_EL0 (Sail.BitVec.updateSubrange w__1345 9 0 0b0000000000#10)
  let w__1346 ← (( do readReg AMCNTENSET0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENSET0_EL0 (Sail.BitVec.updateSubrange w__1346 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1347 ← (( do readReg AMCNTENSET0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENSET0_EL0 (Sail.BitVec.updateSubrange w__1347 15 4 0b000000000000#12)
  if (cold : Bool)
  then
    (do
      let w__1348 ← (( do readReg AMCNTENSET0_EL0 ) : SailM (BitVec 64) )
      writeReg AMCNTENSET0_EL0 (Sail.BitVec.updateSubrange w__1348 3 0 0b0000#4))
  else (pure (()))
  let w__1349 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR0_EL0 (Sail.BitVec.updateSubrange w__1349 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1350 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR0_EL0 (Sail.BitVec.updateSubrange w__1350 15 4 0b000000000000#12)
  if (cold : Bool)
  then
    (do
      let w__1351 ← (( do readReg AMCNTENCLR0_EL0 ) : SailM (BitVec 64) )
      writeReg AMCNTENCLR0_EL0 (Sail.BitVec.updateSubrange w__1351 3 0 0b0000#4))
  else (pure (()))
  let w__1352 ← (( do readReg AMCNTENSET1_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENSET1_EL0 (Sail.BitVec.updateSubrange w__1352 63 16
    0b000000000000000000000000000000000000000000000000#48)
  if (cold : Bool)
  then
    (do
      let w__1353 ← (( do readReg AMCNTENSET1_EL0 ) : SailM (BitVec 64) )
      writeReg AMCNTENSET1_EL0 (Sail.BitVec.updateSubrange w__1353 15 0 0b0000000000000000#16))
  else (pure (()))
  let w__1354 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
  writeReg AMCNTENCLR1_EL0 (Sail.BitVec.updateSubrange w__1354 63 16
    0b000000000000000000000000000000000000000000000000#48)
  if (cold : Bool)
  then
    (do
      let w__1355 ← (( do readReg AMCNTENCLR1_EL0 ) : SailM (BitVec 64) )
      writeReg AMCNTENCLR1_EL0 (Sail.BitVec.updateSubrange w__1355 15 0 0b0000000000000000#16))
  else (pure (()))
  let w__1356 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__1356 63 32
    0b00000000000000000000000000000000#32)
  let w__1357 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__1357 27 25 0b000#3)
  let w__1358 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__1358 23 14 0b0000000000#10)
  let w__1359 ← (( do readReg AMUSERENR_EL0 ) : SailM (BitVec 64) )
  writeReg AMUSERENR_EL0 (Sail.BitVec.updateSubrange w__1359 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1360 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__1360 63 32
    0b00000000000000000000000000000000#32)
  let w__1361 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCGCR_EL0 (Sail.BitVec.updateSubrange w__1361 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1362 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSFCR_EL1 (Sail.BitVec.updateSubrange w__1362 63 19
    0b000000000000000000000000000000000000000000000#45)
  let w__1363 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSFCR_EL1 (Sail.BitVec.updateSubrange w__1363 15 5 0b00000000000#11)
  let w__1364 ← (( do readReg PMSIRR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIRR_EL1 (Sail.BitVec.updateSubrange w__1364 63 32
    0b00000000000000000000000000000000#32)
  let w__1365 ← (( do readReg PMSIRR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIRR_EL1 (Sail.BitVec.updateSubrange w__1365 7 1 0b0000000#7)
  let w__1366 ← (( do readReg PMSICR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__1366 55 32 0b000000000000000000000000#24)
  let w__1367 ← (( do readReg PMSEVFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSEVFR_EL1 (Sail.BitVec.updateSubrange w__1367 47 32 0b0000000000000000#16)
  let w__1368 ← (( do readReg PMSEVFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSEVFR_EL1 (BitVec.update w__1368 0 (Bit 0#1))
  let w__1369 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBLIMITR_EL1 (Sail.BitVec.updateSubrange w__1369 11 6 0b000000#6)
  let w__1370 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBLIMITR_EL1 (Sail.BitVec.updateSubrange w__1370 4 3 0b00#2)
  let w__1371 ← (( do readReg PMBLIMITR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBLIMITR_EL1 (Sail.BitVec.updateSubrange w__1371 0 0 0#1)
  let w__1372 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__1372 63 40 0b000000000000000000000000#24)
  let w__1373 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__1373 36 32 0b00000#5)
  let w__1374 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__1374 25 20 0b000000#6)
  let w__1375 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
  writeReg PMSCR_EL2 (Sail.BitVec.updateSubrange w__1375 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1376 ← (( do readReg PMSCR_EL2 ) : SailM (BitVec 64) )
  writeReg PMSCR_EL2 (BitVec.update w__1376 2 (Bit 0#1))
  let w__1377 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSCR_EL1 (Sail.BitVec.updateSubrange w__1377 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1378 ← (( do readReg PMSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSCR_EL1 (BitVec.update w__1378 2 (Bit 0#1))
  let w__1379 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__1379 63 26
    0b00000000000000000000000000000000000000#38)
  let w__1380 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSNEVFR_EL1 (Sail.BitVec.updateSubrange w__1380 47 32 0b0000000000000000#16)
  let w__1381 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSNEVFR_EL1 (BitVec.update w__1381 0 (Bit 0#1))
  let w__1382 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__1382 63 12
    0b0000000000000000000000000000000000000000000000000000#52)
  let w__1383 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__1383 7 6 0b00#2)
  let w__1384 ← (( do readReg PMSLATFR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSLATFR_EL1 (Sail.BitVec.updateSubrange w__1384 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1385 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1385 63 32 0b00000000000000000000000000000000#32)
  let w__1386 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1386 30 25 0b000000#6)
  let w__1387 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1387 63 32 0b00000000000000000000000000000000#32)
  let w__1388 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1388 30 16 0b000000000000000#15)
  let w__1389 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (BitVec.update w__1389 13 (Bit 0#1))
  let w__1390 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (BitVec.update w__1390 11 (Bit 0#1))
  let w__1391 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1391 8 4 0b00000#5)
  let w__1392 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1392 63 32 0b00000000000000000000000000000000#32)
  let w__1393 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1393 30 16 0b000000000000000#15)
  let w__1394 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (BitVec.update w__1394 13 (Bit 0#1))
  let w__1395 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1395 11 10 0b00#2)
  let w__1396 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
  writeReg VDISR_EL2 (Sail.BitVec.updateSubrange w__1396 8 6 0b000#3)
  let w__1397 ← (( do readReg ERRIDR_EL1 ) : SailM (BitVec 64) )
  writeReg ERRIDR_EL1 (Sail.BitVec.updateSubrange w__1397 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1398 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1398 63 32 0b00000000000000000000000000000000#32)
  let w__1399 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1399 30 25 0b000000#6)
  let w__1400 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1400 23 13 0b00000000000#11)
  let w__1401 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1401 8 6 0b000#3)
  let w__1402 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1402 63 32 0b00000000000000000000000000000000#32)
  let w__1403 ← (( do readReg DISR_EL1 ) : SailM (BitVec 64) )
  writeReg DISR_EL1 (Sail.BitVec.updateSubrange w__1403 30 25 0b000000#6)
  let w__1404 ← (( do readReg ERRSELR_EL1 ) : SailM (BitVec 64) )
  writeReg ERRSELR_EL1 (Sail.BitVec.updateSubrange w__1404 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1405 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (Sail.BitVec.updateSubrange w__1405 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1406 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (BitVec.update w__1406 13 (Bit 0#1))
  let w__1407 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (Sail.BitVec.updateSubrange w__1407 11 0 0b000000000000#12)
  let w__1408 ← (( do readReg VSESR_EL2 ) : SailM (BitVec 64) )
  writeReg VSESR_EL2 (Sail.BitVec.updateSubrange w__1408 63 25
    0b000000000000000000000000000000000000000#39)
  let w__1409 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1409 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1411 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1411 : Bool)
  then
    (do
      let w__1412 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1413 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1412 23 23 w__1413))
  else (pure (()))
  let w__1415 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1414 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1414) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1415 : Bool)
  then
    (do
      let w__1416 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1417 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1416 23 23 w__1417))
  else (pure (()))
  let w__1419 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1419 : Bool)
  then
    (do
      let w__1420 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1421 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1420 22 22 w__1421))
  else (pure (()))
  let w__1423 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1422 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1422) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1423 : Bool)
  then
    (do
      let w__1424 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1425 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1424 22 22 w__1425))
  else (pure (()))
  let w__1426 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1426 21 10 0b000000000000#12)
  let w__1428 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1428 : Bool)
  then
    (do
      let w__1429 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1430 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1429 8 8 w__1430))
  else (pure (()))
  let w__1432 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1431 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1431) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1432 : Bool)
  then
    (do
      let w__1433 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1434 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1433 8 8 w__1434))
  else (pure (()))
  let w__1435 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (BitVec.update w__1435 7 (Bit 0#1))
  let w__1437 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1437 : Bool)
  then
    (do
      let w__1438 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1439 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1438 6 5 w__1439))
  else (pure (()))
  let w__1441 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1440 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1440) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1441 : Bool)
  then
    (do
      let w__1442 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1443 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1442 6 5 w__1443))
  else (pure (()))
  let w__1445 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1445 : Bool)
  then
    (do
      let w__1446 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1447 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1446 4 4 w__1447))
  else (pure (()))
  let w__1449 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1448 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1448) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1449 : Bool)
  then
    (do
      let w__1450 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1451 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1450 4 4 w__1451))
  else (pure (()))
  let w__1453 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1453 : Bool)
  then
    (do
      let w__1454 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1455 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1454 3 3 w__1455))
  else (pure (()))
  let w__1457 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1456 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1456) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1457 : Bool)
  then
    (do
      let w__1458 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
      let w__1459 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1458 3 3 w__1459))
  else (pure (()))
  let w__1460 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (BitVec.update w__1460 2 (Bit 0#1))
  let w__1461 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1461 1 1 0#1)
  let w__1462 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL2 (Sail.BitVec.updateSubrange w__1462 0 0 0#1)
  let w__1463 ← (( do readReg BRBTS_EL1 ) : SailM (BitVec 64) )
  writeReg BRBTS_EL1 (Sail.BitVec.updateSubrange w__1463 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1464 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1464 63 30
    0b0000000000000000000000000000000000#34)
  let w__1465 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1465 27 23 0b00000#5)
  let w__1467 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1467 : Bool)
  then
    (do
      let w__1468 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1469 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1468 22 22 w__1469))
  else (pure (()))
  let w__1471 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1470 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1470) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1471 : Bool)
  then
    (do
      let w__1472 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1473 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1472 22 22 w__1473))
  else (pure (()))
  let w__1475 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1475 : Bool)
  then
    (do
      let w__1476 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1477 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1476 21 21 w__1477))
  else (pure (()))
  let w__1479 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1478 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1478) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1479 : Bool)
  then
    (do
      let w__1480 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1481 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1480 21 21 w__1481))
  else (pure (()))
  let w__1483 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1483 : Bool)
  then
    (do
      let w__1484 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1485 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1484 20 20 w__1485))
  else (pure (()))
  let w__1487 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1486 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1486) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1487 : Bool)
  then
    (do
      let w__1488 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1489 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1488 20 20 w__1489))
  else (pure (()))
  let w__1491 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1491 : Bool)
  then
    (do
      let w__1492 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1493 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1492 19 19 w__1493))
  else (pure (()))
  let w__1495 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1494 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1494) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1495 : Bool)
  then
    (do
      let w__1496 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1497 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1496 19 19 w__1497))
  else (pure (()))
  let w__1499 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1499 : Bool)
  then
    (do
      let w__1500 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1501 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1500 18 18 w__1501))
  else (pure (()))
  let w__1503 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1502 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1502) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1503 : Bool)
  then
    (do
      let w__1504 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1505 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1504 18 18 w__1505))
  else (pure (()))
  let w__1507 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1507 : Bool)
  then
    (do
      let w__1508 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1509 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1508 17 17 w__1509))
  else (pure (()))
  let w__1511 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1510 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1510) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1511 : Bool)
  then
    (do
      let w__1512 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1513 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1512 17 17 w__1513))
  else (pure (()))
  let w__1515 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1515 : Bool)
  then
    (do
      let w__1516 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1517 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1516 16 16 w__1517))
  else (pure (()))
  let w__1519 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1518 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1518) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1519 : Bool)
  then
    (do
      let w__1520 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1521 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1520 16 16 w__1521))
  else (pure (()))
  let w__1522 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1522 15 8 0b00000000#8)
  let w__1524 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1524 : Bool)
  then
    (do
      let w__1525 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1526 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1525 7 7 w__1526))
  else (pure (()))
  let w__1528 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1527 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1527) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1528 : Bool)
  then
    (do
      let w__1529 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1530 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1529 7 7 w__1530))
  else (pure (()))
  let w__1532 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1532 : Bool)
  then
    (do
      let w__1533 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1534 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1533 6 6 w__1534))
  else (pure (()))
  let w__1536 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1535 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1535) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1536 : Bool)
  then
    (do
      let w__1537 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
      let w__1538 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1537 6 6 w__1538))
  else (pure (()))
  let w__1539 ← (( do readReg BRBFCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBFCR_EL1 (Sail.BitVec.updateSubrange w__1539 5 0 0b000000#6)
  let w__1540 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1540 63 47 0b00000000000000000#17)
  let w__1541 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1541 31 18 0b00000000000000#14)
  let w__1542 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1542 15 14 0b00#2)
  let w__1543 ← (( do readReg BRBINFINJ_EL1 ) : SailM (BitVec 64) )
  writeReg BRBINFINJ_EL1 (Sail.BitVec.updateSubrange w__1543 4 2 0b000#3)
  let w__1544 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1544 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1546 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1546 : Bool)
  then
    (do
      let w__1547 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1548 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1547 23 23 w__1548))
  else (pure (()))
  let w__1550 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1549 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1549) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1550 : Bool)
  then
    (do
      let w__1551 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1552 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1551 23 23 w__1552))
  else (pure (()))
  let w__1554 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1554 : Bool)
  then
    (do
      let w__1555 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1556 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1555 22 22 w__1556))
  else (pure (()))
  let w__1558 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1557 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1557) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1558 : Bool)
  then
    (do
      let w__1559 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1560 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1559 22 22 w__1560))
  else (pure (()))
  let w__1561 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1561 21 10 0b000000000000#12)
  let w__1563 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1563 : Bool)
  then
    (do
      let w__1564 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1565 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1564 8 8 w__1565))
  else (pure (()))
  let w__1567 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1566 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1566) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1567 : Bool)
  then
    (do
      let w__1568 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1569 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1568 8 8 w__1569))
  else (pure (()))
  let w__1570 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (BitVec.update w__1570 7 (Bit 0#1))
  let w__1572 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1572 : Bool)
  then
    (do
      let w__1573 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1574 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1573 6 5 w__1574))
  else (pure (()))
  let w__1576 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1575 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1575) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1576 : Bool)
  then
    (do
      let w__1577 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1578 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1577 6 5 w__1578))
  else (pure (()))
  let w__1580 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1580 : Bool)
  then
    (do
      let w__1581 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1582 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1581 4 4 w__1582))
  else (pure (()))
  let w__1584 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1583 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1583) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1584 : Bool)
  then
    (do
      let w__1585 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1586 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1585 4 4 w__1586))
  else (pure (()))
  let w__1588 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_BRBEv1p1))
    else (pure false) ) : SailM Bool )
  if (w__1588 : Bool)
  then
    (do
      let w__1589 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1590 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1589 3 3 w__1590))
  else (pure (()))
  let w__1592 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1591 ← (( do (IsFeatureImplemented FEAT_BRBEv1p1) ) : SailM Bool )
        (pure (((! w__1591) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1592 : Bool)
  then
    (do
      let w__1593 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__1594 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1593 3 3 w__1594))
  else (pure (()))
  let w__1595 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (BitVec.update w__1595 2 (Bit 0#1))
  let w__1596 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1596 1 1 0#1)
  let w__1597 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
  writeReg BRBCR_EL1 (Sail.BitVec.updateSubrange w__1597 0 0 0#1)
  let w__1598 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
  writeReg BRBIDR0_EL1 (Sail.BitVec.updateSubrange w__1598 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1599 ← (( do readReg GCSPR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSPR_EL3 (Sail.BitVec.updateSubrange w__1599 2 0 0b000#3)
  let w__1600 ← (( do readReg GCSPR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSPR_EL1 (Sail.BitVec.updateSubrange w__1600 2 0 0b000#3)
  let w__1601 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1601 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__1602 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1602 9 9 0#1)
  let w__1603 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1603 8 8 0#1)
  let w__1604 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (BitVec.update w__1604 7 (Bit 0#1))
  let w__1605 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1605 6 6 0#1)
  let w__1606 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1606 4 1 0b0000#4)
  let w__1607 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL3 (Sail.BitVec.updateSubrange w__1607 0 0 0#1)
  let w__1608 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1608 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__1609 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1609 9 9 0#1)
  let w__1610 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1610 8 8 0#1)
  let w__1611 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (BitVec.update w__1611 7 (Bit 0#1))
  let w__1612 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1612 6 6 0#1)
  let w__1613 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1613 4 1 0b0000#4)
  let w__1614 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL1 (Sail.BitVec.updateSubrange w__1614 0 0 0#1)
  let w__1615 ← (( do readReg GCSPR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSPR_EL2 (Sail.BitVec.updateSubrange w__1615 2 0 0b000#3)
  let w__1616 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1616 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__1617 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1617 9 9 0#1)
  let w__1618 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1618 8 8 0#1)
  let w__1619 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (BitVec.update w__1619 7 (Bit 0#1))
  let w__1620 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1620 6 6 0#1)
  let w__1621 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1621 4 1 0b0000#4)
  let w__1622 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
  writeReg GCSCR_EL2 (Sail.BitVec.updateSubrange w__1622 0 0 0#1)
  let w__1623 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1623 63 11
    0b00000000000000000000000000000000000000000000000000000#53)
  let w__1624 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1624 10 10 0#1)
  let w__1625 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1625 9 9 0#1)
  let w__1626 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1626 8 8 0#1)
  let w__1627 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1627 7 6 0b00#2)
  let w__1628 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1628 4 1 0b0000#4)
  let w__1629 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
  writeReg GCSCRE0_EL1 (Sail.BitVec.updateSubrange w__1629 0 0 0#1)
  (pure true)


end ArmFull.Functions
