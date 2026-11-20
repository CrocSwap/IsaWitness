module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M1082
public import ArmFull.Fn.M1083
public import ArmFull.Fn.M1084
public import ArmFull.Fn.M1085
public import ArmFull.Fn.M1086
public import ArmFull.Fn.M1087
public import ArmFull.Fn.M1088
public import ArmFull.Fn.M1089
public import ArmFull.Fn.M1090
public import ArmFull.Fn.M1112
public import ArmFull.Fn.M1113
public import ArmFull.Fn.M1114
public import ArmFull.Fn.M1115
public import ArmFull.Fn.M1116
public import ArmFull.Fn.M1117
public import ArmFull.Fn.M1118
public import ArmFull.Fn.M1119
public import ArmFull.Fn.M1120
public import ArmFull.Fn.M1121
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1233
public import ArmFull.Fn.M1234
public import ArmFull.Fn.M1327
public import ArmFull.Fn.M1328
public import ArmFull.Fn.M1329
public import ArmFull.Fn.M1330
public import ArmFull.Fn.M1331
public import ArmFull.Fn.M1332
public import ArmFull.Fn.M1333
public import ArmFull.Fn.M1334
public import ArmFull.Fn.M1335
public import ArmFull.Fn.M1420
public import ArmFull.Fn.M1421
public import ArmFull.Fn.M1422
public import ArmFull.Fn.M1492
public import ArmFull.Fn.M1493
public import ArmFull.Fn.M1494
public import ArmFull.Fn.M1495
public import ArmFull.Fn.M1496
public import ArmFull.Fn.M1497
public import ArmFull.Fn.M1498
public import ArmFull.Fn.M1499
public import ArmFull.Fn.M1500
public import ArmFull.Fn.M1501
public import ArmFull.Fn.M1502
public import ArmFull.Fn.M1503
public import ArmFull.Fn.M1504
public import ArmFull.Fn.M1505
public import ArmFull.Fn.M1506
public import ArmFull.Fn.M1507
public import ArmFull.Fn.M1508
public import ArmFull.Fn.M1509
public import ArmFull.Fn.M1510
public import ArmFull.Fn.M1511
public import ArmFull.Fn.M1512
public import ArmFull.Fn.M1513
public import ArmFull.Fn.M1514
public import ArmFull.Fn.M1515
public import ArmFull.Fn.M1516
public import ArmFull.Fn.M1517
public import ArmFull.Fn.M1518
public import ArmFull.Fn.M1519
public import ArmFull.Fn.M1520
public import ArmFull.Fn.M1528
public import ArmFull.Fn.M1529
public import ArmFull.Fn.M1530
public import ArmFull.Fn.M1531
public import ArmFull.Fn.M1532
public import ArmFull.Fn.M1533
public import ArmFull.Fn.M1534
public import ArmFull.Fn.M1535
public import ArmFull.Fn.M1536
public import ArmFull.Fn.M1537
public import ArmFull.Fn.M1538
public import ArmFull.Fn.M1539
public import ArmFull.Fn.M1540
public import ArmFull.Fn.M1541
public import ArmFull.Fn.M1542
public import ArmFull.Fn.M1543
public import ArmFull.Fn.M1544
public import ArmFull.Fn.M1545
public import ArmFull.Fn.M1546 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: pc : Int -/
def __DecodeA64_LoadStore (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let split_c0 ← (( (__DecodeA64_LoadStore__seg0 pc __opcode) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (__DecodeA64_LoadStore__seg1 pc __opcode) ) : SailM Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (__DecodeA64_LoadStore__seg2 pc __opcode) ) : SailM Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (__DecodeA64_LoadStore__seg3 pc __opcode) ) : SailM Bool )
              if (split_c3 : Bool)
              then
                (do
                  let split_c4 ← (( (__DecodeA64_LoadStore__seg4 pc __opcode) ) : SailM Bool )
                  if (split_c4 : Bool)
                  then
                    (do
                      let split_c5 ← (( (__DecodeA64_LoadStore__seg5 pc __opcode) ) : SailM Bool )
                      if (split_c5 : Bool)
                      then
                        (do
                          let split_c6 ← (( (__DecodeA64_LoadStore__seg6 pc __opcode) ) : SailM
                            Bool )
                          if (split_c6 : Bool)
                          then
                            (do
                              let split_c7 ← (( (__DecodeA64_LoadStore__seg7 pc __opcode) ) :
                                SailM Bool )
                              if (split_c7 : Bool)
                              then (__DecodeA64_LoadStore__seg8 pc __opcode)
                              else (pure ()))
                          else (pure ()))
                      else (pure ()))
                  else (pure ()))
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


/-- Type quantifiers: pc : Int -/
def __DecodeA64_DataProcFPSIMD (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let split_c0 ← (( (__DecodeA64_DataProcFPSIMD__seg0 pc __opcode) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (__DecodeA64_DataProcFPSIMD__seg1 pc __opcode) ) : SailM Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (__DecodeA64_DataProcFPSIMD__seg2 pc __opcode) ) : SailM Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (__DecodeA64_DataProcFPSIMD__seg3 pc __opcode) ) : SailM Bool )
              if (split_c3 : Bool)
              then
                (do
                  let split_c4 ← (( (__DecodeA64_DataProcFPSIMD__seg4 pc __opcode) ) : SailM Bool
                    )
                  if (split_c4 : Bool)
                  then
                    (do
                      let split_c5 ← (( (__DecodeA64_DataProcFPSIMD__seg5 pc __opcode) ) : SailM
                        Bool )
                      if (split_c5 : Bool)
                      then
                        (do
                          let split_c6 ← (( (__DecodeA64_DataProcFPSIMD__seg6 pc __opcode) ) :
                            SailM Bool )
                          if (split_c6 : Bool)
                          then
                            (do
                              let split_c7 ← (( (__DecodeA64_DataProcFPSIMD__seg7 pc __opcode) ) :
                                SailM Bool )
                              if (split_c7 : Bool)
                              then
                                (do
                                  let split_c8 ← (( (__DecodeA64_DataProcFPSIMD__seg8 pc __opcode)
                                    ) : SailM Bool )
                                  if (split_c8 : Bool)
                                  then
                                    (do
                                      let split_c9 ← ((
                                        (__DecodeA64_DataProcFPSIMD__seg9 pc __opcode) ) : SailM
                                        Bool )
                                      if (split_c9 : Bool)
                                      then
                                        (do
                                          let split_c10 ← ((
                                            (__DecodeA64_DataProcFPSIMD__seg10 pc __opcode) ) :
                                            SailM Bool )
                                          if (split_c10 : Bool)
                                          then
                                            (do
                                              let split_c11 ← ((
                                                (__DecodeA64_DataProcFPSIMD__seg11 pc __opcode) ) :
                                                SailM Bool )
                                              if (split_c11 : Bool)
                                              then
                                                (do
                                                  let split_c12 ← ((
                                                    (__DecodeA64_DataProcFPSIMD__seg12 pc __opcode)
                                                    ) : SailM Bool )
                                                  if (split_c12 : Bool)
                                                  then
                                                    (do
                                                      let split_c13 ← ((
                                                        (__DecodeA64_DataProcFPSIMD__seg13 pc
                                                          __opcode) ) : SailM Bool )
                                                      if (split_c13 : Bool)
                                                      then
                                                        (do
                                                          let split_c14 ← ((
                                                            (__DecodeA64_DataProcFPSIMD__seg14 pc
                                                              __opcode) ) : SailM Bool )
                                                          if (split_c14 : Bool)
                                                          then
                                                            (__DecodeA64_DataProcFPSIMD__seg15 pc
                                                              __opcode)
                                                          else (pure ()))
                                                      else (pure ()))
                                                  else (pure ()))
                                              else (pure ()))
                                          else (pure ()))
                                      else (pure ()))
                                  else (pure ()))
                              else (pure ()))
                          else (pure ()))
                      else (pure ()))
                  else (pure ()))
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


/-- Type quantifiers: pc : Int -/
def __DecodeA32_Unconditional (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let split_c0 ← (( (__DecodeA32_Unconditional__seg0 pc __opcode) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (__DecodeA32_Unconditional__seg1 pc __opcode) ) : SailM Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (__DecodeA32_Unconditional__seg2 pc __opcode) ) : SailM Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (__DecodeA32_Unconditional__seg3 pc __opcode) ) : SailM Bool )
              if (split_c3 : Bool)
              then
                (do
                  let split_c4 ← (( (__DecodeA32_Unconditional__seg4 pc __opcode) ) : SailM Bool )
                  if (split_c4 : Bool)
                  then
                    (do
                      let split_c5 ← (( (__DecodeA32_Unconditional__seg5 pc __opcode) ) : SailM
                        Bool )
                      if (split_c5 : Bool)
                      then (__DecodeA32_Unconditional__seg6 pc __opcode)
                      else (pure ()))
                  else (pure ()))
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


/-- Type quantifiers: pc : Int -/
def __DecodeA32_DataProMisc (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let split_c0 ← (( (__DecodeA32_DataProMisc__seg0 pc __opcode) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (__DecodeA32_DataProMisc__seg1 pc __opcode) ) : SailM Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (__DecodeA32_DataProMisc__seg2 pc __opcode) ) : SailM Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (__DecodeA32_DataProMisc__seg3 pc __opcode) ) : SailM Bool )
              if (split_c3 : Bool)
              then (__DecodeA32_DataProMisc__seg4 pc __opcode)
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


def ExecuteT16 (instr : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do readReg _PC ) : SailM (BitVec 64) )
  (__DecodeT16 (BitVec.toNat w__0) instr)


/-- Type quantifiers: t : Int -/
def AArch64_AutoGen_SysRegRead (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let split_c0 ← (( (AArch64_AutoGen_SysRegRead__seg0 el op0 op1 CRn op2 CRm t) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (AArch64_AutoGen_SysRegRead__seg1 el op0 op1 CRn op2 CRm t) ) : SailM Bool
        )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (AArch64_AutoGen_SysRegRead__seg2 el op0 op1 CRn op2 CRm t) ) : SailM
            Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (AArch64_AutoGen_SysRegRead__seg3 el op0 op1 CRn op2 CRm t) ) :
                SailM Bool )
              if (split_c3 : Bool)
              then
                (do
                  let split_c4 ← (( (AArch64_AutoGen_SysRegRead__seg4 el op0 op1 CRn op2 CRm t) )
                    : SailM Bool )
                  if (split_c4 : Bool)
                  then
                    (do
                      let split_c5 ← ((
                        (AArch64_AutoGen_SysRegRead__seg5 el op0 op1 CRn op2 CRm t) ) : SailM Bool )
                      if (split_c5 : Bool)
                      then
                        (do
                          let split_c6 ← ((
                            (AArch64_AutoGen_SysRegRead__seg6 el op0 op1 CRn op2 CRm t) ) : SailM
                            Bool )
                          if (split_c6 : Bool)
                          then
                            (do
                              let split_c7 ← ((
                                (AArch64_AutoGen_SysRegRead__seg7 el op0 op1 CRn op2 CRm t) ) :
                                SailM Bool )
                              if (split_c7 : Bool)
                              then
                                (do
                                  let split_c8 ← ((
                                    (AArch64_AutoGen_SysRegRead__seg8 el op0 op1 CRn op2 CRm t) ) :
                                    SailM Bool )
                                  if (split_c8 : Bool)
                                  then (AArch64_AutoGen_SysRegRead__seg9 el op0 op1 CRn op2 CRm t)
                                  else (pure ()))
                              else (pure ()))
                          else (pure ()))
                      else (pure ()))
                  else (pure ()))
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


/-- Type quantifiers: t : Int -/
def AArch64_AutoGen_SysRegWrite (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let split_c0 ← (( (AArch64_AutoGen_SysRegWrite__seg0 el op0 op1 CRn op2 CRm t) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (AArch64_AutoGen_SysRegWrite__seg1 el op0 op1 CRn op2 CRm t) ) : SailM
        Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (AArch64_AutoGen_SysRegWrite__seg2 el op0 op1 CRn op2 CRm t) ) : SailM
            Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (AArch64_AutoGen_SysRegWrite__seg3 el op0 op1 CRn op2 CRm t) ) :
                SailM Bool )
              if (split_c3 : Bool)
              then
                (do
                  let split_c4 ← (( (AArch64_AutoGen_SysRegWrite__seg4 el op0 op1 CRn op2 CRm t) )
                    : SailM Bool )
                  if (split_c4 : Bool)
                  then
                    (do
                      let split_c5 ← ((
                        (AArch64_AutoGen_SysRegWrite__seg5 el op0 op1 CRn op2 CRm t) ) : SailM Bool
                        )
                      if (split_c5 : Bool)
                      then
                        (do
                          let split_c6 ← ((
                            (AArch64_AutoGen_SysRegWrite__seg6 el op0 op1 CRn op2 CRm t) ) : SailM
                            Bool )
                          if (split_c6 : Bool)
                          then (AArch64_AutoGen_SysRegWrite__seg7 el op0 op1 CRn op2 CRm t)
                          else (pure ()))
                      else (pure ()))
                  else (pure ()))
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


/-- Type quantifiers: crm : Int, crn : Int, op0 : Int, op1 : Int, op2 : Int, t : Int -/
def AArch64_SysInstr (op0 : Int) (op1 : Int) (crn : Int) (crm : Int) (op2 : Int) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  (AArch64_AutoGen_SysOpsWrite w__0.EL (integer_subrange op0 1 0) (integer_subrange op1 2 0)
    (integer_subrange crn 3 0) (integer_subrange op2 2 0) (integer_subrange crm 3 0) t)


def decode_aarch32_instrs_LDC_i_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:3431.29-3431.30"
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDC (literal)"))
      else (pure (()))
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let cp : Nat := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      (execute_aarch32_instrs_LDC_i_Op_A_txt add cp imm32 index (Sail.Int.toNatChecked (n)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDC_i_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((Rn == 0b1111#4) : Bool)
      then sailThrow ((Error_See "LDC (literal)"))
      else (pure (()))
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let cp : Nat := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      (execute_aarch32_instrs_LDC_i_Op_A_txt add cp imm32 index (Sail.Int.toNatChecked (n)) wback))
  else (pure (()))


def decode_aarch32_instrs_LDC_l_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:3507.29-3507.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let cp : Nat := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let w__3 ← (( do
        if (((W == 1#1) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((P == 0#1) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
                (pure (((bne w__1 InstrSet_A32) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDC_l_Op_A_txt add cp imm32 index))
  else (pure (()))


def decode_aarch32_instrs_LDC_l_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let cp : Nat := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let w__3 ← (( do
        if (((W == 1#1) : Bool) : Bool)
        then (pure true)
        else
          (do
            if (((P == 0#1) : Bool) : Bool)
            then
              (do
                let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
                (pure (((bne w__1 InstrSet_A32) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_LDC_l_Op_A_txt add cp imm32 index))
  else (pure (()))


def decode_aarch32_instrs_STC_A1enc_A_txt (cond : (BitVec 4)) (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:13365.29-13365.30"
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let cp : Nat := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let w__3 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          if (wback : Bool)
          then (pure true)
          else
            (do
              let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
              (pure (((bne w__1 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STC_Op_A_txt add cp imm32 index (Sail.Int.toNatChecked (n)) wback))
  else (pure (()))


def decode_aarch32_instrs_STC_T1enc_A_txt (P : (BitVec 1)) (U : (BitVec 1)) (W : (BitVec 1)) (Rn : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if ((((P == 0#1) && (U == 0#1)) && (W == 0#1)) : Bool)
      then sailThrow ((Error_Undefined ()))
      else (pure (()))
      let n : Int := (BitVec.toNat Rn)
      let cp : Nat := 14
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let index : Bool := (P == 1#1)
      let add : Bool := (U == 1#1)
      let wback : Bool := (W == 1#1)
      let w__3 ← (( do
        if (((n == 15) : Bool) : Bool)
        then
          if (wback : Bool)
          then (pure true)
          else
            (do
              let w__1 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
              (pure (((bne w__1 InstrSet_A32) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_STC_Op_A_txt add cp imm32 index (Sail.Int.toNatChecked (n)) wback))
  else (pure (()))


/-- Type quantifiers: k_read : Bool, sys_crm : Nat, sys_crn : Nat, sys_op0 : Nat, sys_op1 : Nat, sys_op2
  : Nat, t : Nat, t2 : Nat, 0 ≤ t2 ∧
  t2 ≤ 31 ∧
  0 ≤ t ∧
  t ≤ 31 ∧
  List.elem sys_op2 [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem sys_op1 [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem sys_op0 [2, 3] ∧ 0 ≤ sys_crn ∧ sys_crn ≤ 15 ∧ 0 ≤ sys_crm ∧ sys_crm ≤ 15 -/
def execute_aarch64_instrs_system_register_system_128 (read : Bool) (sys_crm : Nat) (sys_crn : Nat) (sys_op0 : Nat) (sys_op1 : Nat) (sys_op2 : Nat) (t : Nat) (t2 : Nat) : SailM Unit := do
  if (read : Bool)
  then
    (do
      (AArch64_SysRegRead128 sys_op0 sys_op1 sys_crn sys_crm sys_op2 t t2))
  else
    (do
      (AArch64_SysRegWrite128 sys_op0 sys_op1 sys_crn sys_crm sys_op2 t t2))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_SVE (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let split_c0 ← (( (__DecodeA64_SVE__seg0 pc __opcode) ) : SailM Bool )
  if (split_c0 : Bool)
  then
    (do
      let split_c1 ← (( (__DecodeA64_SVE__seg1 pc __opcode) ) : SailM Bool )
      if (split_c1 : Bool)
      then
        (do
          let split_c2 ← (( (__DecodeA64_SVE__seg2 pc __opcode) ) : SailM Bool )
          if (split_c2 : Bool)
          then
            (do
              let split_c3 ← (( (__DecodeA64_SVE__seg3 pc __opcode) ) : SailM Bool )
              if (split_c3 : Bool)
              then
                (do
                  let split_c4 ← (( (__DecodeA64_SVE__seg4 pc __opcode) ) : SailM Bool )
                  if (split_c4 : Bool)
                  then
                    (do
                      let split_c5 ← (( (__DecodeA64_SVE__seg5 pc __opcode) ) : SailM Bool )
                      if (split_c5 : Bool)
                      then
                        (do
                          let split_c6 ← (( (__DecodeA64_SVE__seg6 pc __opcode) ) : SailM Bool )
                          if (split_c6 : Bool)
                          then
                            (do
                              let split_c7 ← (( (__DecodeA64_SVE__seg7 pc __opcode) ) : SailM Bool
                                )
                              if (split_c7 : Bool)
                              then
                                (do
                                  let split_c8 ← (( (__DecodeA64_SVE__seg8 pc __opcode) ) : SailM
                                    Bool )
                                  if (split_c8 : Bool)
                                  then
                                    (do
                                      let split_c9 ← (( (__DecodeA64_SVE__seg9 pc __opcode) ) :
                                        SailM Bool )
                                      if (split_c9 : Bool)
                                      then
                                        (do
                                          let split_c10 ← (( (__DecodeA64_SVE__seg10 pc __opcode)
                                            ) : SailM Bool )
                                          if (split_c10 : Bool)
                                          then
                                            (do
                                              let split_c11 ← ((
                                                (__DecodeA64_SVE__seg11 pc __opcode) ) : SailM Bool
                                                )
                                              if (split_c11 : Bool)
                                              then
                                                (do
                                                  let split_c12 ← ((
                                                    (__DecodeA64_SVE__seg12 pc __opcode) ) : SailM
                                                    Bool )
                                                  if (split_c12 : Bool)
                                                  then
                                                    (do
                                                      let split_c13 ← ((
                                                        (__DecodeA64_SVE__seg13 pc __opcode) ) :
                                                        SailM Bool )
                                                      if (split_c13 : Bool)
                                                      then
                                                        (do
                                                          let split_c14 ← ((
                                                            (__DecodeA64_SVE__seg14 pc __opcode) ) :
                                                            SailM Bool )
                                                          if (split_c14 : Bool)
                                                          then
                                                            (do
                                                              let split_c15 ← ((
                                                                (__DecodeA64_SVE__seg15 pc __opcode)
                                                                ) : SailM Bool )
                                                              if (split_c15 : Bool)
                                                              then
                                                                (do
                                                                  let split_c16 ← ((
                                                                    (__DecodeA64_SVE__seg16 pc
                                                                      __opcode) ) : SailM Bool )
                                                                  if (split_c16 : Bool)
                                                                  then
                                                                    (do
                                                                      let split_c17 ← ((
                                                                        (__DecodeA64_SVE__seg17 pc
                                                                          __opcode) ) : SailM Bool )
                                                                      if (split_c17 : Bool)
                                                                      then
                                                                        (do
                                                                          let split_c18 ← ((
                                                                            (__DecodeA64_SVE__seg18
                                                                              pc __opcode) ) : SailM
                                                                            Bool )
                                                                          if (split_c18 : Bool)
                                                                          then
                                                                            (do
                                                                              let split_c19 ← ((
                                                                                (__DecodeA64_SVE__seg19
                                                                                  pc __opcode) ) :
                                                                                SailM Bool )
                                                                              if (split_c19 : Bool)
                                                                              then
                                                                                (do
                                                                                  let split_c20 ← ((
                                                                                    (__DecodeA64_SVE__seg20
                                                                                      pc __opcode) )
                                                                                    : SailM Bool )
                                                                                  if (split_c20 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      let split_c21 ← ((
                                                                                        (__DecodeA64_SVE__seg21
                                                                                          pc
                                                                                          __opcode)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (split_c21 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          let split_c22 ← ((
                                                                                            (__DecodeA64_SVE__seg22
                                                                                              pc
                                                                                              __opcode)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (split_c22 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              let split_c23 ← ((
                                                                                                (__DecodeA64_SVE__seg23
                                                                                                  pc
                                                                                                  __opcode)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (split_c23 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  let split_c24 ← ((
                                                                                                    (__DecodeA64_SVE__seg24
                                                                                                      pc
                                                                                                      __opcode)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (split_c24 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      let split_c25 ← ((
                                                                                                        (__DecodeA64_SVE__seg25
                                                                                                          pc
                                                                                                          __opcode)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (split_c25 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          let split_c26 ← ((
                                                                                                            (__DecodeA64_SVE__seg26
                                                                                                              pc
                                                                                                              __opcode)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (split_c26 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              let split_c27 ← ((
                                                                                                                (__DecodeA64_SVE__seg27
                                                                                                                  pc
                                                                                                                  __opcode)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (split_c27 : Bool)
                                                                                                              then
                                                                                                                (__DecodeA64_SVE__seg28
                                                                                                                  pc
                                                                                                                  __opcode)
                                                                                                              else
                                                                                                                (pure ()))
                                                                                                          else
                                                                                                            (pure ()))
                                                                                                      else
                                                                                                        (pure ()))
                                                                                                  else
                                                                                                    (pure ()))
                                                                                              else
                                                                                                (pure ()))
                                                                                          else
                                                                                            (pure ()))
                                                                                      else (pure ()))
                                                                                  else (pure ()))
                                                                              else (pure ()))
                                                                          else (pure ()))
                                                                      else (pure ()))
                                                                  else (pure ()))
                                                              else (pure ()))
                                                          else (pure ()))
                                                      else (pure ()))
                                                  else (pure ()))
                                              else (pure ()))
                                          else (pure ()))
                                      else (pure ()))
                                  else (pure ()))
                              else (pure ()))
                          else (pure ()))
                      else (pure ()))
                  else (pure ()))
              else (pure ()))
          else (pure ()))
      else (pure ()))
  else (pure ())


end ArmFull.Functions
