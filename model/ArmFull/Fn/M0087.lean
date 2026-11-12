import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0001

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

def execute_aarch64_instrs_integer_flags_xaflag (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let n : (BitVec 1) := ((Complement.complement w__0.C) &&& (Complement.complement w__1.Z))
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
  let z : (BitVec 1) := (w__2.Z &&& w__3.C)
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
  let c : (BitVec 1) := (w__4.C ||| w__5.Z)
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  let v : (BitVec 1) := ((Complement.complement w__6.C) &&& w__7.Z)
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__8 with N := n }
  let w__9 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__9 with Z := z }
  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__10 with C := c }
  let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
  writeReg PSTATE { w__11 with V := v }


/-- Type quantifiers: x_0 : Int -/
def __DecodeA64_Unallocated1 (x_0 : Int) (x_1 : (BitVec 32)) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: x_0 : Int -/
def __DecodeA64_Unallocated2 (x_0 : Int) (x_1 : (BitVec 32)) : SailM Unit := do
  sailThrow ((Error_Undefined ()))


def __SetThisInstrDetails (enc : __InstrEnc) (opcode : (BitVec 32)) (cond : (BitVec 4)) : SailM Unit := do
  writeReg __ThisInstrEnc enc
  writeReg __ThisInstr opcode
  writeReg __currentCond cond


def __CheckForEmulatorTermination (enc : __InstrEnc) (instr : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do readReg __emulator_termination_opcode ) : SailM (Option (BitVec 32)) )
  match w__0 with
  | .some magic =>
    (do
      if ((instr == magic) : Bool)
      then
        (do
          let _ : Unit :=
            (print
              (String.append
                (String.append "[Sail] Terminating emulation at opcode " (BitVec.toFormatted magic))
                "
"))
          throw Error.Exit)
      else (pure (())))
  | none => (pure (()))


def __EndCycle (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg __cycle_count ) : SailM Int )
  writeReg __cycle_count (w__0 +i 1)


def __ListConfig (_ : Unit) : Unit :=
  let _ : Unit :=
    (print_endline
      "cpu.has_arm_v8-1=0 (bool) default = '0'\n        : Implement the ARMv8.1 Extension.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_arm_v8-2=0 (bool) default = '0'\n        : Implement the ARMv8.2 Extension.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_arm_v8-3=0 (bool) default = '0'\n        : Implement the ARMv8.3 Extension.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_arm_v8-4=0 (bool) default = '0'\n        : Implement the ARMv8.4 Extension. This feature is incomplete and under development.\n")
  let _ : Unit :=
    (print_endline
      "cpu.num_loregions=0x0 (int) default = '0x0' \n        : Number of Limited Ordering Regions implemented excluding background region (if ARM v8.1 extensions are implemented) : [0x0..0xFF]\n")
  let _ : Unit :=
    (print_endline
      "cpu.num_loregion_descriptors=0x0 (int) default = '0x0'\n        : Number of Limited Ordering Region descriptors implemented (if ARM v8.1 extensions are implemented) : [0x0..0xFF]\n")
  let _ : Unit :=
    (print_endline
      "cpu.PA_SIZE=0x30 (int) default = '0x30'\n        : Physical address range supported.  For ARMv8.0 and ARMv8.1 this is limited to 48 bits. : [0x20..0x34]\n")
  let _ : Unit :=
    (print_endline
      "counter_addr=0x0 (int) default = '0x0'\n        : Address for memory-mapped system counter block.  0 means the counter is not mapped, otherwise the address must be 4KB aligned.\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_normal_cacheable_read_is_sync=1 (bool) default = '1' \n        : Synchronous reporting of normal write-back cacheable-read External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_normal_noncacheable_read_is_sync=1 (bool) default = '1'\n        : Synchronous reporting of normal noncacheable-read External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_device_read_is_sync=1 (bool) default = '1'\n        : Synchronous reporting of device-nGnRE read External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_so_read_is_sync=1 (bool) default = '1'\n        : Synchronous reporting of device-nGnRnE read External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_so_write_is_sync=1 (bool) default = '1'\n        : Synchronous reporting of device-nGnRnE write External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_prefetch_is_sync=1 (bool) default = '1'\n        : Behavior of External aborts generated by normal writeback cacheable instruction fetches.\n        [0, 1], 0: asynchronous abort,  1: synchronous abort.\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_ttw_cacheable_read_is_sync=1 (bool) default = '1'\n        : Synchronous reporting of TTW cacheable read External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_ttw_noncacheable_read_is_sync=1 (bool) default = '1'\n        : Synchronous reporting of TTW noncacheable read External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_normal_cacheable_write_is_sync=0 (bool) default = '0'\n        : Synchronous reporting of normal write-back cacheable write External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_normal_noncacheable_write_is_sync=0 (bool) default = '0'\n        : Synchronous reporting of normal noncacheable write External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.ext_abort_device_write_is_sync=0 (bool) default = '0'\n        : Synchronous reporting of device-nGnRE write External aborts\n")
  let _ : Unit :=
    (print_endline
      "cpu.unpred_tsize_aborts=0 (bool) default = '0'\n        : Behavior when TSize is out of range.\n        [0, 1], 0: force into range. 1: translation fault, forces unpred_tsize_pamax_aborts to 1.\n")
  let _ : Unit :=
    (print_endline "cpu.isb_is_branch=1 (bool) default='1'\n        : ISB is treated as branch")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.enable_crc32=0x0 (int) default = '0x0'\n        : CRC32 instructions supported.\n        [0, 1], 0: CRC32 not implemented. 1: CRC32 instructions implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_pstate_pan=0x1 (int) default = '0x1' \n        : Implement the PSTATE.PAN (Privileged Access Never) control from ARMv8.1.\n        [0, 1], 0: not implemented. 1: Implemented\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_16bit_vmids=0x1 (int) default = '0x1'\n        : Implement support for 16-bit VMIDs from ARMv8.1\n        [0, 1], 0: Not enabled, 1: Implemented\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_dot_product=0x1 (int) default = '0x1' \n        : Implement the dot product (UDOT, SDOT) instructions from ARMv8.4\n        [0, 1], 0: Not implemnetd, 1: Implemnetd\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_fp16=0x1 (int) default = '0x1' \n        : Implement the half-precision floating-point data processing instructions from ARMv8.2.\n        [0, 1] 0: feature is not enabled. 1: feature is implemented\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_aarch32_hpd=0 (bool) default = '0'\n        : If true then hierarchical permission disable is supported in AArch32\n")
  let _ : Unit :=
    (print_endline "cpu.has_tlb=0x1 (bool) default = '1'\n        : If true then TLB is enabled\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_trickbox=0x1 (bool) default = '1'\n        : If true then Trickbox and abort region checks are enabled\n")
  let _ : Unit :=
    (print_endline
      "cpu.VAL_ignore_rvbar_in_aarch32=0  default = '0'\n        : If '1', ignore RVBAR while determining reset vector in AArch32. This is required for ACK tests \n")
  let _ : Unit :=
    (print_endline
      "SVE.ScalableVectorExtension.sme_veclens_implemented=7  (int) default = '0x7'\n        : Implies which SME vector lengths are implemented: represented as a bitfield where bit[n]==1 implies SME vector length of 128*2^n bits is implemented \n")
  let _ : Unit :=
    (print_endline
      "SVE.ScalableVectorExtension.veclen=0x20  (int) default = '0x20'\n        : Implies which non streaming SVE vector lengths are implemented: size of vector in uints of 64 bits \n")
  let _ : Unit :=
    (print_endline
      "SVE.ScalableVectorExtension.has_sme=1  (bool) default = '1'\n        : If SME is implemented or not\n")
  let _ : Unit :=
    (print_endline
      "SVE.ScalableVectorExtension.sme_only=0  (bool) default = '0'\n        : Where SME is implemented, whether SVE functionality is available only when SM=1 \n")
  let _ : Unit :=
    (print_endline
      "SVE.ScalableVectorExtension.has_sme_priority_control=1  (bool) default = '1'\n        : Whether SME prioirty Control is implemented \n")
  let _ : Unit :=
    (print_endline
      "SVE.ScalableVectorExtension.has_sme_f64f64=1  (bool) default = '1'\n        : Where SME is implemented, whether double precision FMOPA and FMOPS are implemented \n")
  let _ : Unit :=
    (print_endline
      "SVE.ScalableVectorExtension.has_sme_i16i64=1  (bool) default = '1'\n        : Where SME is implemented, whether instructions that accumulate 16-bit integer outer products into 64-bit integer tiles are implemented \n")
  let _ : Unit :=
    (print_endline
      "SVE.ScalableVectorExtension.has_sve_extended_bf16=0x2  (int) default = '0x2'\n        : Whether Extended BFloat16 instructions are implemented: 0 - Disabled, 1 - Enabled, 2 - Enabled if SME is implemented \n")
  let _ : Unit :=
    (print_endline
      "cpu.has_extended_recp_estimate=0x0  (int) default = '0x1'\n        : Whether increased Reciprocal Estimate and Square Root Estimate precision is supported: 0 - Disabled, 1 - Enabled  \n")
  let _ : Unit :=
    (print_endline
      "cpu.has_mpam=1 (bool) default = 0\n        : Implement the MPAM extension.\n        [0, 1] 0: FALSE, not implemented. 1: TRUE, implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_mpamhcr=1 (bool) default = 1\n        : If MPAM is implemented, also implement the MPAM virtualization features.\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.mpam_partid_max=127 (int) default = 0\n        : [0 .. 65535] Maximum MPAM PARTID supported by the implementation.")
  let _ : Unit :=
    (print_endline
      "cpu.mpam_pmg_max=3 (int) default = 0\n        : [0 .. 255] Maximum MPAM PMG supported by the implementation.\n")
  let _ : Unit :=
    (print_endline
      "cpu.mpam_vpmr_max=2 (int) default = 0\n        : [0 .. 7] Maximum MPAM virtual PARTID mapping register implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.mpam_has_altsp=1 (int) default = 1\n        : [0, 1] Whether MPAMIDR_EL1.HAS_ALTSP is set or cleared.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_empam=1 (bool) default = 0\n        : Implement the Enhanced MPAM extension.\n        [0, 1] 0: FALSE, not implemented. 1: TRUE, implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.empam_has_tidr (bool) default = 0\n        : Implement the MPAM2_EL2.TIDR bit to trap MPAMIDR_EL1.\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.empam_has_sdeflt (bool) default = 0\n        : Implement the MPAM3_EL3.SDEFLT bit to generate only the default PARTID in Secure execution.\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.empam_has_force_ns (bool) default = 0\n        : Implement the MPAMe_EL3.FORCE_NS bit to generate Non-secure PARTIDs in Secure execution.\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.empam_force_ns_RAO (bool) default = 0\n        : Implement the MPAM3_EL3.FORCE_NS bit as Read-as-One.\n        [0, 1] 0: FALSE, not implemented.  1: TRUE, implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.crypto_aes=0x2 (int) default = '0x2'\n        : AES and 128 bit PMULL instructions supported.\n        [0, 1, 2], 0: AES instruction not implemented. 1: AES instruction implemented. 2: AES plus 128bit PMULL instruction implemented\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.crypto_sha1=0x1 (int) default = '0x1'\n        : SHA1 instructions supported.\n        [0, 1], 0: SHA1 not implemented. 1: SHA1 instructions implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.crypto_sha256=0x1 (int) default = '0x1'\n        : SHA256 instructions supported.\n        [0, 1], 0: SHA256 not implemented. 1: SHA256 instructions implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.crypto_sha512=0x0 (int) default = '0x0'\n        : SHA512 instructions supported.\n        [0, 1], 0: SHA512 not implemented. 1: SHA512 instructions implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.crypto_sha3=0x0 (int) default = '0x0'\n        : SHA3 instructions supported.\n        [0, 1], 0: SHA3 not implemented. 1: SHA3 instructions implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.crypto_sm3=0x0 (int) default = '0x0'\n        : SM3 instructions supported.\n        [0, 1], 0: SM3 not implemented. 1: SM3 instructions implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.crypto_sm4=0x0 (int) default = '0x0'\n        : SM4 instructions supported.\n        [0, 1], 0: SM4 not implemented. 1: SM4 instructions implemented.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.number-of-breakpoints=0x10 (int) default='0x10'\n        : [1 .. 16] Number of breakpoints.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.number-of-context-breakpoints=0x10 (int) default='0x10'\n        : [1 .. 16] Number of breakpoints that are context aware.\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.number-of-watchpoints=0x10 (int) default='0x10'\n        : [1 .. 16] Number of watchpoints.\n")
  let _ : Unit :=
    (print_endline
      "cpu.pmu-num_counters=0x1f (int) default='0x1f'\n        : [1 .. 16] Number of event counters.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_brbe=0x1 (int) default='0x1'\n        : Branch Record Buffer Extension supported.\n        [0, 1], 0 Not implemented, 1: Implemented\n")
  let _ : Unit :=
    (print_endline
      "cpu.cpu0.number-of-branch-records=0x40 (int) default='0x40'\n        : [16, 32, 48, 64] Number of BRB records.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_mops_option=0x1 (int) default='0x1'\n        : FEAT_MOPS uses option A or B. \n        [1, 2], 1 FEAT_MOPS uses option A, 2 FEAT_MOPS uses option B\n")
  let _ : Unit :=
    (print_endline
      "cpu.mops_cpy_default_dir=0 (int) default='0x0'\n        : CPY* instructions copy in forward/backward direction in non-overlapping case,\n        [0, 1], 0 forward direction,  1 backward direction.\n")
  let _ : Unit :=
    (print_endline
      "cpu.has_brbe_v9_3=0x1 (int) default='0x1'\n        :if 1, implements FEAT_BRBEv1p1.\n")
  let _ : Unit :=
    (print_endline
      "spe.pseudo_cycles=0 (bool) default=0 \n        :if 1, extra cycles are generated on memory reads and writes.\n")
  let _ : Unit :=
    (print_endline
      "ZCR_EL3.LEN=0xf (int) default=UNKNOWN \n        :Specify the vector size of VL at EL3.\n")
  let _ : Unit :=
    (print_endline
      "CPTR_EL3.EZ=0x1 (int) default=UNKNOWN \n        :Enable Trap for non-streaming mode SVE instructions.\n")
  let _ : Unit :=
    (print_endline
      "CPTR_EL3.ESM=0x1 (int) default=UNKNOWN \n        :Enable Trap for SME instructions.\n")
  (print_endline
    "SMCR_EL3.LEN=0xf (int) default=UNKNOWN \n        :Specify the effective streaming vector length.\n")


/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m *i (fdiv_int n m)))


/-- Type quantifiers: i : Int, n : Int -/
def integer_access (i : Int) (n : Int) : (BitVec 1) :=
  (BitVec.access (integer_subrange i n n) 0)


/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if ((l ≥b n) : Bool)
  then (Sail.BitVec.castWidth ((sail_ones n) <<< i))
  else
    (let one : (BitVec n) := (Sail.BitVec.castWidth (sail_mask n (1#1 : (BitVec 1))))
    (Sail.BitVec.castWidth (((one <<< l) - one) <<< i)))


/-- Type quantifiers: n : Nat, n > 0 -/
def to_bytes_le {n : _} (b : (BitVec (8 * n))) : (Vector (BitVec 8) n) := Id.run do
  let res := (vectorInit (BitVec.zero 8))
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := (Sail.Int.toNatChecked ((n -i 1)))
  (do
    let mut loop_vars := res
    for i in [loop_i_lower:loop_i_upper:1]i do
      let res := loop_vars
      loop_vars :=
        (vectorUpdate res (Sail.Int.toNatChecked (i))
          (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb b
            (Sail.Int.toNatChecked (((8 *i i) +i 7))) (Sail.Int.toNatChecked ((8 *i i))))))
    (pure loop_vars))


/-- Type quantifiers: n : Nat, n > 0 -/
def from_bytes_le {n : _} (v : (Vector (BitVec 8) n)) : (BitVec (8 * n)) := Id.run do
  let res := (BitVec.zero (Sail.Int.toNatChecked ((8 *i n))))
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := (Sail.Int.toNatChecked ((n -i 1)))
  ((Sail.BitVec.castWidth ) <$> (do
    let mut loop_vars := res
    for i in [loop_i_lower:loop_i_upper:1]i do
      let res := loop_vars
      loop_vars :=
        (Sail.BitVec.updateSubrange res (Sail.Int.toNatChecked (((8 *i i) +i 7)))
          (Sail.Int.toNatChecked ((8 *i i)))
          (Sail.BitVec.castWidth (GetElem?.getElem! v (Sail.Int.toNatChecked (i)))))
    (pure loop_vars)))


/-- Type quantifiers: m : Int, n : Nat, n ≥ 0 -/
def zext_ones {n : _} (m : Int) : (BitVec n) :=
  let v : (BitVec n) :=
    (Sail.BitVec.castWidth (extsv (m := (Sail.Int.toNatChecked (n))) (1#1 : (BitVec 1))))
  (Sail.BitVec.castWidth (v >>> (n -i m)))


/-- Type quantifiers: k_a : Type -/
def sail_ignore_write_to (reg : (RegisterRef k_a)) : Unit :=
  (sail_mark_register reg "ignore_write")


/-- Type quantifiers: k_a : Type -/
def sail_pick_dependency (reg : (RegisterRef k_a)) : Unit :=
  (sail_mark_register reg "pick")


def undefined_Explicit_access_kind (ℓ : ChoiceLabel) (_ : Unit) : SailM Explicit_access_kind := do
  let w__0 ← (( do (undefined_Access_variety (ℓ.child 0) ()) ) : SailM Access_variety )
  let w__1 ← (( do (undefined_Access_strength (ℓ.child 1) ()) ) : SailM Access_strength )
  (pure ({ variety := w__0
           strength := w__1 }))


/-- Type quantifiers: k_ex10455120_ : Bool, k_ex10455119_ : Bool -/
def iff (p : Bool) (q : Bool) : Bool :=
  ((implies p q) && (implies q p))


/-- Type quantifiers: n : Nat, n ≥ 0 -/
def Ones {n : _} : (BitVec n) :=
  (Sail.BitVec.castWidth (sail_ones n))


/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def IsOnes (x : (BitVec k_n)) : Bool :=
  (x == (Sail.BitVec.castWidth (sail_ones (Sail.BitVec.length x))))


/-- Type quantifiers: y : Int, x : Int -/
def Align_int (x : Int) (y : Int) : Int :=
  ((fdiv_int x y) *i y)


/-- Type quantifiers: n : Nat, n ≥ 0 -/
def __UNKNOWN_bits (n : Nat) : SailM (BitVec n) := do
  ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 6) (Sail.Int.toNatChecked (n))))


def __UNKNOWN_signal (_ : Unit) : SailM signal := do
  (undefined_signal (.site 12) ())


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def IsZeroBit (x : (BitVec k_N)) : (BitVec 1) :=
  if ((IsZero x) : Bool)
  then 1#1
  else 0#1


/-- Type quantifiers: k_N : Nat, shift : Nat, k_N ≥ 0 ∧ shift ≥ 0 -/
def ASR_C (x : (BitVec k_N)) (shift : Nat) : ((BitVec k_N) × (BitVec 1)) :=
  let carry_out :=
    if (((shift == 0) || ((Sail.BitVec.length x) == 0)) : Bool)
    then 0#1
    else
      (if ((shift ≥b (Sail.BitVec.length x)) : Bool)
      then (BitVec.access x (Sail.Int.toNatChecked (((Sail.BitVec.length x) -i 1))))
      else (BitVec.access x (Sail.Int.toNatChecked ((shift -i 1)))))
  ((BitVec.sshiftRight x shift), (BitVec.setWidth 1 (BitVec.join1 [carry_out])))


/-- Type quantifiers: k_M : Nat, N : Nat, k_is_unsigned : Bool, k_M ≥ 0 ∧ N ≥ 0 -/
def Extend (x : (BitVec k_M)) (N : Nat) (is_unsigned : Bool) : SailM (BitVec N) := do
  if (is_unsigned : Bool)
  then
    (do
      ArmFull.assert (((Sail.BitVec.length x) ≥b 0) && (N ≥b (Sail.BitVec.length x))) "sail-arm/builtins.sail:121.47-121.48"
      (pure ((Sail.BitVec.castWidth (Sail.BitVec.zeroExtend x N)))))
  else
    (do
      ArmFull.assert (((Sail.BitVec.length x) >b 0) && (N ≥b (Sail.BitVec.length x))) "sail-arm/builtins.sail:124.46-124.47"
      (pure ((Sail.BitVec.castWidth (sign_extend x N)))))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def LowestSetBit (x : (BitVec k_N)) : Int := ExceptM.run do
  let loop_i_lower : Nat := 0
  let loop_i_upper : Int := ((Sail.BitVec.length x) -i 1)
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access x (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
        then
          (do
            throw (i : Int))
        else (pure (()))
    (pure loop_vars))
  (pure ((Sail.BitVec.length x)))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def HighestSetBit (x : (BitVec k_N)) : Int := ExceptM.run do
  let loop_i_lower : Nat := 0
  let loop_i_upper : Int := ((Sail.BitVec.length x) -i 1)
  (do
    let mut loop_vars := ()
    for i in [loop_i_upper:loop_i_lower:-1]i do
      let () := loop_vars
      loop_vars ← do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access x (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
        then
          (do
            throw (i : Int))
        else (pure (()))
    (pure loop_vars))
  (pure ((Neg.neg 1)))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def BitCount (x : (BitVec k_N)) : Int := Id.run do
  let result : Int := 0
  let result ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := ((Sail.BitVec.length x) -i 1)
    (do
      let mut loop_vars := result
      for i in [loop_i_lower:loop_i_upper:1]i do
        let result := loop_vars
        loop_vars :=
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access x (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
          then (result +i 1)
          else result
      (pure loop_vars)) ) : Id Int )
  let result : Int := result
  (pure result)


def _set_Configuration_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_Configuration_Type_bits r v)


def _set_ACCDATA_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ACCDATA_EL1_Type_bits r v)


def _set_AMCFGR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_bits r v)


def _set_AMCFGR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCFGR_Type_bits r v)


def _set_AMCG1IDR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCG1IDR_EL0_Type_bits r v)


def _set_AMCGCR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCGCR_EL0_Type_bits r v)


def _set_AMCGCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCGCR_Type_bits r v)


def _set_AMCIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR0_Type_bits r v)


def _set_AMCIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR1_Type_bits r v)


def _set_AMCIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR2_Type_bits r v)


def _set_AMCIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCIDR3_Type_bits r v)


def _set_AMCNTENCLR0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCNTENCLR0_EL0_Type_bits r v)


def _set_AMCNTENCLR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCNTENCLR0_Type_bits r v)


def _set_AMCNTENCLR1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCNTENCLR1_EL0_Type_bits r v)


def _set_AMCNTENCLR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCNTENCLR1_Type_bits r v)


def _set_AMCNTENSET0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCNTENSET0_EL0_Type_bits r v)


def _set_AMCNTENSET0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCNTENSET0_Type_bits r v)


def _set_AMCNTENSET1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCNTENSET1_EL0_Type_bits r v)


def _set_AMCNTENSET1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCNTENSET1_Type_bits r v)


def _set_AMCR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCR_EL0_Type_bits r v)


def _set_AMCR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCR_Type_bits r v)


def _set_AMDEVARCH_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMDEVARCH_Type_bits r v)


def _set_AMDEVTYPE_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMDEVTYPE_Type_bits r v)


def _set_AMEVCNTR0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVCNTR0_EL0_Type_bits r v)


def _set_AMEVCNTR0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVCNTR0_Type_bits r v)


def _set_AMEVCNTR1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVCNTR1_EL0_Type_bits r v)


def _set_AMEVCNTR1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVCNTR1_Type_bits r v)


def _set_AMEVTYPER0_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVTYPER0_EL0_Type_bits r v)


def _set_AMEVTYPER0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMEVTYPER0_Type_bits r v)


def _set_AMEVTYPER1_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVTYPER1_EL0_Type_bits r v)


def _set_AMEVTYPER1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMEVTYPER1_Type_bits r v)


def _set_AMIIDR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMIIDR_Type_bits r v)


def _set_AMPIDR0_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR0_Type_bits r v)


def _set_AMPIDR1_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR1_Type_bits r v)


def _set_AMPIDR2_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR2_Type_bits r v)


def _set_AMPIDR3_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR3_Type_bits r v)


def _set_AMPIDR4_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMPIDR4_Type_bits r v)


def _set_AMUSERENR_EL0_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMUSERENR_EL0_Type_bits r v)


def _set_AMUSERENR_Type_bits (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMUSERENR_Type_bits r v)


def _set_BRBCR_EL1_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_bits r v)


def _set_BRBCR_EL2_Type_bits (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_bits r v)


end ArmFull.Functions
