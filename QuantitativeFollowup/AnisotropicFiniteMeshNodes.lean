module
public import QuantitativeFollowup.GaussianShiftFiniteMesh

@[expose] public section

/-! A finite anisotropic Gaussian recursion is jointly continuous in its
actual overlap nodes, including repeated nodes. Upward-rounded nodes converge
to the original nodes, without changing the finite mass sequence. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def anisotropicMeshTailRecursion (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (nodes : ℕ→ℝ) (q : ℝ) : ℕ→AnisotropicParameter n→ℝ
  | 0 => anisotropicGridTerminalPotential D
  | j+1 => gaussianShiftColeHopf
      (Real.sqrt (max q (nodes (k+2-j))-max q (nodes (k+1-j))) • anisotropicUnitInput D)
      (s.m (k+1-j)) (anisotropicMeshTailRecursion D s nodes q j)

theorem anisotropicMeshTailRecursion_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (nodes : ℕ→ℝ) (q : ℝ) (j : ℕ) :
    LipschitzWith ‖anisotropicEnergyMap D‖₊ (anisotropicMeshTailRecursion D s nodes q j) := by
  induction j with
  | zero => exact anisotropicGridTerminalPotential_lipschitz D
  | succ j ih =>
      exact gaussianShiftColeHopf_lipschitz_finite _ _ (s.m_nonneg (Nat.sub_le _ _)) _ _ ih

theorem continuous_anisotropicMeshTailRecursion_joint (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : ℝ) (j : ℕ) :
    Continuous (fun z : (ℕ→ℝ)×AnisotropicParameter n=>anisotropicMeshTailRecursion D s z.1 q j z.2) := by
  induction j with
  | zero => exact (anisotropicGridTerminalPotential_lipschitz D).continuous.comp continuous_snd
  | succ j ih =>
      simp_rw [anisotropicMeshTailRecursion,gaussianShiftColeHopf_eq_finiteStateGaussianStep]
      exact continuous_finiteStateGaussianStep_family (s.m (k+1-j))
        (fun z : (ℕ→ℝ)×AnisotropicParameter n=>anisotropicMeshTailRecursion D s z.1 q j)
        (ih.comp (continuous_fst.fst.prodMk continuous_snd)) ‖anisotropicEnergyMap D‖₊
        (fun z=>anisotropicMeshTailRecursion_lipschitz D s z.1 q j)
        (fun z : (ℕ→ℝ)×AnisotropicParameter n=>
          Real.sqrt (max q (z.1 (k+2-j))-max q (z.1 (k+1-j))) • anisotropicUnitInput D)
        (by fun_prop) (fun z=>z.2) continuous_snd

def anisotropicFiniteMeshNode (s : RSBScheme k) (i : ℕ) : Paper.Overlap :=
  projIcc 0 1 zero_le_one (s.q i)

theorem anisotropicFiniteMeshNode_coe (s : RSBScheme k) (i : ℕ) (hi : i≤k+2) :
    (anisotropicFiniteMeshNode s i : ℝ)=s.q i := by
  exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨s.q_nonneg hi,s.q_le_one hi⟩)

def anisotropicRoundedMeshNodes (s : RSBScheme k) (N : ℕ) (i : ℕ) : ℝ :=
  Paper.parisiGridRound N (anisotropicFiniteMeshNode s i)

def anisotropicFiniteMeshIndices (s : RSBScheme k) (N : ℕ) (i : ℕ) : ℕ :=
  Paper.parisiGridIndex N (anisotropicFiniteMeshNode s i)

theorem anisotropicRoundedMeshNodes_eq_index (s : RSBScheme k) (N i : ℕ) :
    anisotropicRoundedMeshNodes s N i=(anisotropicFiniteMeshIndices s N i : ℝ)/(N+1 : ℕ) := rfl

theorem anisotropicFiniteMeshIndices_le (s : RSBScheme k) (N i : ℕ) :
    anisotropicFiniteMeshIndices s N i≤N+1 :=
  Nat.le_of_lt_succ (Paper.parisiGridIndex N (anisotropicFiniteMeshNode s i)).isLt

theorem anisotropicFiniteMeshIndices_mono (s : RSBScheme k) (N i l : ℕ)
    (hl : l≤k+2) (hil : i≤l) :
    anisotropicFiniteMeshIndices s N i≤anisotropicFiniteMeshIndices s N l := by
  unfold anisotropicFiniteMeshIndices Paper.parisiGridIndex
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [anisotropicFiniteMeshNode_coe s i (hil.trans hl),anisotropicFiniteMeshNode_coe s l hl]
  exact s.q_mono' l hl i hil

theorem anisotropicFiniteMeshIndices_zero (s : RSBScheme k) (N : ℕ) :
    anisotropicFiniteMeshIndices s N 0=0 := by
  unfold anisotropicFiniteMeshIndices Paper.parisiGridIndex
  simp only [anisotropicFiniteMeshNode_coe s 0 (by omega),s.q_zero,mul_zero,Nat.ceil_zero]

theorem anisotropicFiniteMeshIndices_top (s : RSBScheme k) (N : ℕ) :
    anisotropicFiniteMeshIndices s N (k+2)=N+1 := by
  unfold anisotropicFiniteMeshIndices Paper.parisiGridIndex
  simp only [anisotropicFiniteMeshNode_coe s (k+2) le_rfl,s.q_top,mul_one,Nat.ceil_natCast]

theorem tendsto_anisotropicRoundedMeshNodes (s : RSBScheme k) :
    Tendsto (anisotropicRoundedMeshNodes s) atTop (𝓝 (fun i=>(anisotropicFiniteMeshNode s i : ℝ))) := by
  exact tendsto_pi_nhds.mpr fun i=>(continuous_subtype_val.tendsto _).comp
    (Paper.tendsto_parisiGridRound (anisotropicFiniteMeshNode s i))

theorem anisotropicMeshTailRecursion_original (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (q : ℝ) {j : ℕ} (hj : j≤k+2) :
    anisotropicMeshTailRecursion D s (fun i=>(anisotropicFiniteMeshNode s i : ℝ)) q j=
      anisotropicTailRecursion D s q j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [anisotropicMeshTailRecursion,anisotropicTailRecursion,ih (by omega),
        anisotropicFiniteMeshNode_coe s (k+2-j) (Nat.sub_le _ _),
        anisotropicFiniteMeshNode_coe s (k+1-j) (by omega)]

theorem tendsto_anisotropicRoundedMeshTailRecursion (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (q : ℝ) (P : AnisotropicParameter n) {j : ℕ} (hj : j≤k+2) :
    Tendsto (fun N=>anisotropicMeshTailRecursion D s (anisotropicRoundedMeshNodes s N) q j P)
      atTop (𝓝 (anisotropicTailRecursion D s q j P)) := by
  have hh:=(continuous_anisotropicMeshTailRecursion_joint D s q j).tendsto
    ((fun i=>(anisotropicFiniteMeshNode s i : ℝ)),P)
  have ht:=hh.comp ((tendsto_anisotropicRoundedMeshNodes s).prodMk_nhds (tendsto_const_nhds (x:=P)))
  simpa only [Function.comp_def,anisotropicMeshTailRecursion_original D s q hj] using ht

end QuantitativeFollowup
