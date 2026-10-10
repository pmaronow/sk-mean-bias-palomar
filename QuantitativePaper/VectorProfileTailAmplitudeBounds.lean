module
public import QuantitativePaper.VectorProfileTailAmplitudeSmooth
public import QuantitativePaper.VectorGaussianLowerPropagation

@[expose] public section

/-! Actual positive partition bounds uniform across a closed zero-amplitude
neighborhood. The retained disorder and field coordinates are unrestricted. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem exists_vectorProfileTailAmplitudePartition_exponential_lower (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (l u a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (i j : ℕ) (hi : i ≤ k+1) :
    ∃ d D : ℝ, 0 < d ∧ 0 ≤ D ∧ ∀ w ∈ vectorProfileCellCylinder (n:=n) l u a b,
      d*Real.exp (-D*‖w‖) ≤ vectorProfileTailAmplitudePartition s₀ s₁ β t i j w := by
  obtain ⟨B,L,hB,hL,hvalue⟩ := vectorProfileJointFunction_linear_growth (n:=n) s₀ s₁ β t ht j
  let A := vectorProfileJointShift n 1
  let H := L*(|l|+|u|)*‖A‖
  let d := Real.exp (-B)*vectorGaussianNormLaplace n (-H)
  refine ⟨d,L,mul_pos (Real.exp_pos _) (vectorGaussianNormLaplace_pos _ _),hL,?_⟩
  intro w hw
  have hθ : w.2.1 ∈ Icc (0:ℝ) 1 := ⟨(ha.trans hw.2.1).le,(hw.2.2.trans hb).le⟩
  have hmass := vectorProfileMass_mem_unit s₀ s₁ i hi w.2.1 hθ
  have hσ : |w.1| ≤ |l|+|u| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le l,abs_nonneg u,hw.1.1]
    · linarith [le_abs_self u,abs_nonneg l,hw.1.2]
  have heval (z : Field n) : ‖vectorProfileTailAmplitudeEvaluation z w‖ ≤
      ‖w‖+(|l|+|u|)*‖A‖*‖z‖ := by
    change ‖w.2+w.1 • A z‖ ≤ _
    apply (norm_add_le _ _).trans
    apply add_le_add (norm_snd_le w)
    rw [norm_smul,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left (A.le_opNorm z) (abs_nonneg _)).trans
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hσ (mul_nonneg (norm_nonneg A) (norm_nonneg z))
  have hpoint (z : Field n) : -B-L*‖w‖-H*‖z‖ ≤
      vectorProfileCellExponent s₀ s₁ β t i j (vectorProfileTailAmplitudeEvaluation z w) := by
    have hv := hvalue (vectorProfileTailAmplitudeEvaluation z w) (by
      rw [vectorProfileTailAmplitudeEvaluation_eq];exact hθ)
    have hm : |vectorProfileCellExponent s₀ s₁ β t i j (vectorProfileTailAmplitudeEvaluation z w)| ≤
        |vectorProfileJointFunction s₀ s₁ β t j (vectorProfileTailAmplitudeEvaluation z w)| := by
      rw [vectorProfileCellExponent,vectorProfileTailAmplitudeEvaluation_eq]
      rw [abs_mul,abs_of_nonneg hmass.1]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass.2 (abs_nonneg _)
    have hx := mul_le_mul_of_nonneg_left (heval z) hL
    dsimp [H] at *
    linarith [neg_abs_le (vectorProfileCellExponent s₀ s₁ β t i j (vectorProfileTailAmplitudeEvaluation z w))]
  have hiZ : Integrable (fun z : Field n => Real.exp
      (vectorProfileCellExponent s₀ s₁ β t i j (vectorProfileTailAmplitudeEvaluation z w)))
      (fieldGaussian n) := by
    have hh := integrable_gaussianShiftPartition_input
      (vectorProfileRecursion s₀ s₁ β t w.2.1 w.2.2.1 j) (Real.sqrt (n:ℝ)).toNNReal
      (vectorProfileRecursion_lipschitz s₀ s₁ β t w.2.1 hθ w.2.2.1 j)
      (w.1 • ContinuousLinearMap.id ℝ (Field n)) (vectorProfileMass s₀ s₁ w.2.1 i) w.2.2.2
    simpa only [vectorProfileTailAmplitudeEvaluation_eq,vectorProfileCellExponent,
      vectorProfileJointFunction,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using hh
  have hm := integral_mono
    ((SYK.integrable_exp_mul_norm (ι:=Fin n) (-H)).const_mul (Real.exp (-B-L*‖w‖))) hiZ
    (fun z => by
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hpoint z]))
  apply le_trans _ hm
  dsimp only [d,vectorGaussianNormLaplace]
  rw [integral_const_mul,Real.exp_sub,Real.exp_neg]
  ring_nf
  rw [Real.exp_neg]

end QuantitativePaper
