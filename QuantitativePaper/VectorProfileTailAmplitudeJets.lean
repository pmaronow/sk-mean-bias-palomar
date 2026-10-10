module
public import QuantitativePaper.VectorProfileTailAmplitudeBounds
public import QuantitativePaper.VectorProfileCellJetBounds
public import QuantitativePaper.LogValueExponentialBounds

@[expose] public section

/-! All true amplitude/profile/disorder/field jets have uniform exponential
envelopes on compact amplitude and interior profile crops. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2500000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileTailAmplitudeGaussian_exp_jets (N : ℕ) (f : ℝ×VectorParameter n → ℝ)
    (l u a b : ℝ)
    (hf : ∀ y : ℝ×VectorParameter n, y.1 ∈ Ioo a b → ContDiffAt ℝ ∞ f y)
    (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hjets : ∀ r, r ≤ N → ∀ y : ℝ×VectorParameter n, y.1 ∈ Ioo a b →
      ‖iteratedFDeriv ℝ r f y‖ ≤ K*Real.exp (D*‖y‖)) :
    ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ ∀ r, r ≤ N → ∀ w ∈ vectorProfileCellCylinder l u a b,
      ‖iteratedFDeriv ℝ r (fun w : ℝ×(ℝ×VectorParameter n) =>
        ∫ z, f (vectorProfileTailAmplitudeEvaluation z w) ∂fieldGaussian n) w‖ ≤ C*Real.exp (R*‖w‖) := by
  let U : Set (ℝ×VectorParameter n) := {y | y.1 ∈ Ioo a b}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
  have hshift : ∀ w ∈ vectorProfileCellCylinder (n:=n) l u a b, ∀ z,
      variableGaussianEvaluation (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n))
        (vectorProfileJointShift n 1) id z w ∈ U := by
    intro w hw z
    change (vectorProfileTailAmplitudeEvaluation z w).1 ∈ Ioo a b
    rw [vectorProfileTailAmplitudeEvaluation_eq]
    exact hw.2
  have h := variableGaussianAverage_iteratedFDeriv_bound N f U hU hf
    (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n)) (vectorProfileJointShift n 1)
    id univ isOpen_univ (fun _ _ => contDiffAt_id)
    (vectorProfileCellCylinder l u a b) (isOpen_vectorProfileCellCylinder l u a b) l u
    (subset_univ _) (fun w hw => ⟨hw.1.1.le,hw.1.2.le⟩) hshift K D hK hD hjets
  apply exists_common_finite_exponential_jet_bound N _ _
  intro r hr
  obtain ⟨C,R,hC,hR,hb⟩ := h r hr
  exact ⟨C,R,hC,hR,fun w hw => (hb w hw).2⟩

theorem exists_vectorProfileTailAmplitudeFunction_common_exp_jets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (i j N : ℕ) (hi : i ≤ k+1)
    (l u a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ ∀ r, r ≤ N → ∀ w ∈ vectorProfileCellCylinder (n:=n) l u a b,
      ‖iteratedFDeriv ℝ r (vectorProfileTailAmplitudeFunction s₀ s₁ β t i j) w‖ ≤ C*Real.exp (R*‖w‖) := by
  let W := vectorProfileCellCylinder (n:=n) l u a b
  have hW := isOpen_vectorProfileCellCylinder (n:=n) l u a b
  have hθ (w : ℝ×(ℝ×VectorParameter n)) (hw : w ∈ W) : w.2.1 ∈ Ioo (0:ℝ) 1 :=
    ⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  rcases vectorProfileMass_zero_or_pos s₀ s₁ i hi with hm0|hmpos
  · obtain ⟨K,D,hK,hD,hj⟩ := exists_vectorProfileJointFunction_common_exp_jets
      (n:=n) s₀ s₁ β t ht N j a b ha hb
    obtain ⟨C,R,hC,hR,hbnd⟩ := vectorProfileTailAmplitudeGaussian_exp_jets N
      (vectorProfileJointFunction (n:=n) s₀ s₁ β t j) l u a b
      (fun y hy => contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht j y
        ⟨ha.trans hy.1,hy.2.trans hb⟩) K D (zero_le_one.trans hK) hD hj
    refine ⟨C,R,hC,hR,?_⟩
    intro r hr w hw
    have he : vectorProfileTailAmplitudeFunction s₀ s₁ β t i j =ᶠ[𝓝 w]
        (fun w : ℝ×(ℝ×VectorParameter n) => ∫ z,
          vectorProfileJointFunction s₀ s₁ β t j (vectorProfileTailAmplitudeEvaluation z w) ∂fieldGaussian n) := by
      filter_upwards with y
      rw [vectorProfileTailAmplitudeFunction,if_pos (hm0 y.2.1)]
    rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]
    exact hbnd r hr w hw
  · let Z := vectorProfileTailAmplitudePartition (n:=n) s₀ s₁ β t i j
    obtain ⟨K,D,hK,hD,hj⟩ := exists_vectorProfileCellExponent_exp_jets
      (n:=n) s₀ s₁ β t ht N i j hi a b ha hb
    have hf : ∀ y : ℝ×VectorParameter n, y.1 ∈ Ioo a b → ContDiffAt ℝ ∞
        (fun y => Real.exp (vectorProfileCellExponent s₀ s₁ β t i j y)) y :=
      fun y hy => (contDiffAt_vectorProfileCellExponent s₀ s₁ β t ht i j y
        ⟨ha.trans hy.1,hy.2.trans hb⟩).exp
    obtain ⟨C,R,hC,hR,hupper⟩ := vectorProfileTailAmplitudeGaussian_exp_jets N
      (fun y : ℝ×VectorParameter n => Real.exp (vectorProfileCellExponent s₀ s₁ β t i j y))
      l u a b hf K D hK hD hj
    have hZ : ContDiffOn ℝ N Z W := vectorProfileTailAmplitudeGaussian_contDiffOn N
      (fun y : ℝ×VectorParameter n => Real.exp (vectorProfileCellExponent s₀ s₁ β t i j y))
      l u a b hf K D hK hD hj
    obtain ⟨d,T,hd,hT,hlower⟩ := exists_vectorProfileTailAmplitudePartition_exponential_lower
      (n:=n) s₀ s₁ β t ht l u a b ha hb i j hi
    have hlog := log_iteratedFDeriv_exponential_bound Z W hW hZ C R d T
      (zero_le_one.trans hC) hR hd hT hupper hlower
    obtain ⟨A,S,hA,hS,hlogjets⟩ := exists_common_finite_exponential_jet_bound N
      (fun y => Real.log (Z y)) W (by
        intro r hr
        by_cases hz : r = 0
        · subst r
          let B := |Real.log C|+|Real.log d|
          let L := R+T
          refine ⟨B+L,1,by dsimp [B,L];positivity,by norm_num,?_⟩
          intro w hw
          have hp : 0 < Z w := (mul_pos hd (Real.exp_pos _)).trans_le (hlower w hw)
          have hbound : Z w ≤ C*Real.exp (R*‖w‖) := by
            have hzero := hupper 0 (by omega) w hw
            simp only [norm_iteratedFDeriv_zero] at hzero
            change ‖Z w‖ ≤ C*Real.exp (R*‖w‖) at hzero
            simpa only [Real.norm_of_nonneg hp.le] using hzero
          simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,one_mul]
          exact (abs_log_le_of_exponential_bounds (Z w) C R d T ‖w‖
            (zero_lt_one.trans_le hC) hd hR hT (norm_nonneg _) (hlower w hw) hbound).trans
            (linear_growth_le_exponential B L ‖w‖ (by dsimp [B];positivity) (by dsimp [L];positivity) (norm_nonneg _))
        · exact hlog r (by omega) hr)
    obtain ⟨M,hM,hinvjets⟩ := vectorProfileCellMass_inverse_exp_jets (n:=n)
      s₀ s₁ i N hmpos l u a b ha hb
    let I := fun w : ℝ×(ℝ×VectorParameter n) => (vectorProfileMass s₀ s₁ w.2.1 i)⁻¹
    have hI : ContDiffOn ℝ N I W := by
      have hm : ContDiff ℝ N (fun w : ℝ×(ℝ×VectorParameter n) => vectorProfileMass s₀ s₁ w.2.1 i) := by
        unfold vectorProfileMass
        fun_prop
      exact hm.contDiffOn.inv (fun w hw => (hmpos w.2.1 (hθ w hw)).ne')
    have hLog : ContDiffOn ℝ N (fun y => Real.log (Z y)) W :=
      hZ.log (fun w hw => (mul_pos hd (Real.exp_pos _)).trans_le (hlower w hw) |>.ne')
    have hprod := bounded_factor_exponential_jets N (fun y => Real.log (Z y)) I W hW hLog hI
      A S M (zero_le_one.trans hA) hS (zero_le_one.trans hM) hlogjets hinvjets
    apply exists_common_finite_exponential_jet_bound N _ W
    intro r hr
    refine ⟨(2:ℝ)^N*M*A,S,by positivity,hS,?_⟩
    intro w hw
    have he : vectorProfileTailAmplitudeFunction s₀ s₁ β t i j =ᶠ[𝓝 w]
        (fun y => I y*Real.log (Z y)) := by
      filter_upwards [hW.mem_nhds hw] with y hy
      rw [vectorProfileTailAmplitudeFunction,if_neg (hmpos y.2.1 (hθ y hy)).ne']
    rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]
    exact hprod r hr w hw

end QuantitativePaper
