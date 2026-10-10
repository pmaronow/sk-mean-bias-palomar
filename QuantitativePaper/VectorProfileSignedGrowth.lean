module
public import QuantitativePaper.VectorColeHopfOrderAllMass
public import QuantitativePaper.VectorProfileStepRepresentation

@[expose] public section

/-! Actual affine-profile recursions at every real interpolation parameter.
The Gaussian norm barrier gives uniform linear growth on bounded cylinders,
even when an affine mass crosses zero or becomes negative. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000

theorem vectorProfileRecursion_lipschitz_all_theta {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (p : Couplings n×ℝ) (j : ℕ) :
    LipschitzWith (Real.sqrt (n:ℝ)).toNNReal (vectorProfileRecursion s₀ s₁ β t θ p j) := by
  induction j with
  | zero => exact vectorTerminalPotential_lipschitz n β t p
  | succ j ih => exact vectorColeHopfStep_lipschitz_all_mass _ _ ih _ _

theorem vectorProfileRecursion_joint_lipschitz_all_theta {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t θ : ℝ) (j : ℕ) :
    LipschitzWith (vectorJointLipschitzConstant n β t)
      (fun p : VectorParameter n=>vectorProfileRecursion s₀ s₁ β t θ p.1 j p.2) := by
  induction j with
  | zero => exact vectorRecursion_joint_lipschitz s₀ β t 0
  | succ j ih =>
    rw [lipschitzWith_iff_dist_le_mul]
    intro p z
    rw [Real.dist_eq]
    simp only [vectorProfileRecursion]
    apply abs_vectorColeHopfStep_comparison_all_mass _ _ _ _
      (vectorProfileRecursion_lipschitz_all_theta s₀ s₁ β t θ p.1 j)
      (vectorProfileRecursion_lipschitz_all_theta s₀ s₁ β t θ z.1 j)
    intro w
    have hh := ih.dist_le_mul
      (p.1,fieldShift ((1-t)*(β^2*(s₀.q (k+2-j)-s₀.q (k+1-j)))) p.2 w)
      (z.1,fieldShift ((1-t)*(β^2*(s₀.q (k+2-j)-s₀.q (k+1-j)))) z.2 w)
    have he (c : ℝ) : dist (p.1,fieldShift c p.2 w) (z.1,fieldShift c z.2 w)=dist p z := by
      simp [dist_eq_norm,Prod.norm_def,fieldShift]
    simpa only [Real.dist_eq,he] using hh

theorem vectorProfileRecursion_zero_bounded_all_theta {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (j : ℕ) (a b : ℝ) :
    ∃ B : ℝ, 0≤B ∧ ∀θ∈Icc a b,
      |vectorProfileRecursion (n:=n) s₀ s₁ β t θ 0 j 0|≤B := by
  induction j with
  | zero => exact ⟨|vectorTerminalPotential n β t 0 0|,abs_nonneg _,fun θ hθ=>le_rfl⟩
  | succ j ih =>
    obtain ⟨B,hB,hbase⟩ := ih
    obtain ⟨M,hM,hMass⟩ := exists_vectorProfileMass_cylinder_bound (n:=n) s₀ s₁ (k+1-j) 0 a b
    obtain ⟨C,hC,hBarrier⟩ := vectorColeHopfStep_norm_barrier (n:=n)
      (Real.sqrt (n:ℝ)).toNNReal ((1-t)*(β^2*(s₀.q (k+2-j)-s₀.q (k+1-j)))) M
    refine ⟨B+C,add_nonneg hB hC,?_⟩
    intro θ hθ
    have hm : |vectorProfileMass s₀ s₁ θ (k+1-j)|≤M := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
        hMass 0 le_rfl (θ,0) hθ
    exact (hBarrier _ (abs_le.mp hm) _
      (vectorProfileRecursion_lipschitz_all_theta s₀ s₁ β t θ 0 j)).trans
      (add_le_add (hbase θ hθ) le_rfl)

theorem vectorProfileJointFunction_linear_growth_all_theta {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (j : ℕ) (a b : ℝ) :
    ∃ B L : ℝ, 0≤B ∧ 0≤L ∧ ∀z : ℝ×VectorParameter n,
      z.1∈Icc a b → |vectorProfileJointFunction s₀ s₁ β t j z|≤B+L*‖z‖ := by
  obtain ⟨B,hB,hbase⟩ := vectorProfileRecursion_zero_bounded_all_theta (n:=n) s₀ s₁ β t j a b
  refine ⟨B,(vectorJointLipschitzConstant n β t:ℝ),hB,
    (vectorJointLipschitzConstant n β t).coe_nonneg,?_⟩
  intro z hz
  have hh := (vectorProfileRecursion_joint_lipschitz_all_theta (n:=n) s₀ s₁ β t z.1 j).dist_le_mul z.2 0
  rw [Real.dist_eq,dist_zero_right] at hh
  simp only [Prod.fst_zero,Prod.snd_zero] at hh
  have htriangle := abs_add_le
    (vectorProfileRecursion s₀ s₁ β t z.1 z.2.1 j z.2.2-vectorProfileRecursion (n:=n) s₀ s₁ β t z.1 0 j 0)
    (vectorProfileRecursion (n:=n) s₀ s₁ β t z.1 0 j 0)
  rw [sub_add_cancel] at htriangle
  exact htriangle.trans (by
    have hn := mul_le_mul_of_nonneg_left (norm_snd_le z)
      (vectorJointLipschitzConstant n β t).coe_nonneg
    linarith [hh,hbase z.1 hz])

theorem vectorProfileJointFunction_shift_lipschitz_all_theta {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t c : ℝ) (j : ℕ) (x : ℝ×VectorParameter n)
    (z : Field n) :
    |vectorProfileJointFunction s₀ s₁ β t j (x+vectorProfileJointShift n c z)-
      vectorProfileJointFunction s₀ s₁ β t j x|≤
      (vectorJointLipschitzConstant n β t:ℝ)*‖vectorJointShift n c‖*‖z‖ := by
  have hh := (vectorProfileRecursion_joint_lipschitz_all_theta (n:=n) s₀ s₁ β t x.1 j).dist_le_mul
    (x.2+vectorJointShift n c z) x.2
  rw [Real.dist_eq,dist_eq_norm,add_sub_cancel_left] at hh
  rw [vectorProfileJointShift_add]
  unfold vectorProfileJointFunction
  rw [vectorJointShift_add] at hh
  have hmul := mul_le_mul_of_nonneg_left ((vectorJointShift n c).le_opNorm z)
    (vectorJointLipschitzConstant n β t).coe_nonneg
  exact hh.trans (by simpa only [mul_assoc] using hmul)

end QuantitativePaper
