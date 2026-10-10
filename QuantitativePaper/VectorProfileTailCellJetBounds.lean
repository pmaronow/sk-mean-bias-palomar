module
public import QuantitativePaper.VectorProfileTailAmplitudeJets
public import QuantitativePaper.LocalFieldSliceJets

@[expose] public section

/-! Uniform true retained jets on closed overlap cells, including their
zero-variance endpoint. Overlap-time derivatives are not asserted here. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem exists_vectorProfileCellFunction_closed_retained_exp_jets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (c Q l u a b : ℝ) (hc : 0 ≤ c)
    (ha : 0 < a) (hb : b < 1) (i j N : ℕ) (hi : i ≤ k+1) :
    ∃ C R : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ ∀ r, r ≤ N → ∀ q ∈ Icc l u,
      ∀ y : ℝ×VectorParameter n, y.1 ∈ Ioo a b →
      ‖iteratedFDeriv ℝ r (fun z => vectorProfileCellFunction s₀ s₁ β t c Q i j (q,z)) y‖ ≤
        C*Real.exp (R*‖y‖) := by
  let S := Real.sqrt (c*(Q-l))
  obtain ⟨C,R,hC,hR,hjets⟩ := exists_vectorProfileTailAmplitudeFunction_common_exp_jets
    (n:=n) s₀ s₁ β t ht i j N hi (-1) (S+1) a b ha hb
  refine ⟨C*Real.exp (R*S),R,?_,hR,?_⟩
  · calc
      1 = 1*1 := by ring
      _ ≤ C*Real.exp (R*S) := mul_le_mul hC
        (Real.one_le_exp_iff.mpr (mul_nonneg hR (Real.sqrt_nonneg _))) (by norm_num)
        (zero_le_one.trans hC)
  · intro r hr q hq y hy
    let σ := Real.sqrt (c*(Q-q))
    have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
    have hσ : σ ≤ S := Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (by linarith [hq.1]) hc)
    let W := vectorProfileCellCylinder (n:=n) (-1) (S+1) a b
    have hw : (σ,y) ∈ W := ⟨⟨by linarith,by linarith⟩,hy⟩
    have he : (fun z : ℝ×VectorParameter n => vectorProfileCellFunction s₀ s₁ β t c Q i j (q,z)) =
        (fun z => vectorProfileTailAmplitudeFunction s₀ s₁ β t i j (σ,z)) :=
      funext fun z => (vectorProfileTailAmplitudeFunction_eq_cell s₀ s₁ β t c Q i j q z).symm
    rw [he]
    have hslice := norm_iteratedFDeriv_fieldSlice_le_joint_on_open
      (vectorProfileTailAmplitudeFunction (n:=n) s₀ s₁ β t i j) W
      (isOpen_vectorProfileCellCylinder _ _ _ _) (fun w hw =>
        contDiffAt_vectorProfileTailAmplitudeFunction s₀ s₁ β t ht i j hi w
          ⟨ha.trans hw.2.1,hw.2.2.trans hb⟩) r σ y hw
    apply hslice.trans ((hjets r hr (σ,y) hw).trans _)
    have hnorm : ‖(σ,y)‖ ≤ S+‖y‖ := by
      rw [Prod.norm_def,Real.norm_of_nonneg hσ0]
      exact max_le (hσ.trans (le_add_of_nonneg_right (norm_nonneg _)))
        (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    have hbound := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnorm hR)) (zero_le_one.trans hC)
    simpa only [mul_add,Real.exp_add,mul_assoc] using hbound

end QuantitativePaper
