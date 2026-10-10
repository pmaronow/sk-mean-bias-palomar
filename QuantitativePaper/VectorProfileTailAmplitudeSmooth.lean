module
public import QuantitativePaper.VectorProfileTailAmplitude
public import QuantitativePaper.VectorProfileCellSmooth

@[expose] public section

/-! The actual Gaussian amplitude cell is jointly C∞ even at amplitude zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileTailAmplitudeGaussian_contDiffOn (N : ℕ) (f : ℝ×VectorParameter n → ℝ)
    (l u a b : ℝ)
    (hf : ∀ y : ℝ×VectorParameter n, y.1 ∈ Ioo a b → ContDiffAt ℝ ∞ f y)
    (K D : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hjets : ∀ r, r ≤ N → ∀ y : ℝ×VectorParameter n, y.1 ∈ Ioo a b →
      ‖iteratedFDeriv ℝ r f y‖ ≤ K*Real.exp (D*‖y‖)) :
    ContDiffOn ℝ N (fun w : ℝ×(ℝ×VectorParameter n) =>
      ∫ z, f (vectorProfileTailAmplitudeEvaluation z w) ∂fieldGaussian n)
      (vectorProfileCellCylinder l u a b) := by
  let U : Set (ℝ×VectorParameter n) := {y | y.1 ∈ Ioo a b}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_fst
  apply variableGaussianAverage_contDiffOn N f U hU hf
    (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n)) (vectorProfileJointShift n 1)
    id univ isOpen_univ (fun _ _ => contDiffAt_id)
    (vectorProfileCellCylinder l u a b) (isOpen_vectorProfileCellCylinder l u a b) l u
    (subset_univ _) (fun w hw => ⟨hw.1.1.le,hw.1.2.le⟩) ?_ K D hK hD hjets
  intro w hw z
  change (vectorProfileTailAmplitudeEvaluation z w).1 ∈ Ioo a b
  rw [vectorProfileTailAmplitudeEvaluation_eq]
  exact hw.2

theorem contDiffOn_vectorProfileTailAmplitudeFunction (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (i j N : ℕ) (hi : i ≤ k+1)
    (l u a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ContDiffOn ℝ N (vectorProfileTailAmplitudeFunction (n:=n) s₀ s₁ β t i j)
      (vectorProfileCellCylinder l u a b) := by
  let W := vectorProfileCellCylinder (n:=n) l u a b
  have hθ (w : ℝ×(ℝ×VectorParameter n)) (hw : w ∈ W) : w.2.1 ∈ Ioo (0:ℝ) 1 :=
    ⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  rcases vectorProfileMass_zero_or_pos s₀ s₁ i hi with hm0|hmpos
  · obtain ⟨K,D,hK,hD,hj⟩ := exists_vectorProfileJointFunction_common_exp_jets
      (n:=n) s₀ s₁ β t ht N j a b ha hb
    have hAvg := vectorProfileTailAmplitudeGaussian_contDiffOn N
      (vectorProfileJointFunction (n:=n) s₀ s₁ β t j) l u a b
      (fun y hy => contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht j y
        ⟨ha.trans hy.1,hy.2.trans hb⟩) K D (zero_le_one.trans hK) hD hj
    apply hAvg.congr
    intro w hw
    rw [vectorProfileTailAmplitudeFunction,if_pos (hm0 w.2.1)]
  · obtain ⟨K,D,hK,hD,hj⟩ := exists_vectorProfileCellExponent_exp_jets
      (n:=n) s₀ s₁ β t ht N i j hi a b ha hb
    have hPart := vectorProfileTailAmplitudeGaussian_contDiffOn N
      (fun y : ℝ×VectorParameter n => Real.exp (vectorProfileCellExponent s₀ s₁ β t i j y))
      l u a b (fun y hy => (contDiffAt_vectorProfileCellExponent s₀ s₁ β t ht i j y
        ⟨ha.trans hy.1,hy.2.trans hb⟩).exp) K D hK hD hj
    have hLog := hPart.log (fun w hw => (vectorProfileTailAmplitudePartition_pos s₀ s₁ β t i j w
      ⟨(hθ w hw).1.le,(hθ w hw).2.le⟩).ne')
    have hMass : ContDiffOn ℝ N (fun w : ℝ×(ℝ×VectorParameter n) =>
        vectorProfileMass s₀ s₁ w.2.1 i) W := by
      have hm : ContDiff ℝ N (fun w : ℝ×(ℝ×VectorParameter n) =>
          vectorProfileMass s₀ s₁ w.2.1 i) := by unfold vectorProfileMass; fun_prop
      exact hm.contDiffOn
    have hInv := hMass.inv (fun w hw => (hmpos w.2.1 (hθ w hw)).ne')
    apply (hInv.mul hLog).congr
    intro w hw
    rw [vectorProfileTailAmplitudeFunction,if_neg (hmpos w.2.1 (hθ w hw)).ne']
    rfl

theorem contDiffAt_vectorProfileTailAmplitudeFunction (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (i j : ℕ) (hi : i ≤ k+1)
    (w : ℝ×(ℝ×VectorParameter n)) (hθ : w.2.1 ∈ Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileTailAmplitudeFunction s₀ s₁ β t i j) w := by
  apply contDiffAt_infty.mpr
  intro N
  let l := w.1-1
  let u := w.1+1
  let a := w.2.1/2
  let b := (w.2.1+1)/2
  have hw : w ∈ vectorProfileCellCylinder l u a b := by
    dsimp only [vectorProfileCellCylinder,l,u,a,b]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith [hθ.1],by linarith [hθ.2]⟩⟩
  have hh := contDiffOn_vectorProfileTailAmplitudeFunction (n:=n) s₀ s₁ β t ht i j N hi
    l u a b (by dsimp only [a];linarith [hθ.1]) (by dsimp only [b];linarith [hθ.2])
  exact (hh w hw).contDiffAt ((isOpen_vectorProfileCellCylinder l u a b).mem_nhds hw)

end QuantitativePaper
