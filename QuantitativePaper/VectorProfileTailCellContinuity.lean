module
public import QuantitativePaper.VectorProfileTailAmplitudeSmooth
public import QuantitativePaper.VectorProfileCellPDE
public import FourPapersCommon.PartialIteratedFDerivSmooth

@[expose] public section

/-! All retained profile/disorder/field jets are continuous through the
actual overlap-cell endpoints, including zero Gaussian variance. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiffAt_retained_iteratedFDeriv_vectorProfileTailAmplitudeFunction
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) (i j : ℕ) (hi : i ≤ k+1)
    (r : ℕ) (w : ℝ×(ℝ×VectorParameter n)) (hθ : w.2.1 ∈ Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (fun z : ℝ×(ℝ×VectorParameter n) =>
      iteratedFDeriv ℝ r (fun y => vectorProfileTailAmplitudeFunction s₀ s₁ β t i j (z.1,y)) z.2) w := by
  let F := fun z : (ℝ×VectorParameter n)×ℝ => vectorProfileTailAmplitudeFunction s₀ s₁ β t i j (z.2,z.1)
  have hF : ContDiffAt ℝ ∞ F (w.2,w.1) :=
    (contDiffAt_vectorProfileTailAmplitudeFunction s₀ s₁ β t ht i j hi w hθ).comp (w.2,w.1)
      (ContinuousLinearEquiv.prodComm ℝ (ℝ×VectorParameter n) ℝ).contDiff.contDiffAt
  have hJ := contDiffAt_partial_iteratedFDeriv r F (w.2,w.1) hF
  exact ContDiffAt.comp (f:=Prod.swap)
    (g:=fun z : (ℝ×VectorParameter n)×ℝ => iteratedFDeriv ℝ r (fun y => F (y,z.2)) z.1)
    w hJ (ContinuousLinearEquiv.prodComm ℝ ℝ (ℝ×VectorParameter n)).contDiff.contDiffAt

theorem continuousOn_retained_iteratedFDeriv_vectorProfileCellFunction
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) (c Q : ℝ)
    (i j : ℕ) (hi : i ≤ k+1) (r : ℕ) :
    ContinuousOn (fun z : ℝ×(ℝ×VectorParameter n) =>
      iteratedFDeriv ℝ r (fun y => vectorProfileCellFunction s₀ s₁ β t c Q i j (z.1,y)) z.2)
      {z | z.2.1 ∈ Ioo (0:ℝ) 1} := by
  have he (q : ℝ) : (fun y : ℝ×VectorParameter n => vectorProfileCellFunction s₀ s₁ β t c Q i j (q,y)) =
      (fun y => vectorProfileTailAmplitudeFunction s₀ s₁ β t i j (Real.sqrt (c*(Q-q)),y)) :=
    funext fun y => (vectorProfileTailAmplitudeFunction_eq_cell s₀ s₁ β t c Q i j q y).symm
  simp_rw [he]
  intro w hw
  have hJ : ContinuousAt (fun z : ℝ×(ℝ×VectorParameter n) =>
      iteratedFDeriv ℝ r (fun y => vectorProfileTailAmplitudeFunction s₀ s₁ β t i j (z.1,y)) z.2)
      (Real.sqrt (c*(Q-w.1)),w.2) :=
    (contDiffAt_retained_iteratedFDeriv_vectorProfileTailAmplitudeFunction (n:=n)
      s₀ s₁ β t ht i j hi r (Real.sqrt (c*(Q-w.1)),w.2) hw).continuousAt
  exact (hJ.comp (f:=fun z : ℝ×(ℝ×VectorParameter n) => (Real.sqrt (c*(Q-z.1)),z.2))
    (by fun_prop)).continuousWithinAt

theorem continuous_retained_iteratedFDeriv_vectorProfileCellFunction
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t ≤ 1) (c Q : ℝ)
    (i j : ℕ) (hi : i ≤ k+1) (r : ℕ) (θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) 1) :
    Continuous (fun z : ℝ×VectorParameter n =>
      iteratedFDeriv ℝ r (fun y : ℝ×VectorParameter n =>
        vectorProfileCellFunction s₀ s₁ β t c Q i j (z.1,y)) (θ,z.2)) :=
  (continuousOn_retained_iteratedFDeriv_vectorProfileCellFunction (n:=n) s₀ s₁ β t ht c Q i j hi r).comp_continuous
    (f:=fun z : ℝ×VectorParameter n => (z.1,θ,z.2))
    (by fun_prop) (fun _ => hθ)

theorem vectorProfileCellFunction_retained_jet_eq_tail (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (i : ℕ) (hi : i ≤ k+1) (q : ℝ)
    (hq : q ∈ Icc (s₀.q i) (s₀.q (i+1))) (y : ℝ×VectorParameter n)
    (hθ : y.1 ∈ Ioo (0:ℝ) 1) (r : ℕ) :
    iteratedFDeriv ℝ r (fun z : ℝ×VectorParameter n =>
      vectorProfilePhysicalCell s₀ s₁ β t i (q,z)) y =
    iteratedFDeriv ℝ r (fun z : ℝ×VectorParameter n =>
      vectorProfileTailRecursion s₀ s₁ β t q z.1 z.2.1 (k+2) z.2.2) y := by
  have he : (fun z : ℝ×VectorParameter n => vectorProfilePhysicalCell s₀ s₁ β t i (q,z)) =ᶠ[𝓝 y]
      (fun z : ℝ×VectorParameter n => vectorProfileTailRecursion s₀ s₁ β t q z.1 z.2.1 (k+2) z.2.2) := by
    filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds hθ] with z hz
    exact vectorProfilePhysicalCell_eq_tail s₀ s₁ β t i hi q z.1 ⟨hz.1.le,hz.2.le⟩ hq z.2.1 z.2.2
  exact (he.iteratedFDeriv ℝ r).eq_of_nhds

end QuantitativePaper
