module
public import QuantitativePaper.VectorProfileGridFunctionalIdentification
public import QuantitativePaper.VectorProfileSecondVariationEnergy
public import QuantitativePaper.VectorMeasureMinimizer
public import QuantitativeFollowup.AffineProfileCurve

@[expose] public section

/-! Closed continuity and true interior smoothness of the actual common-grid
mixture functional. The affine CDF correction is retained. Nonnegative
curvature is derived from its genuine profile-response energy. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem contDiffAt_vectorProfileFiniteEnergyFunctional (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (lam θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileFiniteEnergyFunctional (n := n) s₀ s₁ β t lam) θ := by
  have hc : ContDiffAt ℝ ∞ (fun y => vectorProfileOuterEnergy (n := n) s₀ s₁ β t lam y -
      ((1-t)*β/2) * ((1-y) *
        (∫ q in (0 : ℝ)..1, q * Paper.parisiCDF (Paper.parisiSchemeMeasure s₀) q) +
        y * (∫ q in (0 : ℝ)..1, q * Paper.parisiCDF (Paper.parisiSchemeMeasure s₁) q))) θ := by
    apply (contDiffAt_vectorProfileOuterEnergy s₀ s₁ β t ht lam θ hθ).sub
    fun_prop
  exact hc.congr_of_eventuallyEq
    (vectorProfileFiniteEnergyFunctional_eventually_affine s₀ s₁ β t lam θ hθ)

theorem continuousOn_vectorGridResponseFunctional_mix (hn : 0 < n)
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t lam : ℝ) (ht : t ≤ 1) :
    ContinuousOn (fun θ => responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) θ) β t lam) (Icc (0 : ℝ) 1) := by
  exact ((continuous_vectorMeasureFunctional n hn β t (lam/β) ht).div_const β).comp_continuousOn
    (QuantitativeFollowup.continuousOn_parisiMix _ _)

theorem vectorGridResponseFunctional_mix_eventually_eq (μ ν : Paper.ParisiMeasure)
    (j : ℕ) (β t lam θ : ℝ) (ht : t ≤ 1) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    (fun y => responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) y) β t lam) =ᶠ[𝓝 θ]
      vectorProfileFiniteEnergyFunctional (n := n)
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t lam := by
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
  have h := vectorProfile_grid_functional_eq (n := n) μ ν j β t lam y ht ⟨hy.1.le, hy.2.le⟩
  rw [parisiGridMeasure_mix μ ν (vectorDyadicIndex j) y ⟨hy.1.le, hy.2.le⟩] at h
  exact h.symm

theorem contDiffAt_vectorGridResponseFunctional_mix (μ ν : Paper.ParisiMeasure)
    (j : ℕ) (β t lam θ : ℝ) (ht : t ≤ 1) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun y => responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) y) β t lam) θ :=
  (contDiffAt_vectorProfileFiniteEnergyFunctional _ _ β t ht lam θ hθ).congr_of_eventuallyEq
    (vectorGridResponseFunctional_mix_eventually_eq μ ν j β t lam θ ht hθ)

theorem contDiffOn_vectorGridResponseFunctional_mix (μ ν : Paper.ParisiMeasure)
    (j : ℕ) (β t lam : ℝ) (ht : t ≤ 1) :
    ContDiffOn ℝ ∞ (fun θ => responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) θ) β t lam) (Ioo (0 : ℝ) 1) := by
  intro θ hθ
  exact (contDiffAt_vectorGridResponseFunctional_mix μ ν j β t lam θ ht hθ).contDiffWithinAt

theorem convexOn_vectorGridResponseFunctional_mix (μ ν : Paper.ParisiMeasure)
    (j : ℕ) (β t lam : ℝ) (hβ : 0 < β) (ht : t ≤ 1) (hlam : 0 ≤ lam) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun θ => responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) θ) β t lam) :=
  responseEnergyFunctional_mix_convex n _ _ β t lam hβ ht hlam

theorem iteratedDeriv2_vectorGridResponseFunctional_mix_nonneg (hn : 0 < n)
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t lam θ : ℝ)
    (hβ : 0 < β) (ht : t < 1) (hlam : 0 ≤ lam) (hθ : θ ∈ Ioo (0 : ℝ) 1) :
    0 ≤ iteratedDeriv 2 (fun y => responseEnergyFunctional n
      (Paper.parisiMix (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
        (Paper.parisiGridMeasure ν (vectorDyadicIndex j)) y) β t lam) θ := by
  rw [(vectorGridResponseFunctional_mix_eventually_eq μ ν j β t lam θ ht.le hθ).iteratedDeriv_eq 2]
  exact (div_nonneg
    (vectorProfileSecondVariationTotalEnergy_nonneg (n := n) _ _ β t (lam/β) θ ht.le
      ⟨hθ.1.le, hθ.2.le⟩) (by positivity)).trans
    (vectorProfileFiniteEnergyFunctional_curvature_ge_total_energy hn _ _ β t lam θ hβ ht hlam hθ)

end QuantitativePaper
