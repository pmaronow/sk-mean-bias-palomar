module
public import HexagonPaper.CavityFixedRowRelativeJointBasic
public import HexagonPaper.CavityFixedCouplingTraceBasic
public import HexagonPaper.CavityCouplingTreeRelativeDensity

@[expose] public section

/-! Actual deterministic-row density relative to the true baseline native
probability law. This identity permits Gaussian heat envelopes using
uniform action differences, without introducing a new path-growth premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
open FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def cavityNativeFixedRowShift {j : ℕ} (T : FiniteTerminalGenealogy j)
    (θ : QuantitativePaper.Field n)
    (z : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T) :=
  (z.1 + cavityNativeIncidentRow n θ,
    cavityTreeRecordPathMap (cavityCouplingPathTranslation (cavityNativeIncidentRow n θ)) T z.2)

theorem measurable_cavityNativeFixedRowShift {j : ℕ} (T : FiniteTerminalGenealogy j)
    (θ : QuantitativePaper.Field n) : Measurable (cavityNativeFixedRowShift T θ) :=
  (measurable_fst.add_const _).prodMk ((measurable_cavityTreeRecordPathMap _
    (measurable_cavityCouplingPathTranslation _) T).comp measurable_snd)

def cavityNativeFixedRowRelativeAction (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (θ : QuantitativePaper.Field n)
    (z : AnisotropicDisorder (n+1) ×
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T) : ℝ :=
  a * (cavityNativeFixedRowPotential D μ (cavityNativeFixedRowShift T θ z).1 -
    cavityNativeFixedRowPotential D μ z.1) +
  treeNativePathLog (anisotropicUnitCouplings D) μ q T
    ((cavityNativeFixedRowShift T θ z).1, 0) (cavityNativeFixedRowShift T θ z).2 -
  treeNativePathLog (anisotropicUnitCouplings D) μ q T (z.1, 0) z.2

theorem measurable_cavityNativeFixedRowRelativeAction (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (θ : QuantitativePaper.Field n) :
    Measurable (cavityNativeFixedRowRelativeAction D μ a q T θ) := by
  have hs := measurable_cavityNativeFixedRowShift T θ
  have hU := (cavityNativeFixedRowPotential_lipschitz D μ).continuous.measurable
  have hL := measurable_treeNativePathLog (anisotropicUnitCouplings D) μ q T
  exact (((hU.comp hs.fst).sub (hU.comp measurable_fst)).const_mul a |>.add
    (hL.comp ((hs.fst.prodMk measurable_const).prodMk hs.snd))) |>.sub
      (hL.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))

theorem cavityNativeFixedRow_relative_density (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (hq : ∀ k, q (k+1) ≤ q k) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (θ : QuantitativePaper.Field n) :
    cavityNativeFixedRowLaw D μ a q T θ =
      ((cavityNativeFixedRowLaw D μ a q T 0).withDensity
        (fun z => ENNReal.ofReal (Real.exp (cavityNativeFixedRowRelativeAction D μ a q T θ z) *
          cavityNativeFixedRowNormalizer D μ a 0 / cavityNativeFixedRowNormalizer D μ a θ))).map
        (cavityNativeFixedRowShift T θ) := by
  let H := cavityNativeIncidentRow n θ
  let tr : Records (NativeTreePath (n+1)) (Configuration (n+1)) T →
      Records (NativeTreePath (n+1)) (Configuration (n+1)) T :=
    cavityTreeRecordPathMap (cavityCouplingPathTranslation H) T
  let K := cavityNativeFixedRowKernel D μ q T
  let g := fun Q Z => ENNReal.ofReal (Real.exp
    (treeNativePathLog (anisotropicUnitCouplings D) μ q T (Q + H, 0) (tr Z) -
      treeNativePathLog (anisotropicUnitCouplings D) μ q T (Q, 0) Z))
  have ht : Measurable tr := measurable_cavityTreeRecordPathMap _
    (measurable_cavityCouplingPathTranslation H) T
  have hL := measurable_treeNativePathLog (anisotropicUnitCouplings D) μ q T
  have hg : Measurable (Function.uncurry g) := by
    exact ((hL.comp (((measurable_fst.add_const H).prodMk measurable_const).prodMk
      (ht.comp measurable_snd))).sub
        (hL.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))).exp.ennreal_ofReal
  have hchild (Q : AnisotropicDisorder (n+1)) : ((K Q).withDensity (g Q)).map tr = K (Q + H) := by
    exact (cavityCoupling_shifted_physical_tree_relative_density (anisotropicUnitCouplings D)
      μ q hq H T (Q, 0)).symm
  have hd := cavityGaussianRootJoint_relative_from_child (cavityNativeFixedRowPotential D μ)
    (cavityNativeFixedRowPotential_lipschitz D μ) a (cavityNativeRestDisorder D) H K tr ht g hg
    (fun _ _ => ENNReal.ofReal_ne_top) hchild
  change cavityNativeFixedRowLaw D μ a q T θ = _ at hd
  rw [hd]
  congr 2
  · congr 1
    simp only [cavityNativeFixedRowLaw, map_zero]
  · funext z
    change ENNReal.ofReal _ * ENNReal.ofReal _ = ENNReal.ofReal _
    have hz0 : cavityGaussianRootNormalizer (cavityNativeFixedRowPotential D μ) a
        (cavityNativeRestDisorder D) 0 = cavityNativeFixedRowNormalizer D μ a 0 := by
      simp only [cavityNativeFixedRowNormalizer, map_zero]
    have hzH : cavityGaussianRootNormalizer (cavityNativeFixedRowPotential D μ) a
        (cavityNativeRestDisorder D) H = cavityNativeFixedRowNormalizer D μ a θ := rfl
    rw [hz0, hzH]
    rw [←ENNReal.ofReal_mul (div_nonneg
      (mul_nonneg (Real.exp_pos _).le (cavityNativeFixedRowNormalizer_pos D μ a 0).le)
      (cavityNativeFixedRowNormalizer_pos D μ a θ).le)]
    congr 1
    have ha : cavityNativeFixedRowRelativeAction D μ a q T θ z =
        a * (cavityNativeFixedRowPotential D μ (z.1 + H) -
          cavityNativeFixedRowPotential D μ z.1) +
        (treeNativePathLog (anisotropicUnitCouplings D) μ q T (z.1 + H, 0) (tr z.2) -
          treeNativePathLog (anisotropicUnitCouplings D) μ q T (z.1, 0) z.2) := by
      unfold cavityNativeFixedRowRelativeAction cavityNativeFixedRowShift
      change _ + _ - _ = _ + (_ - _)
      ring
    rw [ha, Real.exp_add]
    ring

end HexagonPaper
