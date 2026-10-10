module
public import QuantitativePaper.VectorGridInterpolationDerivative
public import QuantitativePaper.VectorInterpolationDefectBounds
public import QuantitativePaper.VectorMeasureMinimizer
public import FourPapersCommon.CompactLipschitzEnvelope

@[expose] public section

/-! The closed physical interpolation interval is controlled by the actual
finite derivative and weak convergence of genuine dyadic Parisi measures. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace QuantitativePaper
open FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1600000

def vectorInterpolationLipschitzConstant (β s : ℝ) (hs : s≤1) : NNReal :=
  ⟨β^2*(1-s),mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hs)⟩

theorem continuousOn_vectorMeasureFunctional_grid_interpolation
    (μ : Paper.ParisiMeasure) (j : ℕ) (β s : ℝ) (hs : 0<s) :
    ContinuousOn (fun t=>vectorMeasureFunctional n
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s) (Icc (0:ℝ) 1) := by
  exact (continuousOn_finiteVectorFunctional_interpolation
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β s hs).congr
      (fun t ht=>vectorMeasureFunctional_grid_eq_finite μ j β t s hs.ne' ht.2)

theorem vectorMeasureFunctional_grid_interpolation_lipschitz
    (hn : 0<n) (μ : Paper.ParisiMeasure) (j : ℕ) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0) :
    LipschitzOnWith (vectorInterpolationLipschitzConstant β s hs.2.le)
      (fun t=>vectorMeasureFunctional n
        (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s) (Icc (0:ℝ) 1) := by
  let g : ℝ→ℝ:=fun t=>if ht:t<1 then -β^2/4*vectorInterpolationDefect (n:=n)
    (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t ht.le else 0
  apply lipschitzOnWith_of_bounded_interior_derivative _ g 0 1
    (vectorInterpolationLipschitzConstant β s hs.2.le)
    (continuousOn_vectorMeasureFunctional_grid_interpolation μ j β s hs.1)
  · intro t ht
    simpa only [g,dif_pos ht.2] using
      hasDerivAt_vectorMeasureFunctional_grid_interpolation hn μ j β s hs.1 hμ hβ t ht
  · intro t ht
    simp only [g,dif_pos ht.2,vectorInterpolationLipschitzConstant]
    have hb:=vectorInterpolationDefect_bounds hn
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t hs.2.le hβ ht.2
    change abs (-β^2/4*vectorInterpolationDefect (n:=n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) s β t ht.2.le) ≤ β^2*(1-s)
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg β)) (by norm_num)) hb.1)]
    have hm:=mul_le_mul_of_nonneg_left hb.2 (sq_nonneg β)
    nlinarith

theorem tendsto_vectorMeasureFunctional_grid (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t s : ℝ) (ht : t≤1) :
    Tendsto (fun j=>vectorMeasureFunctional n
      (Paper.parisiGridMeasure μ (vectorDyadicIndex j)) β t s) atTop
      (𝓝 (vectorMeasureFunctional n μ β t s)) :=
  ((continuous_vectorMeasureFunctional n hn β t s ht).tendsto μ).comp
    ((FRSB.tendsto_parisiGridMeasure μ).comp tendsto_vectorDyadicIndex)

theorem vectorMeasureFunctional_interpolation_lipschitz
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0) :
    LipschitzOnWith (vectorInterpolationLipschitzConstant β s hs.2.le)
      (fun t=>vectorMeasureFunctional n μ β t s) (Icc (0:ℝ) 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro t ht u hu
  apply le_of_tendsto
    ((tendsto_vectorMeasureFunctional_grid hn μ β t s ht.2).dist
      (tendsto_vectorMeasureFunctional_grid hn μ β u s hu.2))
  exact .of_forall fun j=>(vectorMeasureFunctional_grid_interpolation_lipschitz
    hn μ j β s hs hμ hβ).dist_le_mul t ht u hu

theorem continuousOn_vectorMeasureFunctional_interpolation
    (hn : 0<n) (μ : Paper.ParisiMeasure) (β s : ℝ)
    (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0) :
    ContinuousOn (fun t=>vectorMeasureFunctional n μ β t s) (Icc (0:ℝ) 1) :=
  (vectorMeasureFunctional_interpolation_lipschitz hn μ β s hs hμ hβ).continuousOn

end QuantitativePaper
