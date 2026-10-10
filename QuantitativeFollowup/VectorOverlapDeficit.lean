module
public import QuantitativeFollowup.VectorMeanOverlap

@[expose] public section

/-! The reflected transport-deficit estimate with the actual all-measure
vector self-overlap, including endpoint folds and the exact uniform cost. -/
noncomputable section
open Set MeasureTheory QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
variable {n : ℕ}

def vectorMeanOverlapReal (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : ℝ) : ℝ := vectorMeanOverlap (n:=n) μ β t a ht (projIcc (0:ℝ) 1 zero_le_one q)

theorem continuous_vectorMeanOverlapReal (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : Continuous (vectorMeanOverlapReal (n:=n) μ β t a ht) :=
  (continuous_vectorMeanOverlap μ β t a ht).comp continuous_projIcc

theorem vectorMeanOverlapReal_nonneg_le_one (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : ℝ) :
    0≤vectorMeanOverlapReal (n:=n) μ β t a ht q ∧ vectorMeanOverlapReal (n:=n) μ β t a ht q≤1 :=
  vectorMeanOverlap_nonneg_le_one μ β t a ht _

theorem vectorMeanOverlapReal_monotoneOn (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) :
    MonotoneOn (vectorMeanOverlapReal (n:=n) μ β t a ht.le) (Icc (0:ℝ) 1) := by
  intro r hr q hq hrq
  unfold vectorMeanOverlapReal
  rw [projIcc_of_mem zero_le_one hr,projIcc_of_mem zero_le_one hq]
  exact vectorMeanOverlap_monotone μ β t a hβ ht hrq

def vectorOverlapDeficit (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) : ℝ→ℝ :=
  transportDeficit (vectorMeanOverlapReal (n:=n) μ β t a ht)

theorem vectorOverlapDeficit_taylor (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q y : ℝ) (hq : q∈Icc (0:ℝ) 1) (hy : y∈Icc (0:ℝ) 1) :
    vectorOverlapDeficit (n:=n) μ β t a ht.le y ≤ vectorOverlapDeficit (n:=n) μ β t a ht.le q+
      (q-vectorMeanOverlapReal (n:=n) μ β t a ht.le q)*(y-q)+(y-q)^2/2 :=
  transportDeficit_taylor _ (continuous_vectorMeanOverlapReal μ β t a ht.le)
    (vectorMeanOverlapReal_monotoneOn μ β t a hβ ht) q y hq hy

theorem vectorOverlapDeficit_reflected_taylor (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q u : ℝ) (hq : q∈Icc (0:ℝ) 1)
    (hy : overlapReflection (q+u)∈Icc (0:ℝ) 1) :
    vectorOverlapDeficit (n:=n) μ β t a ht.le (overlapReflection (q+u)) ≤
      vectorOverlapDeficit (n:=n) μ β t a ht.le q+
      (q-vectorMeanOverlapReal (n:=n) μ β t a ht.le q)*u+u^2/2 :=
  transportDeficit_reflected_taylor _ (continuous_vectorMeanOverlapReal μ β t a ht.le)
    (vectorMeanOverlapReal_monotoneOn μ β t a hβ ht)
    (fun q _=>vectorMeanOverlapReal_nonneg_le_one μ β t a ht.le q) q u hq hy

theorem vectorOverlapDeficit_reflected_uniform_bound (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (h : ℝ) (hh : h∈Ioc (0:ℝ) (1/2))
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    (∫u,vectorOverlapDeficit (n:=n) μ β t a ht.le (overlapReflection (q+u))∂symmetricUniformLaw h)-
      vectorOverlapDeficit (n:=n) μ β t a ht.le q≤h^2/6 :=
  transportDeficit_reflected_uniform_bound _ (continuous_vectorMeanOverlapReal μ β t a ht.le)
    (vectorMeanOverlapReal_monotoneOn μ β t a hβ ht)
    (fun q _=>vectorMeanOverlapReal_nonneg_le_one μ β t a ht.le q) h hh q hq

end QuantitativeFollowup
