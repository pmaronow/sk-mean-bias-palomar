module
public import QuantitativeFollowup.FoundationContinuousDerivative
public import QuantitativeFollowup.FoundationJointMartingale
public import QuantitativePaper.VectorMeanStochasticL2
public import QuantitativePaper.ContactProposition
public import QuantitativeFollowup.VectorDeficitFirstVariation
public import QuantitativeFollowup.VectorContactCriterion

@[expose] public section

/-! The complete follow-up Proposition 2.1, on the actual disorder,
Brownian-path and terminal Gibbs-spin law. All profile and contact inputs
are the genuine model assumptions; no stochastic identity is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper Filter
open scoped Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

structure FoundationMartingaleContactTarget (n : ℕ) (μ : Paper.ParisiMeasure)
    (β s t : ℝ) (ht : t < 1) : Prop where
  conditional_mean : ∀q : Paper.Overlap,
    (vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le)[
      (fun p : VectorDisorderBrownianSample n × Configuration n => spinVector p.2) |
      foundationSpinFiltration n q] =ᵐ[vectorMeasureSpinPathLaw μ β t s ht.le]
      fun p => vectorMeasureSpinMean μ β t ht.le q p.1
  gradient_identity : ∀q (p : VectorDisorderBrownianSample n),
    vectorMeasureSpinMean μ β t ht.le q p =
      vectorMeasureGradient μ β t q p.1
        (vectorMeasureState μ β t ht.le (q:ℝ).toNNReal p)
  initial_zero : ∀p : VectorDisorderBrownianSample n,
    vectorMeasureSpinMean μ β t ht.le 0 p = 0
  martingale : Martingale (fun q : Paper.Overlap => fun p :
      VectorDisorderBrownianSample n × Configuration n =>
      vectorMeasureSpinMean μ β t ht.le q p.1)
    (foundationSpinFiltration n) (vectorMeasureSpinPathLaw μ β t s ht.le)
  stochastic_L2 : ∀(r q : Paper.Overlap) (hrq : r ≤ q),
    Tendsto (fun N => ∫p : VectorDisorderBrownianSample n,
      ‖vectorMeasureSpinMean μ β t ht.le q p - vectorMeasureSpinMean μ β t ht.le r p -
        vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq N p‖^2
      ∂vectorMeasureDisorderTilt μ β t s) atTop (𝓝 0)
  stochastic_probability : ∀(r q : Paper.Overlap) (hrq : r ≤ q),
    TendstoInMeasure (vectorMeasureDisorderTilt (n:=n) μ β t s)
      (vectorMeanLeftSum (n:=n) μ β t ht.le r q hrq) atTop
      (fun p => vectorMeasureSpinMean μ β t ht.le q p -
        vectorMeasureSpinMean μ β t ht.le r p)
  covariance_order : ∀q : Paper.Overlap,
    ∀ᵐp ∂vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le,
      (vectorMeasureSpinCovariance μ β t s ht.le q p.1).PosSemidef ∧
      (vectorMeasureHessianMatrix μ β t ht.le q p.1 -
        Paper.parisiCDF μ q • vectorMeasureSpinCovariance μ β t s ht.le q p.1).PosSemidef ∧
      (vectorMeasureSpinCovariance μ β t s ht.le q p.1 -
        vectorMeasureHessianMatrix μ β t ht.le q p.1).PosSemidef
  mean_C1_extension : ∃f : ℝ → ℝ, ContDiff ℝ 1 f ∧
    (∀q : Paper.Overlap, f q = ∫p, vectorSelfOverlap (n:=n) μ β t ht.le q p
      ∂vectorMeasureSpinPathLaw μ β t s ht.le) ∧
    (∀q : Paper.Overlap, HasDerivAt f
      (((1-t)*β^2)/(n:ℝ) *
        (∫p : VectorDisorderBrownianSample n × Configuration n,
          Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q p.1 *
            vectorMeasureHessianMatrix μ β t ht.le q p.1)
          ∂vectorMeasureSpinPathLaw μ β t s ht.le)) (q:ℝ))
  first_variation : ∀ν ∈ scalarFloor s,
    HasDerivWithinAt (fun lam => vectorMeasureFunctional n (Paper.parisiMix μ ν lam) β t s)
      (((1-t)*β^2)/2 *
        ((∫q : Paper.Overlap, vectorOverlapDeficit (n:=n) μ β t s ht.le q
          ∂(ν:Measure Paper.Overlap)) -
         (∫q : Paper.Overlap, vectorOverlapDeficit (n:=n) μ β t s ht.le q
          ∂(μ:Measure Paper.Overlap)))) (Icc (0:ℝ) 1) 0
  contact : (∀ν ∈ scalarFloor s,
      vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s) →
    (parisiFreeMeasure μ s).support ⊆
      Paper.overlapArgmin (fun q : Paper.Overlap => vectorOverlapDeficit (n:=n) μ β t s ht.le q) ∧
    (∀q ∈ (parisiFreeMeasure μ s).support, (q:ℝ) < 1 ∧
      (∫p, vectorSelfOverlap (n:=n) μ β t ht.le q p
        ∂vectorMeasureSpinPathLaw μ β t s ht.le) = (q:ℝ) ∧
      (∫p : VectorDisorderBrownianSample n × Configuration n,
        Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q p.1 *
          vectorMeasureHessianMatrix μ β t ht.le q p.1)
        ∂vectorMeasureSpinPathLaw μ β t s ht.le) ≤ (n:ℝ)/((1-t)*β^2))

theorem foundation_martingale_contact (hn : 0 < n) (β : ℝ) (hβ : 0 < β)
    (s : ℝ) (hs : s ∈ Ioc (0:ℝ) (1/2)) (t : ℝ) (ht : t ∈ Ico (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (hμ : μ ∈ scalarFloor s) :
    FoundationMartingaleContactTarget n μ β s t ht.2 := by
  have hs1 : s < 1 := by linarith [hs.2]
  refine {
    conditional_mean := foundation_terminal_spin_condExp μ β t s hβ.ne' ht.2
    gradient_identity := fun _ _ => rfl
    initial_zero := vectorMeasureSpinMean_zero μ β t ht.2.le
    martingale := foundation_joint_spin_mean_martingale μ β t s hβ.ne' ht.2
    stochastic_L2 := tendsto_vectorMeanLeftSum_L2 hn μ β t s hβ.ne' ht.2
    stochastic_probability := vectorMeasureSpinMean_stochastic_identity hn μ β t s hβ.ne' ht.2
    covariance_order := (contact_proposition hn β hβ s hs t ht μ hμ).1
    mean_C1_extension := ⟨vectorMeanOverlapPrimitive (n:=n) μ β t s ht.2.le,
      foundation_mean_overlap_C1_extension hn μ β t s hβ.ne' ht.2⟩
    first_variation := fun ν _ =>
      hasDerivWithinAt_vectorMeasureFunctional_mix_deficit hn μ ν β t s hβ.ne' ht.2
    contact := ?_ }
  intro hmin
  refine ⟨(vector_minimum_iff_free_support_argmin hn μ s ⟨hs.1.le,hs1.le⟩ hs1 hμ
    β t s hβ.ne' ht.2 hs.1.le).mp hmin, ?_⟩
  intro q hq
  have hc := (contact_proposition hn β hβ s hs t ht μ hμ).2 hmin q hq
  exact ⟨hc.1, vectorSelfOverlap_mean_on_free_support hn μ s β t ⟨hs.1,hs1⟩ hμ
    hβ.ne' ht.2 hmin q hq, hc.2.2⟩

end QuantitativeFollowup
