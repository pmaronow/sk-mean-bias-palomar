module
public import QuantitativePaper.VectorPhysicalFutureCovariance
public import FourPapersCommon.ConditionalPullback

@[expose] public section

/-! The future covariance integrand has its literal conditional meaning
on the marked terminal-spin law, as does the covariance at the current time. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorPhysicalSpinCovariance (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (p : VectorDisorderBrownianSample n × Configuration n) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  ((vectorMeasureSpinPathLaw μ β t a ht)[
    (fun z : VectorDisorderBrownianSample n × Configuration n => Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j)) |
    vectorSpinPast n (q:ℝ).toNNReal]) p -
    vectorMeasureSpinMean μ β t ht q p.1 i*vectorMeasureSpinMean μ β t ht q p.1 j

theorem vectorPhysicalSpinCovariance_eq_base (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) :
    ∀ᵐp ∂vectorMeasureSpinPathLaw (n:=n) μ β t a ht,
      vectorPhysicalSpinCovariance μ β t a ht q p = vectorMeasureSpinCovariance μ β t a ht q p.1 := by
  have he (i j : Fin n) := vectorMeasureSpinPathLaw_terminal_observable_condExp μ β t a ht q
    (fun σ => Paper.spinSign (σ i)*Paper.spinSign (σ j))
  filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr (he i)] with p hp
  ext i j
  unfold vectorPhysicalSpinCovariance vectorMeasureSpinCovariance
  rw [hp i j]

theorem integrable_vectorMeasureSpinCovariance_entry (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t ≤ 1) (u : Paper.Overlap) (i j : Fin n) :
    Integrable (fun p => vectorMeasureSpinCovariance μ β t a ht u p i j)
      (vectorMeasureDisorderTilt μ β t a) := by
  have hi := (((integrable_vectorMeasureConditionalVariance μ β t a ht u
    (EuclideanSpace.single i 1+EuclideanSpace.single j 1)).sub
    (integrable_vectorMeasureConditionalVariance μ β t a ht u (EuclideanSpace.single i 1))).sub
    (integrable_vectorMeasureConditionalVariance μ β t a ht u (EuclideanSpace.single j 1))).div_const 2
  apply hi.congr
  filter_upwards [vectorMeasureSpinCovariance_entry_polarization μ β t a ht u i j] with p hp
  exact hp.symm

theorem vectorPhysicalExpectedFutureCovariance_condExp (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (q u : Paper.Overlap) (ht : t ≤ 1) (hqu : q ≤ u) (i j : Fin n) :
    (vectorMeasureSpinPathLaw μ β t a ht)[
      (fun p => vectorPhysicalSpinCovariance μ β t a ht u p i j) |
        vectorSpinPast n (q:ℝ).toNNReal] =ᵐ[vectorMeasureSpinPathLaw μ β t a ht]
      fun p => vectorMeasureExpectedFutureCovarianceMatrix μ β t a q ht u p.1 i j := by
  let P := vectorMeasureDisorderTilt (n:=n) μ β t a
  let J := vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  letI := vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  let F := fun p => vectorMeasureSpinCovariance μ β t a ht u p i j
  have hF : Measurable F := by
    unfold F vectorMeasureSpinCovariance
    exact ((stronglyMeasurable_condExp.mono ((vectorBrownianFiltration n).le _)).measurable).sub
      (((adapted_vectorMeasureSpinMean_component μ β t ht u i).mono
        ((vectorBrownianFiltration n).le _) le_rfl).mul
        ((adapted_vectorMeasureSpinMean_component μ β t ht u j).mono
          ((vectorBrownianFiltration n).le _) le_rfl))
  have hbase := condExp_comp_of_measurePreserving J P Prod.fst
    (measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht)
    (vectorBrownianFiltration n (q:ℝ).toNNReal) ((vectorBrownianFiltration n).le _) F hF
    (integrable_vectorMeasureSpinCovariance_entry μ β t a ht u i j)
  have hactual := condExp_congr_ae (μ:=J) (m:=vectorSpinPast n (q:ℝ).toNNReal)
    ((vectorPhysicalSpinCovariance_eq_base μ β t a ht u).mono fun p hp => congrFun (congrFun hp i) j)
  have hfuture := (measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht).quasiMeasurePreserving.ae
    (vectorMeasureExpectedFutureCovarianceMatrix_condExp μ β t a q u ht hqu i j)
  exact hactual.trans (hbase.trans hfuture)

theorem vectorPhysicalHessian_future_covariance_integral (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap) :
    ∀ᵐp ∂vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le, ∀i j : Fin n,
      vectorMeasureHessianMatrix μ β t ht.le q p.1 i j =
        Paper.parisiCDF μ q*vectorPhysicalSpinCovariance μ β t a ht.le q p i j +
        ∫u : Paper.Overlap,
          if q < u then vectorMeasureExpectedFutureCovarianceMatrix μ β t a q ht.le u p.1 i j else 0
            ∂(μ:Measure Paper.Overlap) := by
  filter_upwards [vectorMeasureHessianMatrix_physical_future_covariance_integral μ β t a hβ ht q,
    vectorPhysicalSpinCovariance_eq_base μ β t a ht.le q] with p hp hc
  rw [hc]
  exact hp

end QuantitativePaper
