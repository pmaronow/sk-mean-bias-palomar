module
public import QuantitativeFollowup.VectorMeanMartingale
public import QuantitativePaper.VectorMeasureSpinPast

@[expose] public section

/-! The actual terminal Gibbs spin and its full-vector conditional mean
under the marked physical law. The retained filtration contains the whole
disorder and Brownian past, and excludes the terminal spin. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def foundationSpinFiltration (n : ℕ) :
    Filtration Paper.Overlap (inferInstance :
      MeasurableSpace (VectorDisorderBrownianSample n × Configuration n)) where
  seq q := vectorSpinPast n (q:ℝ).toNNReal
  mono' _ _ h := MeasurableSpace.comap_mono
    ((vectorBrownianFiltration n).mono (Real.toNNReal_mono h))
  le' q := vectorSpinPast_le n (q:ℝ).toNNReal

theorem foundation_terminal_spin_condExp (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap) :
    (vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le)[
      (fun p : VectorDisorderBrownianSample n × Configuration n => spinVector p.2) |
      foundationSpinFiltration n q] =ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun p => vectorMeasureSpinMean μ β t ht.le q p.1 := by
  let P := vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  letI := vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hm : Measurable (fun p : VectorDisorderBrownianSample n × Configuration n =>
      spinVector p.2) := (measurable_of_finite spinVector).comp measurable_snd
  have hi : Integrable (fun p : VectorDisorderBrownianSample n × Configuration n =>
      spinVector p.2) P := (integrable_const (Real.sqrt (n:ℝ))).mono'
    hm.aestronglyMeasurable (.of_forall fun p => (norm_spinVector p.2).le)
  have hc (l : Fin n) :
      (fun p => (P[(fun p : VectorDisorderBrownianSample n × Configuration n =>
        spinVector p.2) | foundationSpinFiltration n q]) p l) =ᵐ[P]
      fun p => vectorMeasureSpinMean μ β t ht.le q p.1 l := by
    have hproj := (EuclideanSpace.proj l).comp_condExp_comm
      (m:=foundationSpinFiltration n q) hi
    have hspin := vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht q l
    exact hproj.trans hspin
  filter_upwards [ae_all_iff.mpr hc] with p hp
  ext l
  exact hp l

theorem foundation_joint_spin_mean_martingale (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) :
    Martingale (fun q : Paper.Overlap => fun p :
        VectorDisorderBrownianSample n × Configuration n =>
      vectorMeasureSpinMean μ β t ht.le q p.1)
      (foundationSpinFiltration n) (vectorMeasureSpinPathLaw μ β t a ht.le) := by
  letI := vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  apply (martingale_condExp (fun p : VectorDisorderBrownianSample n × Configuration n =>
    spinVector p.2) (foundationSpinFiltration n)
    (vectorMeasureSpinPathLaw μ β t a ht.le)).congr
  · intro q
    exact ((adapted_vectorMeasureSpinMean μ β t ht.le q).comp
      (comap_measurable Prod.fst)).stronglyMeasurable
  · intro q
    exact foundation_terminal_spin_condExp μ β t a hβ ht q

end QuantitativeFollowup
