module
public import QuantitativePaper.VectorMeasureMarkedConditionalLaw
public import QuantitativePaper.VectorMeasureHessianCovariance
public import Mathlib.Probability.CondVar

@[expose] public section

/-! The directional covariance along the actual arbitrary-profile diffusion
is the genuine conditional variance of the marked terminal spin in its full
past. The literal Hessian sandwich therefore holds for that conditional
variance under the actual joint spin law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasureSpinPathLaw_direction_condExp (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (w : Field n) :
    (vectorMeasureSpinPathLaw μ β t a ht.le)[
      (fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2)|
        vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun p=>vectorMeasureMeanInDirection μ β t ht.le q w p.1 := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hi (l : Fin n) : Integrable
      (fun p : VectorDisorderBrownianSample n×Configuration n=>w l*Paper.spinSign (p.2 l)) J := by
    apply ((integrable_const (1:ℝ)).mono'
      (((measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ l))).comp
        measurable_snd).aestronglyMeasurable)
      (.of_forall fun p=>by
        change ‖Paper.spinSign (p.2 l)‖≤1
        rw [Real.norm_eq_abs,Paper.abs_spinSign])).const_mul
  have he (l : Fin n) : J[(fun p : VectorDisorderBrownianSample n×Configuration n=>
      w l*Paper.spinSign (p.2 l))|vectorSpinPast n (q:ℝ).toNNReal]=ᵐ[J]
      fun p=>w l*vectorMeasureSpinMean μ β t ht.le q p.1 l := by
    have hs:=(condExp_smul (μ:=J) (w l)
      (fun p : VectorDisorderBrownianSample n×Configuration n=>Paper.spinSign (p.2 l))
      (vectorSpinPast n (q:ℝ).toNNReal))
    filter_upwards [hs,vectorMeasureSpinPathLaw_spin_condExp μ β t a hβ ht q l] with p hp hspin
    change J[(fun p : VectorDisorderBrownianSample n×Configuration n=>
      w l*Paper.spinSign (p.2 l))|vectorSpinPast n (q:ℝ).toNNReal] p=
      w l*J[(fun p : VectorDisorderBrownianSample n×Configuration n=>
        Paper.spinSign (p.2 l))|vectorSpinPast n (q:ℝ).toNNReal] p at hp
    rw [hspin] at hp
    exact hp
  have hs:=condExp_finsetSum (μ:=J) (s:=Finset.univ) (fun l _=>hi l)
    (vectorSpinPast n (q:ℝ).toNNReal)
  have hsum : (∑l : Fin n,fun p : VectorDisorderBrownianSample n×Configuration n=>
      w l*Paper.spinSign (p.2 l))=(fun p=>∑l : Fin n,w l*Paper.spinSign (p.2 l)) := by
    funext p
    simp only [Finset.sum_apply]
  rw [hsum] at hs
  filter_upwards [hs,ae_all_iff.2 he] with p hp hall
  simp only [Finset.sum_apply] at hp
  change J[(fun p : VectorDisorderBrownianSample n×Configuration n=>
    ∑l : Fin n,w l*Paper.spinSign (p.2 l))|vectorSpinPast n (q:ℝ).toNNReal] p=
      ∑l : Fin n,w l*vectorMeasureSpinMean μ β t ht.le q p.1 l
  exact hp.trans (Finset.sum_congr rfl fun l _=>hall l)

theorem condVar_vectorMeasure_terminal_direction (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (w : Field n) :
    condVar (vectorSpinPast n (q:ℝ).toNNReal)
      (fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2)
      (vectorMeasureSpinPathLaw μ β t a ht.le)=ᵐ[vectorMeasureSpinPathLaw μ β t a ht.le]
      fun p=>vectorMeasureConditionalVariance μ β t a ht.le q w p.1 := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht.le
  have hi : MemLp (fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2) 2 J :=
    MemLp.of_bound (((measurable_of_finite (fieldDot w)).comp measurable_snd).aestronglyMeasurable)
      (vectorDirectionBound w) (.of_forall fun p=>by
        simpa only [Real.norm_eq_abs] using abs_fieldDot_le_directionBound w p.2)
  have hv:=condVar_ae_eq_condExp_sq_sub_sq_condExp (vectorSpinPast_le n (q:ℝ).toNNReal) hi
  have h1:=vectorMeasureSpinPathLaw_direction_condExp μ β t a hβ ht q w
  have h2:=vectorMeasureSpinPathLaw_terminal_observable_condExp μ β t a ht.le q
    (fun σ=>fieldDot w σ^2)
  filter_upwards [hv,h1,h2] with p hp h1p h2p
  change condVar (vectorSpinPast n (q:ℝ).toNNReal)
    (fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2) J p=
      J[(fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2)^2|
        vectorSpinPast n (q:ℝ).toNNReal] p-
      (J[(fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2)|
        vectorSpinPast n (q:ℝ).toNNReal] p)^2 at hp
  rw [h1p,show (fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2)^2=
    (fun p=>fieldDot w p.2^2) from rfl,h2p] at hp
  exact hp

theorem vectorMeasureHessian_physical_condVar_bounds (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (w : Field n) :
    ∀ᵐp ∂vectorMeasureSpinPathLaw μ β t a ht.le,
      Paper.parisiCDF μ q*condVar (vectorSpinPast n (q:ℝ).toNNReal)
          (fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2)
          (vectorMeasureSpinPathLaw μ β t a ht.le) p≤
        vectorMeasureHessianQuadratic μ β t ht.le q w p.1 ∧
      vectorMeasureHessianQuadratic μ β t ht.le q w p.1≤
        condVar (vectorSpinPast n (q:ℝ).toNNReal)
          (fun p : VectorDisorderBrownianSample n×Configuration n=>fieldDot w p.2)
          (vectorMeasureSpinPathLaw μ β t a ht.le) p := by
  have he:=condVar_vectorMeasure_terminal_direction μ β t a hβ ht q w
  have hb:=(measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).quasiMeasurePreserving.ae
    (vectorMeasureHessian_conditionalVariance_bounds μ β t a hβ ht q w)
  filter_upwards [he,hb] with p hp hb
  rw [hp]
  exact hb

end QuantitativePaper
