module
public import QuantitativePaper.VectorFiniteCellHeatIto
public import QuantitativePaper.VectorNonnegativeTimeIntegral

@[expose] public section

/-! Literal Gaussian-heat form of the finite-cell Duhamel identity. Endpoint
integrability follows from the proved Itô identity, rather than Bochner defaults. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

def vectorFiniteCellHeatValue {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (a r : ℝ) (x : Field n) : ℝ :=
  ∫ z,vectorFiniteCellPotential s β t p i r
    (fieldShift ((1-t)*β^2*(r-a)) x z) ∂fieldGaussian n

def vectorFiniteCellGradientHeat {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (a r : ℝ) (x : Field n) : ℝ :=
  ∫ z,‖gradient (vectorFiniteCellPotential s β t p i r)
    (fieldShift ((1-t)*β^2*(r-a)) x z)‖^2 ∂fieldGaussian n

theorem measurable_vectorFiniteCellGradientHeat {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (a : ℝ) (x : Field n) :
    Measurable (fun r => vectorFiniteCellGradientHeat s β t p i a r x) := by
  have hg : Measurable (fun z : ℝ×Field n =>
      ‖gradient (vectorFiniteCellPotential s β t p i z.1)
        (fieldShift ((1-t)*β^2*(z.1-a)) x z.2)‖^2) := by
    have hh := (continuous_vectorFiniteCellPotential_gradient s β t p i).measurable.comp
      (show Measurable (fun z : ℝ×Field n => (z.1,fieldShift ((1-t)*β^2*(z.1-a)) x z.2)) from by
        unfold fieldShift;fun_prop)
    exact hh.norm.pow_const 2
  exact (hg.stronglyMeasurable.integral_prod_right' (ν := fieldGaussian n)).measurable

theorem norm_gradient_eq_fderiv {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E→ℝ) (x : E) :
    ‖gradient f x‖=‖fderiv ℝ f x‖ := by
  simpa only [toDual_gradient] using (InnerProductSpace.toDual ℝ E).norm_map (gradient f x) |>.symm

theorem intervalIntegrable_vectorFiniteCellGradientHeat {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (i : ℕ) (a l r : ℝ) (x : Field n) :
    IntervalIntegrable (fun q => vectorFiniteCellGradientHeat s β t p i a q x) volume l r := by
  obtain ⟨K,hK,hB⟩ := vectorFiniteCellPotential_uniform_field_jets (n := n) s β t i 1
  have hb (q : ℝ) : |vectorFiniteCellGradientHeat s β t p i a q x|≤K^2 := by
    have h := norm_integral_le_of_norm_le_const (μ := fieldGaussian n)
      (f := fun z => ‖gradient (vectorFiniteCellPotential s β t p i q)
        (fieldShift ((1-t)*β^2*(q-a)) x z)‖^2) (C := K^2) (Eventually.of_forall fun z => by
          rw [Real.norm_of_nonneg (sq_nonneg _),norm_gradient_eq_fderiv,←norm_iteratedFDeriv_one]
          have hh := hB q 1 le_rfl le_rfl p (fieldShift ((1-t)*β^2*(q-a)) x z)
          simp only [pow_one] at hh
          nlinarith [norm_nonneg (iteratedFDeriv ℝ 1 (vectorFiniteCellPotential s β t p i q)
            (fieldShift ((1-t)*β^2*(q-a)) x z))])
    simpa only [vectorFiniteCellGradientHeat,Real.norm_eq_abs,probReal_univ,mul_one] using h
  apply IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := K^2))
    (measurable_vectorFiniteCellGradientHeat s β t p i a x).aestronglyMeasurable
  exact Eventually.of_forall hb

theorem vectorFiniteCell_heat_identity {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1)
    (a : ℝ) (T : ℝ≥0) (hT : a+(T : ℝ) ≤ s.q (i+1)) (x : Field n) :
    vectorFiniteCellHeatValue s β t p i a (a+T) x-vectorFiniteCellPotential s β t p i a x=
      -((1-t)*β^2)/2*(s.m i)*∫ r in a..a+(T : ℝ),
        vectorFiniteCellGradientHeat s β t p i a r x := by
  let c := (1-t)*β^2
  have hc : 0≤c := by dsimp only [c];positivity
  have hh := vectorFiniteCell_heat_ito s β t hβ ht p i hi a T hT x
  have hiEnd : Integrable (fun sample => vectorFiniteCellPotential s β t p i (a+T)
      (vectorHeatState (Real.sqrt c) x T sample)) (vectorDisorderBrownianMeasure n) := by
    apply (hh.1.add (integrable_const (vectorFiniteCellPotential s β t p i a x))).congr
    exact Eventually.of_forall (fun sample => by simp only [Pi.add_apply];ring)
  have hVal := integral_vectorHeatState_eq_heat c hc x T (vectorFiniteCellPotential s β t p i (a+T))
    ((contDiff_vectorColeHopfStep_recursion_field s β t _ _ p _).continuous.measurable)
  have hGrad (r : ℝ≥0) :
      (∫ sample,‖gradient (vectorFiniteCellPotential s β t p i (a+r))
        (vectorHeatState (Real.sqrt c) x r sample)‖^2 ∂vectorDisorderBrownianMeasure n)=
      vectorFiniteCellGradientHeat s β t p i a (a+r) x := by
    have hme : Measurable (fun y : Field n => ‖gradient (vectorFiniteCellPotential s β t p i (a+r)) y‖^2) :=
      (((continuous_vectorFiniteCellPotential_gradient s β t p i).comp
        (continuous_const.prodMk continuous_id)).norm.pow 2).measurable
    simpa only [vectorFiniteCellGradientHeat,add_sub_cancel_left,c] using
      integral_vectorHeatState_eq_heat c hc x r _ hme
  have hEq := hh.2
  rw [integral_sub hiEnd (integrable_const _)] at hEq
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at hEq
  have hVal' : (∫ sample,vectorFiniteCellPotential s β t p i (a+T)
      (vectorHeatState (Real.sqrt c) x T sample) ∂vectorDisorderBrownianMeasure n)=
      vectorFiniteCellHeatValue s β t p i a (a+T) x := by
    simpa only [vectorFiniteCellHeatValue,add_sub_cancel_left,c] using hVal
  rw [hVal'] at hEq
  change vectorFiniteCellHeatValue s β t p i a (a+T) x-vectorFiniteCellPotential s β t p i a x=
    -c/2*s.m i*(∫ r in Ioc 0 T,(∫ sample,‖gradient (vectorFiniteCellPotential s β t p i (a+r))
      (vectorHeatState (Real.sqrt c) x r sample)‖^2 ∂vectorDisorderBrownianMeasure n)
      ∂nonnegativeLebesgueMeasure) at hEq
  simp_rw [hGrad] at hEq
  rw [vectorNonnegativeTimeIntegral_eq_shifted_interval _
    (measurable_vectorFiniteCellGradientHeat s β t p i a x)] at hEq
  exact hEq

end QuantitativePaper
