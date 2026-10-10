module
public import QuantitativePaper.VectorFixedStateGradientRegularity

@[expose] public section

/-! Joint measurability and global deterministic envelopes for the genuine
finite gradient-square generator on the fixed arbitrary-profile diffusion.
The envelopes permit closed-cell endpoint passage and Fubini without a
stochastic regularity premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem norm_vectorFiniteCellGradient_global (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (r : ℝ) (x : Field n) :
    ‖gradient (vectorFiniteCellPotential s β t p i r) x‖≤Real.sqrt n := by
  rw [EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  calc
    _≤∑_l : Fin n,(1 : ℝ) := by
      apply Finset.sum_le_sum
      intro l _
      have h:=abs_vectorFiniteCellGradient_component_global s β t p i r x l
      simpa only [Real.norm_eq_abs,sq_abs,one_pow] using
        pow_le_pow_left₀ (abs_nonneg _) h 2
    _=_:=by simp

theorem measurable_uncurry_vectorFixedStateCellGradient (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>gradient
      (vectorFiniteCellPotential s β t z.2.1 i z.1) (vectorMeasureState μ β t ht z.1 z.2) l) := by
  exact measurable_uncurry_of_continuous_of_measurable
    (continuous_vectorFixedStateCellGradient_path s μ β t ht i l)
    (measurable_vectorFixedStateCellGradient s μ β t ht i l)

theorem measurable_uncurry_vectorFixedStateCellGradientDerivative (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>fderiv ℝ
      (fun y=>gradient (vectorFiniteCellPotential s β t z.2.1 i z.1) y l)
      (vectorMeasureState μ β t ht z.1 z.2)) := by
  exact measurable_uncurry_of_continuous_of_measurable
    (continuous_vectorFixedStateCellGradientDerivative_path s μ β t ht i l)
    (measurable_vectorFixedStateCellGradientDerivative s μ β t ht i l)

theorem measurable_uncurry_vectorFixedStateCellGradientEnergy (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      vectorFixedStateCellGradientEnergy s μ β t ht i z.1 z.2 l) := by
  exact measurable_uncurry_of_continuous_of_measurable
    (continuous_vectorFixedStateCellGradientEnergy_path s μ β t ht i l)
    (measurable_vectorFixedStateCellGradientEnergy s μ β t ht i l)

theorem measurable_uncurry_vectorFixedStateCellFullGradient (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>gradient
      (vectorFiniteCellPotential s β t z.2.1 i z.1) (vectorMeasureState μ β t ht z.1 z.2)) := by
  have hh : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>fun l : Fin n=>
      gradient (vectorFiniteCellPotential s β t z.2.1 i z.1)
        (vectorMeasureState μ β t ht z.1 z.2) l) :=
    Measurable.of_eval fun l=>measurable_uncurry_vectorFixedStateCellGradient s μ β t ht i l
  exact (show Measurable (WithLp.toLp 2 : (Fin n→ℝ)→Field n) from by fun_prop).comp hh

theorem measurable_uncurry_vectorFixedStateCellGradientSquareSource (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      vectorFixedStateCellGradientSquareSource s μ β t ht i z.1 z.2 l) := by
  have hg:=measurable_uncurry_vectorFixedStateCellGradient s μ β t ht i l
  have hD:=measurable_uncurry_vectorFixedStateCellGradientDerivative s μ β t ht i l
  have hU:=measurable_uncurry_vectorFixedStateCellFullGradient (n:=n) s μ β t ht i
  have hd:=measurable_uncurry_vectorAdditiveDrift (vectorMeasureDriftData (n:=n) μ β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1
  have hδ:=hd.sub ((hU.const_smul (s.m i)).const_smul ((1-t)*β^2))
  have hE:=measurable_uncurry_vectorFixedStateCellGradientEnergy s μ β t ht i l
  have hEval : Measurable (fun z : (Field n→L[ℝ]ℝ)×Field n=>z.1 z.2) := by fun_prop
  exact ((measurable_const.mul hg).mul (hEval.comp (hD.prodMk hδ))).add (measurable_const.mul hE)

theorem norm_vectorFixedStateCellGradientSquareSource_le (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (l : Fin n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorFixedStateCellGradientSquareSource s μ β t ht i r sample l‖≤
      ((1-t)*β^2)*(4*(vectorFiniteCellGradientDerivativeBound s β t i l : ℝ)*Real.sqrt n+
        (n : ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l : ℝ)^2) := by
  let c:ℝ:=(1-t)*β^2
  let A:ℝ:=vectorFiniteCellGradientDerivativeBound s β t i l
  let X:=vectorMeasureState μ β t ht r sample
  let U:=vectorFiniteCellPotential s β t sample.1 i r
  let g:=fun y=>gradient U y l
  let d:=vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1 r sample
  have hc:0≤c:=mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have hA:0≤A:=NNReal.coe_nonneg _
  have hg:|g X|≤1:=abs_vectorFiniteCellGradient_component_global s β t sample.1 i r X l
  have hD:‖fderiv ℝ g X‖≤A:=norm_fderiv_vectorFiniteCellGradient_component_global s β t sample.1 i r X l
  have hd:‖d‖≤c*Real.sqrt n:=norm_vectorAdditiveDrift_le _ _ _ _ _ _
  have hU:‖gradient U X‖≤Real.sqrt n:=norm_vectorFiniteCellGradient_global s β t sample.1 i r X
  have hm:|s.m i|≤1:=by rw [abs_of_nonneg (s.m_nonneg hi)];exact s.m_le_one hi
  have hδ:‖d-c • ((s.m i) • gradient U X)‖≤2*c*Real.sqrt n:=by
    calc
      _≤‖d‖+‖c • ((s.m i) • gradient U X)‖:=norm_sub_le _ _
      _=‖d‖+c*(|s.m i| *‖gradient U X‖):=by
        rw [norm_smul,norm_smul,Real.norm_of_nonneg hc,Real.norm_eq_abs]
      _≤c*Real.sqrt n+c*(1*Real.sqrt n):=by gcongr
      _=_:=by ring
  have hEval:|fderiv ℝ g X (d-c • ((s.m i) • gradient U X))|≤A*(2*c*Real.sqrt n):=by
    rw [←Real.norm_eq_abs]
    exact ((fderiv ℝ g X).le_opNorm _).trans (mul_le_mul hD hδ (norm_nonneg _) hA)
  have hE:=vectorFixedStateCellGradientEnergy_nonneg_le s μ β t ht i l r sample
  have hEb : vectorFixedStateCellGradientEnergy s μ β t ht i r sample l≤(n : ℝ)*A^2:=hE.2
  change ‖2*g X*fderiv ℝ g X (d-c • ((s.m i) • gradient U X))+
    c*vectorFixedStateCellGradientEnergy s μ β t ht i r sample l‖≤_
  calc
    _≤|2*g X*fderiv ℝ g X (d-c • ((s.m i) • gradient U X))|+
      |c*vectorFixedStateCellGradientEnergy s μ β t ht i r sample l|:=norm_add_le _ _
    _=2*|g X| *|fderiv ℝ g X (d-c • ((s.m i) • gradient U X))|+
      c*vectorFixedStateCellGradientEnergy s μ β t ht i r sample l:=by
      rw [abs_mul,abs_mul,show |(2 : ℝ)|=2 by norm_num,abs_mul,
        abs_of_nonneg hc,abs_of_nonneg hE.1]
    _≤2*1*(A*(2*c*Real.sqrt n))+c*((n : ℝ)*A^2):=by gcongr
    _=_:=by ring

end QuantitativePaper
