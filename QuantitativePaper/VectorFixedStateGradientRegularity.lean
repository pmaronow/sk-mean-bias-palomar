module
public import QuantitativePaper.VectorFixedStateGradientCells
public import QuantitativePaper.VectorFiniteCellJointMeasurable

@[expose] public section

/-! Genuine continuity, measurability, and deterministic bounds for the
finite gradient squares and energies along the fixed arbitrary-profile state.
These are available at both endpoints of each finite cell. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def vectorFiniteCellGradientDerivativeBound (s : RSBScheme k) (β t : ℝ) (i : ℕ) (l : Fin n) : ℝ≥0 :=
  ((vectorFiniteGradientResponseData (n:=n) s β t i l).jointBounds (s.m i)).responsePower

theorem abs_vectorFiniteCellGradient_component_global (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (r : ℝ) (x : Field n) (l : Fin n) :
    |gradient (vectorFiniteCellPotential s β t p i r) x l|≤1 := by
  rw [vectorFiniteCellGradient_eq_response]
  exact abs_vectorStepResponse_le _ _ _ (vectorRecursion_lipschitz s β t p (k+1-i)) _ _ 1
    (fun y=>vectorMagnetization_component_bound s β t p (k+1-i) y l) x

theorem norm_fderiv_vectorFiniteCellGradient_component_global (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (r : ℝ) (x : Field n) (l : Fin n) :
    ‖fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t p i r) y l) x‖≤
      vectorFiniteCellGradientDerivativeBound s β t i l := by
  have hg : (fun y=>gradient (vectorFiniteCellPotential s β t p i r) y l)=
      vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t p (k+1-i))
        (fun y=>vectorMagnetization s β t p (k+1-i) y l) :=
    funext fun y=>vectorFiniteCellGradient_eq_response s β t p i r y l
  rw [hg,←norm_iteratedFDeriv_one]
  let h:=(vectorFiniteGradientResponseData (n:=n) s β t i l).jointBounds (s.m i)
  change ‖iteratedFDeriv ℝ 1 (vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
    (vectorRecursion s β t p (k+1-i)) (fun y=>vectorMagnetization s β t p (k+1-i) y l)) x‖≤h.responsePower
  simpa only [pow_one,VectorJointBackwardBounds.fieldBounds] using
    (h.fieldBounds p).responseJets (((1-t)*β^2)*(s.q (i+1)-r)) 1 le_rfl (by omega) x

theorem continuous_vectorFixedStateCellGradient_path (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r : ℝ≥0=>gradient (vectorFiniteCellPotential s β t sample.1 i r)
      (vectorMeasureState μ β t ht r sample) l) := by
  have hg : Continuous (fun z : ℝ×Field n=>gradient (vectorFiniteCellPotential s β t sample.1 i z.1) z.2 l) :=
    continuous_vectorFiniteCellPotential_gradient_coordinate (n:=n) s β t sample.1 i l
  have hmap : Continuous (fun r : ℝ≥0=>((r : ℝ),vectorMeasureState μ β t ht r sample)) :=
    NNReal.continuous_coe.prodMk (continuous_vectorMeasureState μ β t ht sample)
  simpa only [Function.comp_def] using hg.comp hmap

theorem measurable_vectorFixedStateCellGradient (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ≥0) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>gradient
      (vectorFiniteCellPotential s β t sample.1 i r) (vectorMeasureState μ β t ht r sample) l) := by
  have hX : Measurable (vectorMeasureState (n:=n) μ β t ht r):=
    ((stronglyAdapted_vectorMeasureState (n:=n) μ β t ht r).measurable).mono
      ((vectorBrownianFiltration n).le r) le_rfl
  exact (EuclideanSpace.proj l).continuous.measurable.comp
    ((continuous_vectorFiniteCell_gradient_parameter (n:=n) s β t i r).measurable.comp
      (measurable_fst.prodMk hX))

theorem continuous_vectorFixedStateCellGradientDerivative_path (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r : ℝ≥0=>fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i r) y l)
      (vectorMeasureState μ β t ht r sample)) := by
  let data:=(vectorFiniteGradientResponseData (n:=n) s β t i l).fieldData sample.1
  have hc:=data.continuous_response_first (s.m i)
  have hmap : Continuous (fun r : ℝ≥0=>(((1-t)*β^2*(s.q (i+1)-r)),
      vectorMeasureState μ β t ht r sample)) :=
    (show Continuous (fun r : ℝ≥0=>((1-t)*β^2*(s.q (i+1)-r))) from by fun_prop).prodMk
      (continuous_vectorMeasureState μ β t ht sample)
  have hh:=hc.comp hmap
  have hg (r : ℝ≥0) : (fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i r) y l)=
      vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t sample.1 (k+1-i))
        (fun y=>vectorMagnetization s β t sample.1 (k+1-i) y l) :=
    funext fun y=>vectorFiniteCellGradient_eq_response s β t sample.1 i r y l
  simp_rw [hg]
  exact hh

theorem measurable_vectorFixedStateCellGradientDerivative (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ≥0) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>fderiv ℝ
      (fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i r) y l)
      (vectorMeasureState μ β t ht r sample)) := by
  have hX : Measurable (vectorMeasureState (n:=n) μ β t ht r):=
    ((stronglyAdapted_vectorMeasureState (n:=n) μ β t ht r).measurable).mono
      ((vectorBrownianFiltration n).le r) le_rfl
  have hc:=(vectorFiniteGradientResponseData (n:=n) s β t i l).continuous_response_first_parameter
    (s.m i) (((1-t)*β^2)*(s.q (i+1)-r))
  have hh:=hc.measurable.comp (measurable_fst.prodMk hX)
  have hg (sample : VectorDisorderBrownianSample n) :
      (fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i r) y l)=
      vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t sample.1 (k+1-i))
        (fun y=>vectorMagnetization s β t sample.1 (k+1-i) y l) :=
    funext fun y=>vectorFiniteCellGradient_eq_response s β t sample.1 i r y l
  simp_rw [hg]
  exact hh

theorem continuous_vectorFixedStateCellGradientEnergy_path (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r : ℝ≥0=>vectorFixedStateCellGradientEnergy s μ β t ht i r sample l) := by
  unfold vectorFixedStateCellGradientEnergy
  apply continuous_finsetSum
  intro j _
  exact (((continuous_vectorFixedStateCellGradientDerivative_path s μ β t ht i l sample).clm_apply
    continuous_const).pow 2)

theorem measurable_vectorFixedStateCellGradientEnergy (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ≥0) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>vectorFixedStateCellGradientEnergy s μ β t ht i r sample l) := by
  unfold vectorFixedStateCellGradientEnergy
  apply Finset.measurable_sum
  intro j _
  exact ((show Measurable (fun L : Field n→L[ℝ]ℝ=>L (EuclideanSpace.single j 1)) from by fun_prop).comp
    (measurable_vectorFixedStateCellGradientDerivative s μ β t ht i l r)).pow_const 2

theorem vectorFixedStateCellGradientEnergy_nonneg_le (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    0≤vectorFixedStateCellGradientEnergy s μ β t ht i r sample l ∧
    vectorFixedStateCellGradientEnergy s μ β t ht i r sample l≤
      (n : ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l : ℝ)^2 := by
  refine ⟨Finset.sum_nonneg fun _ _=>sq_nonneg _,?_⟩
  let A:=vectorFiniteCellGradientDerivativeBound s β t i l
  have he (j : Fin n) : |fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i r) y l)
      (vectorMeasureState μ β t ht r sample) (EuclideanSpace.single j 1)|≤A := by
    simpa only [Real.norm_eq_abs,PiLp.norm_single,norm_one,mul_one] using
      ((fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i r) y l)
        (vectorMeasureState μ β t ht r sample)).le_opNorm (EuclideanSpace.single j 1)).trans
      (mul_le_mul_of_nonneg_right
        (norm_fderiv_vectorFiniteCellGradient_component_global s β t sample.1 i r _ l) (norm_nonneg _))
  calc
    _≤∑_j : Fin n,(A : ℝ)^2:=Finset.sum_le_sum fun j _=>by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he j) 2
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,A]

end QuantitativePaper
