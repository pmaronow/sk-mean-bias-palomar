module
public import QuantitativePaper.VectorFixedStateHessianCells
public import QuantitativePaper.VectorFixedStateGradientSourceRegularity

@[expose] public section

/-! Actual closed-endpoint regularity and measurable bounded reaction sources
for a finite Hessian diagonal along the fixed arbitrary-profile state. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem fderiv_vectorFiniteCellHessianDiagonal_eq_response (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (r : ℝ) (x : Field n) (l : Fin n) :
    fderiv ℝ (fun y=>vectorFiniteCellHessianDiagonal s β t p i r y l) x=
      fderiv ℝ (vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t p (k+1-i))
        (fun y=>vectorFiniteHessianResponseObservable s β t i l (p,y))) x-
      (s.m i) • ((2*gradient (vectorFiniteCellPotential s β t p i r) x l) •
        fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t p i r) y l) x) := by
  let R:=vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
    (vectorRecursion s β t p (k+1-i)) (fun y=>vectorFiniteHessianResponseObservable s β t i l (p,y))
  let g : Field n→ℝ:=fun y=>gradient (vectorFiniteCellPotential s β t p i r) y l
  have hR : Differentiable ℝ R:=
    ((((vectorFiniteHessianResponseData s β t i l).fieldData p).bounds (s.m i)).responseRegularity _).differentiable
      (by norm_num)
  have hg : Differentiable ℝ g:=
    (contDiff_vectorFiniteCellGradient_component s β t p i r l).differentiable (by simp)
  have hH : (fun y=>vectorFiniteCellHessianDiagonal s β t p i r y l)=fun y=>R y-(s.m i)*g y^2:=by
    funext y
    exact vectorFiniteCellHessian_diagonal_eq_response s β t p i r y l
  have hh:=((hR x).hasFDerivAt.sub (((hg.pow 2) x).hasFDerivAt.const_smul (s.m i))).fderiv
  change fderiv ℝ (fun y=>R y-(s.m i)*g y^2) x=
    fderiv ℝ R x-(s.m i) • fderiv ℝ (fun y=>g y^2) x at hh
  rw [hH,hh,fderiv_square g hg]

def vectorFiniteCellHessianDerivativeBound (s : RSBScheme k) (β t : ℝ) (i : ℕ) (l : Fin n) : ℝ :=
  (((vectorFiniteHessianResponseData (n:=n) s β t i l).jointBounds (s.m i)).responsePower : ℝ)+
    2*|s.m i| *(vectorFiniteCellGradientDerivativeBound s β t i l : ℝ)

theorem vectorFiniteCellHessianDerivativeBound_nonneg (s : RSBScheme k) (β t : ℝ) (i : ℕ) (l : Fin n) :
    0≤vectorFiniteCellHessianDerivativeBound s β t i l := by
  unfold vectorFiniteCellHessianDerivativeBound
  positivity

theorem norm_fderiv_vectorFiniteCellHessianDiagonal_global (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (r : ℝ) (x : Field n) (l : Fin n) :
    ‖fderiv ℝ (fun y=>vectorFiniteCellHessianDiagonal s β t p i r y l) x‖≤
      vectorFiniteCellHessianDerivativeBound s β t i l := by
  let h:=(vectorFiniteHessianResponseData (n:=n) s β t i l).jointBounds (s.m i)
  have hR : ‖fderiv ℝ (vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t p (k+1-i))
        (fun y=>vectorFiniteHessianResponseObservable s β t i l (p,y))) x‖≤h.responsePower:=by
    rw [←norm_iteratedFDeriv_one]
    simpa only [pow_one,VectorJointBackwardBounds.fieldBounds] using
      (h.fieldBounds p).responseJets (((1-t)*β^2)*(s.q (i+1)-r)) 1 le_rfl (by omega) x
  have hg:=abs_vectorFiniteCellGradient_component_global s β t p i r x l
  have hD:=norm_fderiv_vectorFiniteCellGradient_component_global s β t p i r x l
  rw [fderiv_vectorFiniteCellHessianDiagonal_eq_response]
  calc
    _≤_+‖(s.m i) • ((2*gradient (vectorFiniteCellPotential s β t p i r) x l) •
        fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t p i r) y l) x)‖:=norm_sub_le _ _
    _≤h.responsePower+|s.m i| *(2*1*(vectorFiniteCellGradientDerivativeBound s β t i l : ℝ)):=by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,show |(2 : ℝ)|=2 by norm_num]
      gcongr
    _=_:=by dsimp [vectorFiniteCellHessianDerivativeBound,h];ring

theorem abs_vectorFiniteCellHessianDiagonal_global (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1) (r : ℝ) (x : Field n) (l : Fin n) :
    |vectorFiniteCellHessianDiagonal s β t p i r x l|≤2 := by
  have hR:=vectorStepResponse_recursion_heat_bounds (n:=n) s β t (((1-t)*β^2)*(s.q (i+1)-r))
    (s.m i) p (k+1-i) (s.m_nonneg hi) (s.m_le_one hi) x l
  have hg:=abs_vectorFiniteCellGradient_component_global s β t p i r x l
  have hm : |s.m i|≤1:=by rw [abs_of_nonneg (s.m_nonneg hi)];exact s.m_le_one hi
  unfold vectorFiniteCellHessianDiagonal
  rw [vectorFiniteCellHessian_diagonal_eq_response]
  calc
    _≤|vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t p (k+1-i))
        (fun y=>vectorFiniteHessianResponseObservable s β t i l (p,y)) x|+
      |(s.m i)*(gradient (vectorFiniteCellPotential s β t p i r) x l)^2|:=by
        simpa only [Real.norm_eq_abs] using norm_sub_le
          (vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
            (vectorRecursion s β t p (k+1-i))
            (fun y=>vectorFiniteHessianResponseObservable s β t i l (p,y)) x)
          ((s.m i)*(gradient (vectorFiniteCellPotential s β t p i r) x l)^2)
    _≤1+1*1^2:=by
      rw [abs_mul,abs_pow]
      gcongr
      · dsimp only [vectorFiniteHessianResponseObservable,Prod.fst,Prod.snd]
        rw [abs_of_nonneg hR.1]
        exact hR.2
    _=2:=by norm_num

theorem continuous_vectorFixedStateCellHessian_path (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r : ℝ≥0=>vectorFiniteCellHessianDiagonal s β t sample.1 i r
      (vectorMeasureState μ β t ht r sample) l) := by
  have h:=continuous_vectorFiniteCellPotential_hessian_diagonal (n:=n) s β t sample.1 i l
  have hm : Continuous (fun r : ℝ≥0=>((r : ℝ),vectorMeasureState μ β t ht r sample)):=
    NNReal.continuous_coe.prodMk (continuous_vectorMeasureState μ β t ht sample)
  have he : (fun r : ℝ≥0=>vectorFiniteCellHessianDiagonal s β t sample.1 i r
      (vectorMeasureState μ β t ht r sample) l)=
      (fun r : ℝ≥0=>directionalHessian (vectorFiniteCellPotential s β t sample.1 i r)
        (vectorMeasureState μ β t ht r sample) (EuclideanSpace.single l 1)):=by
    funext r
    exact hessianOperator_euclidean_diagonal (vectorFiniteCellPotential (n:=n) s β t sample.1 i r)
      (vectorMeasureState μ β t ht r sample) l
  rw [he]
  simpa only [Function.comp_def] using h.comp hm

theorem measurable_vectorFixedStateCellHessian (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ≥0) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>vectorFiniteCellHessianDiagonal s β t sample.1 i r
      (vectorMeasureState μ β t ht r sample) l) := by
  have hX : Measurable (vectorMeasureState (n:=n) μ β t ht r):=
    ((stronglyAdapted_vectorMeasureState (n:=n) μ β t ht r).measurable).mono
      ((vectorBrownianFiltration n).le r) le_rfl
  have hH:=((continuous_vectorFiniteCell_hessian_parameter (n:=n) s β t i r).measurable.comp
    (measurable_fst.prodMk hX))
  have he : (fun sample : VectorDisorderBrownianSample n=>vectorFiniteCellHessianDiagonal s β t sample.1 i r
      (vectorMeasureState μ β t ht r sample) l)=
      (fun sample=>vectorHessian (vectorFiniteCellPotential s β t sample.1 i r)
        (vectorMeasureState μ β t ht r sample) (EuclideanSpace.single l 1) (EuclideanSpace.single l 1)):=by
    funext sample
    exact (hessianOperator_euclidean_diagonal _ _ _).trans (by rfl)
  rw [he]
  exact (show Measurable (fun H : Field n→L[ℝ]Field n→L[ℝ]ℝ=>
    H (EuclideanSpace.single l 1) (EuclideanSpace.single l 1)) from by fun_prop).comp hH

theorem continuous_vectorFixedStateCellHessianDerivative_path (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r : ℝ≥0=>fderiv ℝ (fun y=>vectorFiniteCellHessianDiagonal s β t sample.1 i r y l)
      (vectorMeasureState μ β t ht r sample)) := by
  let data:=(vectorFiniteHessianResponseData (n:=n) s β t i l).fieldData sample.1
  have hmap : Continuous (fun r : ℝ≥0=>(((1-t)*β^2*(s.q (i+1)-r)),
      vectorMeasureState μ β t ht r sample)):=
    (show Continuous (fun r : ℝ≥0=>((1-t)*β^2*(s.q (i+1)-r))) from by fun_prop).prodMk
      (continuous_vectorMeasureState μ β t ht sample)
  simp_rw [fderiv_vectorFiniteCellHessianDiagonal_eq_response]
  have hsub:=((data.continuous_response_first (s.m i)).comp hmap).sub
    ((continuous_const (y:=s.m i)).smul (((continuous_vectorFixedStateCellGradient_path s μ β t ht i l sample).const_mul 2).smul
      (continuous_vectorFixedStateCellGradientDerivative_path s μ β t ht i l sample)))
  convert hsub using 1
  funext r
  rfl

theorem measurable_vectorFixedStateCellHessianDerivative (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ≥0) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>fderiv ℝ
      (fun y=>vectorFiniteCellHessianDiagonal s β t sample.1 i r y l)
      (vectorMeasureState μ β t ht r sample)) := by
  have hX : Measurable (vectorMeasureState (n:=n) μ β t ht r):=
    ((stronglyAdapted_vectorMeasureState (n:=n) μ β t ht r).measurable).mono
      ((vectorBrownianFiltration n).le r) le_rfl
  have hR:=(vectorFiniteHessianResponseData (n:=n) s β t i l).continuous_response_first_parameter
    (s.m i) (((1-t)*β^2)*(s.q (i+1)-r))
  simp_rw [fderiv_vectorFiniteCellHessianDiagonal_eq_response]
  have hsub:=(hR.measurable.comp (measurable_fst.prodMk hX)).sub
    ((measurable_const (a:=s.m i)).smul (((measurable_vectorFixedStateCellGradient s μ β t ht i l r).const_mul 2).smul
      (measurable_vectorFixedStateCellGradientDerivative s μ β t ht i l r)))
  convert hsub using 1
  funext sample
  rfl

theorem measurable_uncurry_vectorFixedStateCellHessianSource (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      vectorFixedStateCellHessianSource s μ β t ht i z.1 z.2 l) := by
  have hD : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>fderiv ℝ
      (fun y=>vectorFiniteCellHessianDiagonal s β t z.2.1 i z.1 y l)
      (vectorMeasureState μ β t ht z.1 z.2)):=
    measurable_uncurry_of_continuous_of_measurable
      (continuous_vectorFixedStateCellHessianDerivative_path s μ β t ht i l)
      (measurable_vectorFixedStateCellHessianDerivative s μ β t ht i l)
  have hU:=measurable_uncurry_vectorFixedStateCellFullGradient (n:=n) s μ β t ht i
  have hd:=measurable_uncurry_vectorAdditiveDrift (vectorMeasureDriftData (n:=n) μ β t ht)
    (Real.sqrt ((1-t)*β^2)) 0 1
  have hδ:=hd.sub ((hU.const_smul (s.m i)).const_smul ((1-t)*β^2))
  have hE:=measurable_uncurry_vectorFixedStateCellGradientEnergy s μ β t ht i l
  exact ((show Measurable (fun z : (Field n→L[ℝ]ℝ)×Field n=>z.1 z.2) from by fun_prop).comp
    (hD.prodMk hδ)).sub (measurable_const.mul hE)

end QuantitativePaper
