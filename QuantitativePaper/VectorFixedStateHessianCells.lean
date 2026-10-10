module
public import QuantitativePaper.VectorFiniteHessianReaction
public import QuantitativePaper.VectorJointResponseLinearInterval
public import QuantitativePaper.VectorItoLinearCombination
public import QuantitativePaper.VectorFixedStateGradientCells

@[expose] public section

/-! Genuine cropped Hessian reaction on the fixed arbitrary-profile
diffusion. The third-jet drift discrepancy is retained until approximation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def vectorFixedStateCellHessianSource (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n)
    (l : Fin n) : ℝ :=
  let X:=vectorMeasureState μ β t ht r sample
  let U:=vectorFiniteCellPotential s β t sample.1 i r
  let H:=fun y=>vectorFiniteCellHessianDiagonal s β t sample.1 i r y l
  let d:=vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1 r sample
  fderiv ℝ H X (d-((1-t)*β^2) • ((s.m i) • gradient U X))-
    ((1-t)*β^2)*(s.m i)*vectorFixedStateCellGradientEnergy s μ β t ht i r sample l

theorem vectorResponseSources_hessian_finiteCell (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    vectorResponseLinearSource
      (fun z : VectorParameter n=>vectorRecursion s β t z.1 (k+1-i) z.2)
      (vectorFiniteHessianResponseObservable s β t i l)
      (s.m i) ((1-t)*β^2) (s.q (i+1)) (vectorMeasureState μ β t ht)
      (vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1)
      r sample-(s.m i)*vectorResponseSquareSource
      (fun z : VectorParameter n=>vectorRecursion s β t z.1 (k+1-i) z.2)
      (fun z : VectorParameter n=>vectorMagnetization s β t z.1 (k+1-i) z.2 l)
      (s.m i) ((1-t)*β^2) (s.q (i+1)) (vectorMeasureState μ β t ht)
      (vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1)
      r sample=vectorFixedStateCellHessianSource s μ β t ht i r sample l := by
  let U:=vectorFiniteCellPotential s β t sample.1 i r
  let R:=vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
    (vectorRecursion s β t sample.1 (k+1-i))
    (fun y=>vectorFiniteHessianResponseObservable s β t i l (sample.1,y))
  let g : Field n→ℝ:=fun y=>gradient U y l
  have hR : Differentiable ℝ R:=
    ((((vectorFiniteHessianResponseData s β t i l).fieldData sample.1).bounds (s.m i)).responseRegularity _).differentiable
      (by norm_num)
  have hg : Differentiable ℝ g:=
    (contDiff_vectorFiniteCellGradient_component s β t sample.1 i r l).differentiable (by simp)
  have hH : (fun y=>vectorFiniteCellHessianDiagonal s β t sample.1 i r y l)=
      (fun y=>R y-(s.m i)*g y^2):=by
    funext y
    exact vectorFiniteCellHessian_diagonal_eq_response s β t sample.1 i r y l
  have hD (x : Field n) :
      fderiv ℝ (fun y=>vectorFiniteCellHessianDiagonal s β t sample.1 i r y l) x=
        fderiv ℝ R x-(s.m i) • ((2*g x) • fderiv ℝ g x):=by
    have hh:=((hR x).hasFDerivAt.sub (((hg.pow 2) x).hasFDerivAt.const_smul (s.m i))).fderiv
    change fderiv ℝ (fun y=>R y-(s.m i)*g y^2) x=
      fderiv ℝ R x-(s.m i) • fderiv ℝ (fun y=>g y^2) x at hh
    rw [hH,hh,fderiv_square g hg]
  rw [vectorResponseSquareSource_finiteCell]
  unfold vectorResponseLinearSource vectorFixedStateCellGradientSquareSource
    vectorFixedStateCellHessianSource
  dsimp only
  rw [show vectorColeHopfStep (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
      (fun x=>vectorRecursion s β t sample.1 (k+1-i) x)=U from rfl]
  rw [hD]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  change fderiv ℝ R _ _-(s.m i)*(2*g _*fderiv ℝ g _ _+_)=
    fderiv ℝ R _ _-(s.m i)*(2*g _*fderiv ℝ g _ _)-_
  ring

theorem vectorFixedState_hessian_cropped (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (l : Fin n)
    (a b : ℝ≥0) (hab : a≤b) (hb : (b : ℝ)<s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*(
      vectorFiniteCellHessianDiagonal s β t sample.1 i b
          (vectorMeasureState μ β t ht.le b sample) l-
      vectorFiniteCellHessianDiagonal s β t sample.1 i a
          (vectorMeasureState μ β t ht.le a sample) l)) (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*(vectorFiniteCellHessianDiagonal s β t sample.1 i b
          (vectorMeasureState μ β t ht.le b sample) l-
      vectorFiniteCellHessianDiagonal s β t sample.1 i a
          (vectorMeasureState μ β t ht.le a sample) l)∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc a b,Z sample*vectorFixedStateCellHessianSource s μ β t ht.le i r sample l
        ∂nonnegativeLebesgueMeasure)∂vectorDisorderBrownianMeasure n := by
  let c:=(1-t)*β^2
  have hcpos : 0<c:=mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  let X : ℝ≥0→VectorDisorderBrownianSample n→Field n:=vectorMeasureState μ β t ht.le
  let d : ℝ≥0→VectorDisorderBrownianSample n→Field n:=
    vectorAdditiveDrift (vectorMeasureDriftData μ β t ht.le) (Real.sqrt c) 0 1
  let dataA:=vectorFiniteHessianResponseData (n:=n) s β t i l
  let dataG:=vectorFiniteGradientResponseData (n:=n) s β t i l
  let hA:=dataA.jointBounds (s.m i)
  let hG:=dataG.jointBounds (s.m i)
  let A:=vectorJointResponseSampleTimeData dataA (s.m i) hA c (s.q (i+1)) hcpos b hb
  let B:=vectorJointResponseSampleSquareTimeData dataG (s.m i) hG c (s.q (i+1)) hcpos b hb
  let hc:=vectorItoCharacteristics_vectorMeasureState (n:=n) μ β t ht.le
  let hfA:=vectorJointResponseSampleSpatialTest dataA (s.m i) hA c (s.q (i+1)) b X
    hc.continuous_state hc.adapted_state
  let hfB:=vectorJointResponseSampleSquareSpatialTest dataG (s.m i) hG c (s.q (i+1)) b X
    hc.continuous_state hc.adapted_state
  have hito:=vector_ito_interval_linear_combination hc A B hfA hfB (s.m i) Z hZ C hC a b hab le_rfl
  have he (r : ℝ≥0) (hr : r≤b) (sample : VectorDisorderBrownianSample n) :
      A.f r sample (X r sample)-(s.m i)*B.f r sample (X r sample)=
        vectorFiniteCellHessianDiagonal s β t sample.1 i r (X r sample) l:=by
    dsimp only [A,B,vectorJointResponseSampleTimeData,vectorJointResponseSampleSquareTimeData,
      TimeFTCData.square]
    simp only [vectorCappedResponse,vectorResponseCapVariance_of_le c (s.q (i+1)) b r
      (show (r : ℝ)≤b from hr)]
    rw [←vectorFiniteCellGradient_eq_response]
    exact (vectorFiniteCellHessian_diagonal_eq_response s β t sample.1 i r (X r sample) l).symm
  have hefun : (fun sample=>Z sample*((A.f b sample (X b sample)-(s.m i)*B.f b sample (X b sample))-
      (A.f a sample (X a sample)-(s.m i)*B.f a sample (X a sample))))=
      (fun sample=>Z sample*(vectorFiniteCellHessianDiagonal s β t sample.1 i b (X b sample) l-
        vectorFiniteCellHessianDiagonal s β t sample.1 i a (X a sample) l)):=by
    funext sample
    rw [he b le_rfl,he a hab]
  refine ⟨hito.1.congr (.of_forall fun sample=>congrFun hefun sample),?_⟩
  rw [hefun] at hito
  rw [hito.2]
  apply integral_congr_ae
  filter_upwards with sample
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [vectorJointResponseLinear_generator dataA (s.m i) hA c (s.q (i+1)) hcpos b hb X d
      (Real.sqrt c) (Real.sq_sqrt hcpos.le) r hr.2 sample,
    vectorJointResponseSquare_generator dataG (s.m i) hG c (s.q (i+1)) hcpos b hb X d
      (Real.sqrt c) (Real.sq_sqrt hcpos.le) r hr.2 sample,
    vectorResponseSources_hessian_finiteCell]

end QuantitativePaper
