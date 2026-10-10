module
public import QuantitativePaper.VectorJointResponseSquareInterval
public import QuantitativePaper.VectorFiniteCellGradientBounds
public import QuantitativePaper.VectorMeasureIto

@[expose] public section

/-! Genuine cropped finite-gradient square evolution on the FIXED actual
arbitrary-profile diffusion. Its literal drift defect has a depth-independent
CDF and uniform-gradient error envelope. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def vectorFixedStateCellGradientEnergy (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n)
    (l : Fin n) : ℝ :=
  ∑j : Fin n,(fderiv ℝ (fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i r) y l)
    (vectorMeasureState μ β t ht r sample) (EuclideanSpace.single j 1))^2

def vectorFixedStateCellGradientSquareSource (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n)
    (l : Fin n) : ℝ :=
  let X:=vectorMeasureState μ β t ht r sample
  let U:=vectorFiniteCellPotential s β t sample.1 i r
  let g:=fun y=>gradient U y l
  let d:=vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1 r sample
  2*g X*fderiv ℝ g X (d-((1-t)*β^2) • ((s.m i) • gradient U X))+
    ((1-t)*β^2)*vectorFixedStateCellGradientEnergy s μ β t ht i r sample l

theorem vectorResponseSquareSource_finiteCell (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (l : Fin n) (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    vectorResponseSquareSource
      (fun z : VectorParameter n=>vectorRecursion s β t z.1 (k+1-i) z.2)
      (fun z : VectorParameter n=>vectorMagnetization s β t z.1 (k+1-i) z.2 l)
      (s.m i) ((1-t)*β^2) (s.q (i+1))
      (vectorMeasureState μ β t ht)
      (vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1)
      r sample=vectorFixedStateCellGradientSquareSource s μ β t ht i r sample l := by
  have hg : (fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i r) y l)=
      vectorStepResponse (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t sample.1 (k+1-i))
        (fun y=>vectorMagnetization s β t sample.1 (k+1-i) y l) :=
    funext fun y=>vectorFiniteCellGradient_eq_response s β t sample.1 i r y l
  have hu : vectorFiniteCellPotential s β t sample.1 i r=
      vectorColeHopfStep (((1-t)*β^2)*(s.q (i+1)-r)) (s.m i)
        (vectorRecursion s β t sample.1 (k+1-i)) := rfl
  unfold vectorResponseSquareSource vectorFixedStateCellGradientSquareSource vectorFixedStateCellGradientEnergy
  dsimp only
  rw [←hg,←hu]

theorem vectorFixedState_gradient_square_cropped (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (l : Fin n)
    (a b : ℝ≥0) (hab : a≤b) (hb : (b : ℝ)<s.q (i+1))
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Integrable (fun sample=>Z sample*
      ((gradient (vectorFiniteCellPotential s β t sample.1 i b)
          (vectorMeasureState μ β t ht.le b sample) l)^2-
        (gradient (vectorFiniteCellPotential s β t sample.1 i a)
          (vectorMeasureState μ β t ht.le a sample) l)^2)) (vectorDisorderBrownianMeasure n) ∧
    (∫sample,Z sample*((gradient (vectorFiniteCellPotential s β t sample.1 i b)
          (vectorMeasureState μ β t ht.le b sample) l)^2-
        (gradient (vectorFiniteCellPotential s β t sample.1 i a)
          (vectorMeasureState μ β t ht.le a sample) l)^2) ∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc a b,Z sample*vectorFixedStateCellGradientSquareSource s μ β t ht.le i r sample l
        ∂nonnegativeLebesgueMeasure) ∂vectorDisorderBrownianMeasure n := by
  have hcpos : 0<(1-t)*β^2:=mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ)
  have hh:=vector_jointResponse_square_interval (m:=s.m i) (vectorFiniteGradientResponseData (n:=n) s β t i l)
    (vectorItoCharacteristics_vectorMeasureState μ β t ht.le) (Real.sq_sqrt hcpos.le) hcpos
    a b hab hb Z hZ C hC
  simpa only [vectorJointResponse,←vectorFiniteCellGradient_eq_response,
    vectorResponseSquareSource_finiteCell] using hh

theorem vectorMeasure_drift_physical (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1
      (q : ℝ).toNNReal sample=
    ((1-t)*β^2) • (Paper.parisiCDF μ q • vectorMeasureGradient μ β t q sample.1
      (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample)) := by
  have hq : ((q : ℝ).toNNReal : ℝ≥0)≤1:=by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ q.property.1,NNReal.coe_one]
    exact q.property.2
  rw [vectorAdditiveDrift,if_pos hq]
  change vectorMeasureDrift μ β t ht (q : ℝ).toNNReal sample.1 _=_
  unfold vectorMeasureDrift
  rw [Real.coe_toNNReal _ q.property.1,projIcc_of_mem _ q.property,smul_smul]
  rfl

theorem norm_vectorMeasure_cell_drift_defect_le (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (D : ℝ) (hD : 0≤D)
    (hgrad : ∀q p x,‖vectorMeasureGradient (n:=n) μ β t q p x-vectorFiniteTailGradient s β t q p x‖≤D)
    (q : Paper.Overlap) (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1))) (sample : VectorDisorderBrownianSample n) :
    ‖vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1
        (q : ℝ).toNNReal sample-((1-t)*β^2) • ((s.m i) • gradient
          (vectorFiniteCellPotential s β t sample.1 i q)
          (vectorMeasureState μ β t ht (q : ℝ).toNNReal sample))‖≤
      ((1-t)*β^2)*(Real.sqrt n*|Paper.parisiCDF μ q-s.m i|+D) := by
  let c:ℝ:=(1-t)*β^2
  let a:ℝ:=Paper.parisiCDF μ q
  let b:ℝ:=s.m i
  let X:=vectorMeasureState μ β t ht (q : ℝ).toNNReal sample
  let v:Field n:=vectorMeasureGradient μ β t q sample.1 X
  let w:Field n:=gradient (vectorFiniteCellPotential s β t sample.1 i q) X
  have hc : 0≤c:=mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have hb : 0≤b:=s.m_nonneg hi
  have hb1 : b≤1:=s.m_le_one hi
  have hv : ‖v‖≤Real.sqrt n:=norm_vectorMeasureGradient_le μ β t ht q sample.1 X
  have hvw : ‖v-w‖≤D:=by
    dsimp [v,w]
    rw [←vectorFiniteTailGradient_eq_cell s β t q sample.1 i hi hq]
    exact hgrad q sample.1 X
  rw [vectorMeasure_drift_physical]
  change ‖c • (a • v)-c • (b • w)‖≤c*(Real.sqrt n*|a-b|+D)
  have he : c • (a • v)-c • (b • w)=(c*(a-b)) • v+(c*b) • (v-w) := by
    simp only [smul_smul,mul_sub,sub_smul,smul_sub]
    abel
  rw [he]
  calc
    _≤‖(c*(a-b)) • v‖+‖(c*b) • (v-w)‖:=norm_add_le _ _
    _=c*|a-b| *‖v‖+(c*b)*‖v-w‖:=by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hc,
        Real.norm_of_nonneg (mul_nonneg hc hb)]
    _≤c*|a-b| *Real.sqrt n+(c*b)*D:=add_le_add
      (mul_le_mul_of_nonneg_left hv (mul_nonneg hc (abs_nonneg _)))
      (mul_le_mul_of_nonneg_left hvw (mul_nonneg hc hb))
    _≤c*(Real.sqrt n*|a-b|+D):=by
      have hcb : c*b≤c:=by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcb hD]

theorem vectorFixedStateCellGradientSquareSource_error (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (D : ℝ) (hD : 0≤D)
    (hgrad : ∀q p x,‖vectorMeasureGradient (n:=n) μ β t q p x-vectorFiniteTailGradient s β t q p x‖≤D)
    (q : Paper.Overlap) (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1)))
    (sample : VectorDisorderBrownianSample n) (l : Fin n) :
    |vectorFixedStateCellGradientSquareSource s μ β t ht i (q : ℝ).toNNReal sample l-
      ((1-t)*β^2)*vectorFixedStateCellGradientEnergy s μ β t ht i (q : ℝ).toNNReal sample l|≤
      2*((1-t)*β^2)*(n : ℝ)*(Real.sqrt n*|Paper.parisiCDF μ q-s.m i|+D) := by
  let X:=vectorMeasureState μ β t ht (q : ℝ).toNNReal sample
  let g:=fun y=>gradient (vectorFiniteCellPotential s β t sample.1 i q) y l
  let δ:=vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1
    (q : ℝ).toNNReal sample-((1-t)*β^2) • ((s.m i) • gradient
      (vectorFiniteCellPotential s β t sample.1 i q) X)
  have hg : |g X|≤1:=abs_vectorFiniteCellGradient_component_le s β t q sample.1 i hi hq X l
  have hdf : ‖fderiv ℝ g X‖≤(n : ℝ):=
    norm_fderiv_vectorFiniteCellGradient_component_le s β t q sample.1 i hi hq X l
  have hδ : ‖δ‖≤((1-t)*β^2)*(Real.sqrt n*|Paper.parisiCDF μ q-s.m i|+D):=
    norm_vectorMeasure_cell_drift_defect_le s μ β t ht i hi D hD hgrad q hq sample
  have hd : |fderiv ℝ g X δ|≤(n : ℝ)*‖δ‖:=by
    simpa only [Real.norm_eq_abs] using
      ((fderiv ℝ g X).le_opNorm δ).trans (mul_le_mul_of_nonneg_right hdf (norm_nonneg _))
  unfold vectorFixedStateCellGradientSquareSource
  rw [Real.coe_toNNReal _ q.property.1]
  change |2*g X*fderiv ℝ g X δ+_ -_|≤_
  rw [add_sub_cancel_right,abs_mul,abs_mul,show |(2 : ℝ)|=2 by norm_num]
  calc
    _≤2*1*((n : ℝ)*‖δ‖):=mul_le_mul (mul_le_mul_of_nonneg_left hg (by norm_num)) hd
      (abs_nonneg _) (by positivity)
    _≤2*1*((n : ℝ)*(((1-t)*β^2)*(Real.sqrt n*|Paper.parisiCDF μ q-s.m i|+D))):=by gcongr
    _=2*((1-t)*β^2)*(n : ℝ)*(Real.sqrt n*|Paper.parisiCDF μ q-s.m i|+D):=by ring

end QuantitativePaper
