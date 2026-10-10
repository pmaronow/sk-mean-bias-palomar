module
public import QuantitativePaper.VectorFixedStateHessianRegularity

@[expose] public section

/-! Genuine third-jet control of the Hessian drift error. The constants are
uniform in the number of Parisi cells, so the error vanishes in the grid limit. -/
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

theorem norm_fderiv_hessian_diagonal_le_thirdJet (f : Field n→ℝ) (hf : ContDiff ℝ 3 f)
    (x : Field n) (l : Fin n) :
    ‖fderiv ℝ (fun y=>(hessianOperator f y (EuclideanSpace.single l (1 : ℝ))) l) x‖≤
      ‖iteratedFDeriv ℝ 3 f x‖ := by
  let g : Field n→ℝ:=fun y=>gradient f y l
  have hg : ContDiff ℝ 2 g:=by
    have hG : ContDiff ℝ 2 (gradient f):=
      (InnerProductSpace.toDual ℝ (Field n)).symm.contDiff.comp (hf.fderiv_right (by norm_num))
    exact (EuclideanSpace.proj l).contDiff.comp hG
  have hD : Differentiable ℝ (fderiv ℝ g):=(hg.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have he : (fun y=>(hessianOperator f y (EuclideanSpace.single l (1 : ℝ))) l)=
      (fun y=>fderiv ℝ g y (EuclideanSpace.single l (1 : ℝ))):=by
    funext y
    exact (fderiv_gradient_component_eq_hessian f (hf.of_le (by norm_num)) y _ l).symm
  rw [he,fderiv_clm_apply (hD x) (differentiableAt_const (EuclideanSpace.single l (1 : ℝ)))]
  rw [show fderiv ℝ (fun _ : Field n=>EuclideanSpace.single l (1 : ℝ)) x=0 from
    (hasFDerivAt_const (EuclideanSpace.single l (1 : ℝ)) x).fderiv]
  simp only [ContinuousLinearMap.comp_zero,zero_add]
  have hb : ‖(fderiv ℝ (fderiv ℝ g) x).flip (EuclideanSpace.single l (1 : ℝ))‖≤
      ‖fderiv ℝ (fderiv ℝ g) x‖:=by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    calc
      _≤‖fderiv ℝ (fderiv ℝ g) x w‖*‖EuclideanSpace.single l (1 : ℝ)‖:=
        (fderiv ℝ (fderiv ℝ g) x w).le_opNorm _
      _≤(‖fderiv ℝ (fderiv ℝ g) x‖*‖w‖)*‖EuclideanSpace.single l (1 : ℝ)‖:=by gcongr;exact (fderiv ℝ (fderiv ℝ g) x).le_opNorm w
      _=_:=by simp only [PiLp.norm_single,norm_one,mul_one]
  have h2 : ‖fderiv ℝ (fderiv ℝ g) x‖=‖iteratedFDeriv ℝ 2 g x‖:=by
    rw [←norm_iteratedFDeriv_one (fderiv ℝ g),norm_iteratedFDeriv_fderiv]
  exact (hb.trans_eq h2).trans (norm_secondJet_gradient_component_le f hf x l)

theorem norm_fderiv_vectorFiniteCellHessianDiagonal_le (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (i : ℕ) (hi : i≤k+1) (q : Paper.Overlap)
    (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1))) (x : Field n) (l : Fin n) :
    ‖fderiv ℝ (fun y=>vectorFiniteCellHessianDiagonal s β t p i q y l) x‖≤
      vectorSpatialJetBound n 3 := by
  let f:=vectorFiniteCellPotential s β t p i q
  have hf : ContDiff ℝ 3 f:=
    (contDiff_vectorColeHopfStep_recursion_field s β t _ _ p (k+1-i)).of_le (by simp)
  have hb : ‖iteratedFDeriv ℝ 3 f x‖≤vectorSpatialJetBound n 3:=by
    dsimp only [f]
    rw [←vectorTailRecursion_eq_finiteCell s β t q p i hi hq]
    exact norm_vectorTailRecursion_jet_le_uniform s β t q q.property p _ le_rfl 3 (by norm_num) x
  exact (norm_fderiv_hessian_diagonal_le_thirdJet f hf x l).trans hb

theorem vectorFixedStateCellHessianSource_error (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (D : ℝ) (hD : 0≤D)
    (hgrad : ∀q p x,‖vectorMeasureGradient (n:=n) μ β t q p x-vectorFiniteTailGradient s β t q p x‖≤D)
    (q : Paper.Overlap) (hq : (q : ℝ)∈Icc (s.q i) (s.q (i+1)))
    (sample : VectorDisorderBrownianSample n) (l : Fin n) :
    |vectorFixedStateCellHessianSource s μ β t ht i (q : ℝ).toNNReal sample l+
      ((1-t)*β^2)*(s.m i)*vectorFixedStateCellGradientEnergy s μ β t ht i (q : ℝ).toNNReal sample l|≤
      ((1-t)*β^2)*vectorSpatialJetBound n 3*(Real.sqrt n*|Paper.parisiCDF μ q-s.m i|+D) := by
  let X:=vectorMeasureState μ β t ht (q : ℝ).toNNReal sample
  let H : Field n→ℝ:=fun y=>vectorFiniteCellHessianDiagonal s β t sample.1 i q y l
  let δ:=vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt ((1-t)*β^2)) 0 1
    (q : ℝ).toNNReal sample-((1-t)*β^2) • ((s.m i) • gradient
      (vectorFiniteCellPotential s β t sample.1 i q) X)
  have hH : ‖fderiv ℝ H X‖≤vectorSpatialJetBound n 3:=
    norm_fderiv_vectorFiniteCellHessianDiagonal_le s β t sample.1 i hi q hq X l
  have hδ : ‖δ‖≤((1-t)*β^2)*(Real.sqrt n*|Paper.parisiCDF μ q-s.m i|+D):=
    norm_vectorMeasure_cell_drift_defect_le s μ β t ht i hi D hD hgrad q hq sample
  unfold vectorFixedStateCellHessianSource
  rw [Real.coe_toNNReal _ q.property.1]
  change |fderiv ℝ H X δ-_+_|≤_
  rw [sub_add_cancel]
  calc
    _≤‖fderiv ℝ H X‖*‖δ‖:=by simpa only [Real.norm_eq_abs] using (fderiv ℝ H X).le_opNorm δ
    _≤vectorSpatialJetBound n 3*(((1-t)*β^2)*(Real.sqrt n*|Paper.parisiCDF μ q-s.m i|+D)):=
      mul_le_mul hH hδ (norm_nonneg _) (vectorSpatialJetBound_nonneg n 3)
    _=_:=by ring

theorem norm_vectorFixedStateCellHessianSource_le (s : RSBScheme k) (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (i : ℕ) (hi : i≤k+1) (l : Fin n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorFixedStateCellHessianSource s μ β t ht i r sample l‖≤
      ((1-t)*β^2)*(2*vectorFiniteCellHessianDerivativeBound s β t i l*Real.sqrt n+
        (n : ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l : ℝ)^2) := by
  let c:ℝ:=(1-t)*β^2
  let A:ℝ:=vectorFiniteCellHessianDerivativeBound s β t i l
  let G:ℝ:=vectorFiniteCellGradientDerivativeBound s β t i l
  let X:=vectorMeasureState μ β t ht r sample
  let U:=vectorFiniteCellPotential s β t sample.1 i r
  let H : Field n→ℝ:=fun y=>vectorFiniteCellHessianDiagonal s β t sample.1 i r y l
  let d:=vectorAdditiveDrift (vectorMeasureDriftData μ β t ht) (Real.sqrt c) 0 1 r sample
  have hc:0≤c:=mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have hA:0≤A:=vectorFiniteCellHessianDerivativeBound_nonneg s β t i l
  have hD:‖fderiv ℝ H X‖≤A:=norm_fderiv_vectorFiniteCellHessianDiagonal_global s β t sample.1 i r X l
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
  have hEval:‖fderiv ℝ H X (d-c • ((s.m i) • gradient U X))‖≤A*(2*c*Real.sqrt n):=
    ((fderiv ℝ H X).le_opNorm _).trans (mul_le_mul hD hδ (norm_nonneg _) hA)
  have hE:=vectorFixedStateCellGradientEnergy_nonneg_le s μ β t ht i l r sample
  have hE0:=hE.1
  have hEb : vectorFixedStateCellGradientEnergy s μ β t ht i r sample l≤(n : ℝ)*G^2:=hE.2
  have hEvalAbs : |fderiv ℝ H X (d-c • ((s.m i) • gradient U X))|≤A*(2*c*Real.sqrt n):=by
    simpa only [Real.norm_eq_abs] using hEval
  change ‖fderiv ℝ H X (d-c • ((s.m i) • gradient U X))-
    c*(s.m i)*vectorFixedStateCellGradientEnergy s μ β t ht i r sample l‖≤_
  calc
    _≤‖fderiv ℝ H X (d-c • ((s.m i) • gradient U X))‖+
      ‖c*(s.m i)*vectorFixedStateCellGradientEnergy s μ β t ht i r sample l‖:=norm_sub_le _ _
    _≤A*(2*c*Real.sqrt n)+c*1*((n : ℝ)*G^2):=by
      simp only [norm_mul,Real.norm_eq_abs,abs_of_nonneg hc,abs_of_nonneg hE.1]
      gcongr
    _=_:=by ring

end QuantitativePaper
