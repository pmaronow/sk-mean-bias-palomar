module
public import QuantitativeFollowup.ScalarTransportPointwiseResponse
public import QuantitativeFollowup.GaussianScoreBounds
public import QuantitativeFollowup.ScalarScoreConditioning

@[expose] public section

/-! The literal normalized Gaussian score is an expectation under the
constructed scalar diffusion and marked terminal spin law. Boundedness and
measurability of the score are proved from actual spatial jets and parameter
partials before applying the density change of variables. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 240000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem scalarTransportExplicitScore_continuous_bounded (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (e : Bool)
    (center : ℝ) :
    Continuous (fun x=>scalarTransportExplicitScore s β φ p e x center) ∧
      ∃K : ℝ,0≤K ∧ ∀x,‖scalarTransportExplicitScore s β φ p e x center‖≤K := by
  let A:=scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2)
  let B:=scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficientDerivative s β φ 0) (k+2)
  let V:=scalarTransportEuclideanExponent s β φ e 0
  let F:=scalarTransportGradientSquare s β φ p 0
  have hs (i : Fin (k+2)) : Continuous (fun x=>gaussianScoreBilinear V F x
      (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) center) ∧
      ∃K : ℝ,0≤K ∧ ∀x,‖gaussianScoreBilinear V F x
        (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) center‖≤K :=
    gaussianScoreBilinear_continuous_bounded V F
      (boundedPositiveJets_scalarTransportEuclideanExponent s β φ e 0)
      (boundedJets_scalarTransportGradientSquare s β φ p 0) _ _ center
  choose K hK hb using fun i=>(hs i).2
  let ins : QuantitativePaper.Field (k+3)→ℝ×QuantitativePaper.Field (k+3) := fun x=>(0,x)
  have hi : Continuous ins := continuous_const.prodMk continuous_id
  have hcD : Continuous (fun x : QuantitativePaper.Field (k+3)=>scalarTransportSquarePartial s β φ p 0 x) := by
    convert! (continuous_scalarTransportSquarePartial s β hβ φ p).comp hi using 1
  have hcP : Continuous (fun x : QuantitativePaper.Field (k+3)=>scalarTransportExponentPartial s β φ 0 x) := by
    convert! (continuous_scalarTransportExponentPartial s β hβ φ).comp hi using 1
  have hcF : Continuous F := (boundedJets_scalarTransportGradientSquare s β φ p 0).1.continuous
  have hcS : Continuous (fun x : QuantitativePaper.Field (k+3)=>∑i : Fin (k+2),
      gaussianScoreBilinear V F x (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) center) :=
    continuous_finsetSum _ (fun i _=>(hs i).1)
  refine ⟨(hcD.add ((hcF.sub continuous_const).mul hcP)).add hcS,?_⟩
  let P:=3*β^2/2*‖φ‖
  let Q:=2*scalarTransportVariationSpatialBound β φ
  refine ⟨Q+(1+‖center‖)*P+∑i,K i,by
    have hp : 0≤P := by dsimp only [P];positivity
    have hq : 0≤Q := mul_nonneg (by norm_num) (scalarTransportVariationSpatialBound_nonneg β φ)
    exact add_nonneg (add_nonneg hq (mul_nonneg (by positivity) hp))
      (Finset.sum_nonneg (fun i _=>hK i)),?_⟩
  intro x
  have hf : ‖F x‖≤1 := by
    dsimp only [F]
    rw [scalarTransportSquare_zero]
    exact norm_scalarFiniteGradientSquare_le_one s β p x
  have hcenter : ‖F x-center‖≤1+‖center‖ :=
    (norm_sub_le _ _).trans (add_le_add hf le_rfl)
  have hsum : ‖∑i : Fin (k+2),gaussianScoreBilinear V F x
      (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) center‖≤∑i,K i :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>hb i x))
  unfold scalarTransportExplicitScore
  apply (norm_add_le _ _).trans
  apply add_le_add _ hsum
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_scalarTransportSquarePartial_le s β φ p 0 x)
  rw [norm_mul]
  exact mul_le_mul hcenter (norm_scalarTransportExponentPartial_le s β φ 0 x)
    (norm_nonneg _) (by positivity)

theorem measurable_bounded_scalarTransportExplicitScore (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) (center : ℝ) :
    Measurable (fun z : QuantitativePaper.Field (k+3)×Bool=>
      scalarTransportExplicitScore s β φ p z.2 z.1 center) ∧
      ∃K : ℝ,0≤K ∧ ∀z : QuantitativePaper.Field (k+3)×Bool,
        ‖scalarTransportExplicitScore s β φ p z.2 z.1 center‖≤K := by
  have hh:=fun e=>scalarTransportExplicitScore_continuous_bounded s β hβ φ p e center
  refine ⟨measurable_from_prod_countable_left (fun e=>(hh e).1.measurable),?_⟩
  choose K hK hb using fun e=>(hh e).2
  refine ⟨∑e : Bool,K e,Finset.sum_nonneg (fun e _=>hK e),fun z=>(hb z.2 z.1).trans ?_⟩
  exact Finset.single_le_sum (fun e _=>hK e) (Finset.mem_univ z.2)

theorem scalarTransportGaussianInput_zero (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) :
    scalarCoefficientHistoryLinear (scalarSchemeTransportCoefficient s β φ 0) (k+2)=
      scalarFiniteGaussianInput s β := by
  unfold scalarFiniteGaussianInput
  apply scalarCoefficientHistoryLinear_congr
  intro i
  simp only [scalarSchemeTransportCoefficient,zero_mul,add_zero,
    scalarSchemeHistoryClock_coe s (i+1) (by omega),scalarSchemeHistoryClock_coe s i (by omega)]

theorem scalarTransportGaussianResponse_eq_physical_score (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ : C(Paper.Overlap,ℝ)) (p : Fin (k+3)) :
    scalarTransportGaussianResponse s β φ p=
      ∫z,scalarTransportExplicitScore s β φ p z.2
        (WithLp.toLp 2 (scalarSelectedHistory s β hβ z.1))
        (FRSB.Gamma β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p))
        ∂scalarMarkedSpinLaw β hβ (Paper.parisiSchemeMeasure s) := by
  let center:=FRSB.Gamma β (Paper.parisiSchemeMeasure s) (scalarSchemeTransportNode s p)
  let f:=fun z : QuantitativePaper.Field (k+3)×Bool=>scalarTransportExplicitScore s β φ p z.2 z.1 center
  obtain ⟨hf,K,hK,hb⟩:=measurable_bounded_scalarTransportExplicitScore s β hβ φ p center
  have he:=integral_scalarGaussianMarkedLaw_euclidean s β hβ f hf K hb
  have hp:=integral_scalarGaussianMarkedLaw_euclidean_physical s β hβ f hf
  calc
    _ = (1/2:ℝ)*∑e : Bool,∫z,Real.exp (scalarFiniteEuclideanExponent s β e
        (scalarFiniteGaussianInput s β z))*f (scalarFiniteGaussianInput s β z,e) ∂fieldGaussian (k+2) := by
      unfold scalarTransportGaussianResponse f scalarTransportExplicitScore center
      simp only [scalarTransportGaussianInput_zero,scalarTransportExponent_zero]
    _ = ∫z,f (scalarFiniteGaussianInput s β z.1,z.2) ∂scalarGaussianMarkedLaw s β := he.symm
    _ = _ := hp

end QuantitativeFollowup
