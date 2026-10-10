module
public import QuantitativeFollowup.AnisotropicBinaryFeatureConditional
public import QuantitativeFollowup.AnisotropicSpinPathConditionals
public import QuantitativeFollowup.AnisotropicCovarianceMoments
public import FourPapersCommon.ConditionalPullback

@[expose] public section

/-! Literal terminal row-parameter differentiation under the actual single-leaf
law. The coordinate perturbation adds exactly theta times the binary terminal
feature, even when an original Gaussian coupling coefficient is zero. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology ContDiff
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def anisotropicPairParameterPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) (θ : ℝ) : ℝ :=
  anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
    (anisotropicCouplingRescaling D P+θ • anisotropicCouplingDirection e)

theorem anisotropicPairParameter_terminal_feature (D : AnisotropicSpinModel n)
    (P : AnisotropicParameter n) (e : AnisotropicCouplingIndex n) (θ : ℝ)
    (σ : Configuration n) :
    anisotropicEnergyMap (anisotropicUnitCouplings D)
      (anisotropicCouplingRescaling D P+θ • anisotropicCouplingDirection e) σ=
        anisotropicEnergyMap D P σ+θ*(Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)) := by
  rw [map_add,map_smul,anisotropicEnergyMap_unitCouplings]
  change anisotropicEnergyMap D P σ+θ*anisotropicTerminalLinear
    (anisotropicUnitCouplings D) σ (anisotropicCouplingDirection e)=_
  rw [anisotropicTerminalLinear_unitCoupling]

theorem hasDerivAt_anisotropicPairParameterPotential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) (θ : ℝ) :
    HasDerivAt (anisotropicPairParameterPotential D μ q P e)
      (fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q)
        (anisotropicCouplingRescaling D P+θ • anisotropicCouplingDirection e)
          (anisotropicCouplingDirection e)) θ :=
  hasDerivAt_affine_line_of_differentiable _
    (anisotropicMeasureTailPotential_derivative_limit (anisotropicUnitCouplings D) μ q).2.differentiable_one
    _ _ θ

theorem hasDerivAt_anisotropicPairParameterPotential_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) :
    HasDerivAt (anisotropicPairParameterPotential D μ q P e)
      (anisotropicTailPairResponse D μ q P e) 0 := by
  simpa only [zero_smul,add_zero,anisotropicTailPairResponse] using
    hasDerivAt_anisotropicPairParameterPotential D μ q P e 0

theorem hasDerivAt_anisotropicPairParameterPotential_first_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) :
    HasDerivAt (fun θ=>deriv (anisotropicPairParameterPotential D μ q P e) θ)
      (anisotropicTailPairSecond D μ q P e) 0 := by
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  let K:=anisotropicCouplingDirection e
  let H:=anisotropicCouplingRescaling D P
  have hD : ContDiff ℝ 1 (fderiv ℝ U):=
    (anisotropicMeasureTailPotential_hessian_limit (anisotropicUnitCouplings D) μ q).2.fderiv_right (by norm_num)
  have hh:=(hD.differentiable_one (H+(0:ℝ) • K)).hasFDerivAt
  have hc:=hh.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).smul_const K |>.const_add H)
  have he:=hc.clm_apply (hasDerivAt_const (0:ℝ) K)
  have hd (θ : ℝ) := (hasDerivAt_anisotropicPairParameterPotential D μ q P e θ).deriv
  simp_rw [hd]
  simpa only [Function.comp_def,id_eq,one_smul,zero_smul,add_zero,map_zero,
    anisotropicTailPairSecond,U,H,K] using he

theorem anisotropic_marked_pair_second_nodeTheta (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
      anisotropicProcessPairSecond D μ q e p.1)=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>1-Paper.parisiCDF μ q*(anisotropicProcessPairResponse D μ q e p.1)^2-
        ∫r : Paper.Overlap,if q < r then anisotropicPastPairSquareKernel D μ a q r e p.1 else 0
          ∂parisiFreeMeasure μ a :=
  (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).quasiMeasurePreserving.ae
    (anisotropic_pair_second_nodeTheta D μ a ha hμ q e)

theorem anisotropic_marked_pair_square_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q r : Paper.Overlap)
    (e : AnisotropicCouplingIndex n) :
    (anisotropicMeasureSpinPathLaw D μ a)[
      (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
        (anisotropicProcessPairResponse D μ r e p.1)^2)|anisotropicSpinPast n (q:ℝ).toNNReal]
      =ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicPastPairSquareKernel D μ a q r e p.1 := by
  let F:=fun p : AnisotropicDisorderBrownianSample n=>(anisotropicProcessPairResponse D μ r e p)^2
  have hF : Measurable F:=(measurable_anisotropicProcessPairResponse D μ r e).pow_const 2
  have hi : Integrable F (anisotropicMeasureSampleLaw D μ a):=
    (integrable_const (1:ℝ)).mono' hF.aestronglyMeasurable (.of_forall fun p=>by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (anisotropicProcessPairResponse_bound D μ r e p) 2).trans_eq (by norm_num))
  have h:=condExp_comp_of_measurePreserving
    (anisotropicMeasureSpinPathLaw D μ a) (anisotropicMeasureSampleLaw D μ a) Prod.fst
    (measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a)
    (anisotropicBrownianFiltration n (q:ℝ).toNNReal) ((anisotropicBrownianFiltration n).le _) F hF hi
  exact h.trans ((measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).quasiMeasurePreserving.ae
    (anisotropicPastPairSquareKernel_condExp D μ a q r e))

theorem anisotropic_marked_pair_parameter_nodeTheta (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (e : AnisotropicCouplingIndex n) :
    ∀ᵐp : AnisotropicDisorderBrownianSample n×Configuration n ∂anisotropicMeasureSpinPathLaw D μ a,
      HasDerivAt (anisotropicPairParameterPotential D μ q (anisotropicProcessParameter D μ q p.1) e)
        ((anisotropicMeasureSpinPathLaw D μ a)[
          fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
            Paper.spinSign (z.2 e.1.1)*Paper.spinSign (z.2 e.1.2)|
              anisotropicSpinPast n (q:ℝ).toNNReal] p) 0 ∧
      HasDerivAt (fun θ=>deriv
        (anisotropicPairParameterPotential D μ q (anisotropicProcessParameter D μ q p.1) e) θ)
        (1-Paper.parisiCDF μ q*(anisotropicProcessPairResponse D μ q e p.1)^2-
          ∫r : Paper.Overlap,if q < r then anisotropicPastPairSquareKernel D μ a q r e p.1 else 0
            ∂parisiFreeMeasure μ a) 0 := by
  filter_upwards [anisotropicMeasureSpinPathLaw_pair_condExp D μ a q e,
    anisotropic_marked_pair_second_nodeTheta D μ a ha hμ q e] with p hfirst hsecond
  constructor
  · rw [hfirst]
    exact hasDerivAt_anisotropicPairParameterPotential_zero D μ q _ e
  · rw [←hsecond]
    exact hasDerivAt_anisotropicPairParameterPotential_first_zero D μ q _ e

def anisotropicCavityRowIndex (n : ℕ) (i : Fin n) : AnisotropicCouplingIndex (n+1) :=
  anisotropicOrderedCoupling i.castSucc (Fin.last n)

theorem anisotropicCavityRowIndex_feature (i : Fin n) (σ : Configuration (n+1)) :
    Paper.spinSign (σ (anisotropicCavityRowIndex n i).1.1)*
      Paper.spinSign (σ (anisotropicCavityRowIndex n i).1.2)=
        Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n)) :=
  anisotropicOrderedCoupling_feature _ _ σ

theorem anisotropicCavityRowParameter_terminal_feature (D : AnisotropicSpinModel (n+1))
    (P : AnisotropicParameter (n+1)) (i : Fin n) (θ : ℝ) (σ : Configuration (n+1)) :
    anisotropicEnergyMap (anisotropicUnitCouplings D)
      (anisotropicCouplingRescaling D P+θ • anisotropicCouplingDirection (anisotropicCavityRowIndex n i)) σ=
        anisotropicEnergyMap D P σ+θ*(Paper.spinSign (σ i.castSucc)*Paper.spinSign (σ (Fin.last n))) := by
  rw [anisotropicPairParameter_terminal_feature,anisotropicCavityRowIndex_feature]

theorem anisotropic_cavity_row_parameter_nodeTheta (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : Paper.Overlap) (i : Fin n) :
    ∀ᵐp : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)
        ∂anisotropicMeasureSpinPathLaw D μ a,
      HasDerivAt (anisotropicPairParameterPotential D μ q (anisotropicProcessParameter D μ q p.1)
        (anisotropicCavityRowIndex n i))
        ((anisotropicMeasureSpinPathLaw D μ a)[
          fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
            Paper.spinSign (z.2 i.castSucc)*Paper.spinSign (z.2 (Fin.last n))|
              anisotropicSpinPast (n+1) (q:ℝ).toNNReal] p) 0 ∧
      HasDerivAt (fun θ=>deriv
        (anisotropicPairParameterPotential D μ q (anisotropicProcessParameter D μ q p.1)
          (anisotropicCavityRowIndex n i)) θ)
        (1-Paper.parisiCDF μ q*(anisotropicProcessPairResponse D μ q (anisotropicCavityRowIndex n i) p.1)^2-
          ∫r : Paper.Overlap,if q < r then
            anisotropicPastPairSquareKernel D μ a q r (anisotropicCavityRowIndex n i) p.1 else 0
            ∂parisiFreeMeasure μ a) 0 := by
  simpa only [anisotropicCavityRowIndex_feature] using
    anisotropic_marked_pair_parameter_nodeTheta D μ a ha hμ q (anisotropicCavityRowIndex n i)

end QuantitativeFollowup
