module
public import QuantitativeFollowup.AnisotropicTailDerivative
public import FourPapersCommon.FiniteStateCascadePosteriorJets

@[expose] public section

/-! Genuine depth-uniform third jets and the actual continuous Hessian of
every arbitrary-profile anisotropic tail potential. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped BigOperators NNReal Topology ContDiff
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 800000

theorem norm_anisotropicFinitePotential_thirdJet_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) (P : AnisotropicParameter n) :
    ‖iteratedFDeriv ℝ 3 (anisotropicFinitePotential D s j) P‖≤8*‖anisotropicEnergyMap D‖^3 := by
  let L := fun l=>(anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)
  let F := finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s) L j
  have hdec : Antitone (anisotropicSchemeMass s) := by
    exact antitone_nat_of_succ_le (anisotropicSchemeMass_antitone_step s)
  change ‖iteratedFDeriv ℝ 3 (F ∘ anisotropicEnergyMap D) P‖≤_
  rw [(anisotropicEnergyMap D).iteratedFDeriv_comp_right
    (contDiff_finiteStateGaussianTerminalCascade _ _ (anisotropicSchemeMass_nonneg s) L j) P (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul_of_nonneg_right
    (norm_finiteStateCascade_thirdJet_le_eight _ _ (anisotropicSchemeMass_nonneg s)
      (anisotropicSchemeMass_le_one s 0) hdec L j _) (by positivity)

theorem anisotropicFinitePotential_secondDifferential_lipschitz (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (j : ℕ) :
    LipschitzWith (8*‖anisotropicEnergyMap D‖₊^3)
      (fderiv ℝ (fderiv ℝ (anisotropicFinitePotential D s j))) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    (((contDiff_anisotropicFinitePotential D s j).fderiv_right (m:=∞) (by simp)).fderiv_right
      (m:=1) (by simp)).differentiable_one
  intro P
  rw [←NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm,
    ←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]
  exact norm_anisotropicFinitePotential_thirdJet_le D s j P

theorem anisotropicMeasureTailPotential_hessian_limit (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    TendstoUniformly (fun j=>fderiv ℝ (fderiv ℝ (anisotropicDyadicTailPotential D μ q j)))
      (fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))) atTop ∧
    ContDiff ℝ 2 (anisotropicMeasureTailPotential D μ q) := by
  have hLip (j : ℕ) : LipschitzWith (8*‖anisotropicEnergyMap D‖₊^3)
      (fderiv ℝ (fderiv ℝ (anisotropicDyadicTailPotential D μ q j))) := by
    unfold anisotropicDyadicTailPotential
    rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
    exact anisotropicFinitePotential_secondDifferential_lipschitz D _ _
  obtain ⟨g',hu,hd,hc⟩ := exists_uniform_derivative_limit
    (fun j=>fderiv ℝ (anisotropicDyadicTailPotential D μ q j))
    (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
    (fun j=>(contDiff_anisotropicDyadicTailPotential D μ q j).fderiv_right (m:=2) (by simp))
    (8*‖anisotropicEnergyMap D‖₊^3) hLip
    (anisotropicMeasureTailPotential_derivative_limit D μ q).1
  have he : g'=fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) :=
    funext fun P=>(hd P).fderiv.symm
  rw [he] at hu hc
  refine ⟨hu,?_⟩
  rw [show (2 : ℕ∞ω)=1+1 by norm_num,contDiff_succ_iff_fderiv]
  refine ⟨(anisotropicMeasureTailPotential_derivative_limit D μ q).2.differentiable_one,by simp,?_⟩
  exact contDiff_one_iff_fderiv.mpr ⟨fun P=>(hd P).differentiableAt,hc⟩

theorem tendstoUniformly_anisotropicDyadicTailSecondDifferential (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    TendstoUniformly (fun j=>fun z : Paper.Overlap×AnisotropicParameter n=>
      fderiv ℝ (fderiv ℝ (anisotropicDyadicTailPotential D μ z.1 j)) z.2)
      (fun z=>fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ z.1)) z.2) atTop := by
  apply tendstoUniformly_fderiv_family (fun j q=>fderiv ℝ (anisotropicDyadicTailPotential D μ q j))
    (fun z=>fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ z.1)) z.2)
    (fun j q=>((contDiff_anisotropicDyadicTailPotential D μ q j).fderiv_right (m:=1) (by simp)).differentiable_one)
    (8*‖anisotropicEnergyMap D‖₊^3)
    (fun j q=>by
      unfold anisotropicDyadicTailPotential
      rw [anisotropicTailRecursion_eq_clamped D _ q q.property le_rfl]
      exact anisotropicFinitePotential_secondDifferential_lipschitz D _ _)
    ((tendstoUniformlyOn_univ.mpr (tendstoUniformly_anisotropicDyadicTailDifferential D μ)).uniformCauchySeqOn)
  intro z
  exact (anisotropicMeasureTailPotential_hessian_limit D μ z.1).1.tendsto_at z.2

end QuantitativeFollowup
