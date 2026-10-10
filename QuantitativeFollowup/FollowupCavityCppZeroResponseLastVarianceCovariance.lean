module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceFieldExpectation
public import QuantitativeFollowup.FollowupCavityFixedRowLineOuterMarginal

@[expose] public section

/-! Genuine covariance cancellation at zero incident row for every positive
last auxiliary variance. The rest couplings and variances stay fixed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets SpinGlass.AT OverlapPaper
variable {n k : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem cavityFixedRow_field_integral_zero (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (hd : d≤k+2) (F : FiniteStateField (QuantitativePaper.Configuration (n+1))→ℝ)
    (hF : BoundedJets F) :
    (∫z,F (cavityFixedRowLineField (k+2) d z.1 z.2)∂cavityFixedRowLaw D s a 0)=
      ∫g,sourceKernelExpectation
        (fun r=>finiteStateGaussianCascadeKernel (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
          (gtStateLogPartition (fun _ : QuantitativePaper.Configuration (n+1)=>0)) (d+r)) (k+2-d) F
        (anisotropicEnergyMap D (anisotropicDisorderInjection (n+1) g))
        ∂anisotropicFiniteOuterLaw D s a :=by
  obtain ⟨C,hC,hb⟩:=hF.2 0
  have hbound(Q):|F Q|≤C:=by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb Q
  have ht:=integral_cavityFixedRowLineField_jointLaw_eq_tilted_gaussian
    (fun _ : QuantitativePaper.Configuration (n+1)=>0) (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
    (cavityFiniteEnergyInput D s) a (k+2) d hd (anisotropicRootEnergyMap D) 0
    F hF.1.continuous.measurable C hbound
  have hInput : cavityFiniteEnergyInput D s =
      (fun l => (anisotropicEnergyMap D).comp (anisotropicSchemeInput D s l)) := rfl
  simpa only [hInput,cavityFixedRowLaw,map_zero,zero_add,anisotropicRootEnergyMap,
    ContinuousLinearMap.comp_apply,anisotropicFiniteOuterLaw,anisotropicDisorderLaw,
    anisotropicFiniteFieldPotential,anisotropicFinitePotential,anisotropicDisorderInjection_apply,
    cavityFiniteEnergyInput] using ht

theorem cavityFixedRowLastSquare_lastVariance_zero_mean (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (a : ℝ)
    (d : ℕ) (hd : d≤k+2) :
    let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
    (∫z,cavityFixedRowLastSquare D s d z∂cavityFixedRowLaw D s a 0)=
      cavityLastVarianceScalarSquareMean s b d (k+2-d) 0 :=by
  dsimp only
  let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
  simp_rw [cavityFixedRowLastSquare_eq_field]
  rw [cavityFixedRow_field_integral_zero D s a d hd _ (boundedJets_cavityFixedRowLastFieldSquare D s d)]
  dsimp only [D]
  simp_rw [cavityLastVariance_energy_last_mean]
  have hz(g:AnisotropicDisorder (n+1)):
      anisotropicDisorderInjection (n+1) g (Sum.inr (Fin.last n))=0:=rfl
  simp_rw [hz]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem cavityFixedRowProduct_lastVariance_zero_mean (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (a : ℝ)
    (d : ℕ) (hd : d≤k+2) :
    let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
    (∫z,cavityFixedRowLastSquare D s d z*cavityFixedRowRestSquare D s d z∂cavityFixedRowLaw D s a 0)=
      cavityLastVarianceScalarSquareMean s b d (k+2-d) 0*
        (∫z,cavityFixedRowRestSquare D s d z∂cavityFixedRowLaw D s a 0) :=by
  dsimp only
  let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
  simp_rw [cavityFixedRowLastSquare_eq_field,cavityFixedRowRestSquare_eq_field]
  rw [cavityFixedRow_field_integral_zero D s a d hd _
    (boundedJets_cavityFixedRowProductFieldSquare D s d),
    cavityFixedRow_field_integral_zero D s a d hd _ (boundedJets_cavityFixedRowRestFieldSquare D s d)]
  dsimp only [D]
  simp_rw [cavityLastVariance_energy_product_mean,cavityLastVariance_energy_rest_mean]
  have hz(g:AnisotropicDisorder (n+1)):
      anisotropicDisorderInjection (n+1) g (Sum.inr (Fin.last n))=0:=rfl
  simp_rw [hz]
  exact integral_const_mul _ _

theorem cavityFixedRowCovariance_lastVariance_zero (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) (a : ℝ)
    (d : ℕ) (hd : d≤k+2) :
    let D:=cavityLastVarianceModel n β ρ hβ hρ b hb
    (∫z,cavityFixedRowLastSquare D s d z*cavityFixedRowRestSquare D s d z∂cavityFixedRowLaw D s a 0)-
      (∫z,cavityFixedRowLastSquare D s d z∂cavityFixedRowLaw D s a 0)*
        (∫z,cavityFixedRowRestSquare D s d z∂cavityFixedRowLaw D s a 0)=0 :=by
  dsimp only
  rw [cavityFixedRowLastSquare_lastVariance_zero_mean s n β ρ hβ hρ b hb a d hd,
    cavityFixedRowProduct_lastVariance_zero_mean s n β ρ hβ hρ b hb a d hd,sub_self]

end QuantitativeFollowup
