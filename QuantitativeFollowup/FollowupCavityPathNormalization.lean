module
public import QuantitativeFollowup.FollowupCavityPathScore
public import FourPapersCommon.FiniteCascadeReferenceTerminalProjection

@[expose] public section

/-! Actual normalization of the simultaneous path-variance response.
The denominator is the original one-leaf disorder partition function. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def cavityPathNormalizer (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    (j : ℕ) (b : ℝ) : ℝ :=
  finiteCascadeTreeGaussianNormalizer (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
    (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a j (anisotropicRootEnergyMap D) 0

theorem cavityPathNormalizer_pos (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) (j : ℕ) (b : ℝ) : 0<cavityPathNormalizer D s a i j b :=
  finiteCascadeTreeGaussianNormalizer_pos _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _

theorem cavityPathNumerator_scaled_eq_normalizer_mul_density (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) (hb : 0<b) (z : CavityPathGaussianSpace T n) :
    cavityPathNumerator D s a i T σ (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)=
      cavityPathNormalizer D s a i j b*finiteCascadeTreeGaussianFlatDensity
        (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T
        (anisotropicRootEnergyMap D) 0 (z,σ) := by
  have he:=cavityPathNumerator_scaled_eq_actual_density D s a i T σ b hb z
  have hn:=(cavityPathNormalizer_pos D s a i j b).ne'
  change _/cavityPathNormalizer D s a i j b=_ at he
  rw [div_eq_iff hn] at he
  rw [he,mul_comm]

theorem sum_cavityPathSpinWeight_eq_normalizer (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (b : ℝ) (hb : 0<b) :
    (∑σ : TerminalSpins (Configuration n) T,cavityPathSpinWeight D s a i T σ b)=
      cavityPathNormalizer D s a i j b := by
  let f : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T→ℝ:=fun p=>
    cavityPathNumerator D s a i T p.2 (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b p.1)
  let density:=finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s)
      a T (anisotropicRootEnergyMap D) 0
  let P:=(stdGaussian (CavityPathGaussianSpace T n)).prod
    (Measure.count : Measure (TerminalSpins (Configuration n) T))
  have he : f=fun p=>cavityPathNormalizer D s a i j b*density p := by
    funext p
    exact cavityPathNumerator_scaled_eq_normalizer_mul_density D s a i T p.2 b hb p.1
  have hi : Integrable density P := by
    have hh:=integrable_finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T (anisotropicRootEnergyMap D) 0
    simpa only [finiteCascadeTreeGaussianFlatReferenceMeasure,terminalSpinCountingLaw_eq_count] using hh
  have hf : Integrable f P:=by rw [he];exact hi.const_mul _
  have h1 : (∫p,density p∂P)=1:=by
    have hh:=integral_finiteCascadeTreeGaussianFlatDensity_one (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T (anisotropicRootEnergyMap D) 0
    simpa only [finiteCascadeTreeGaussianFlatReferenceMeasure,terminalSpinCountingLaw_eq_count] using hh
  have hsum : (∫p,f p∂P)=∑σ,cavityPathSpinWeight D s a i T σ b:=by
    rw [integral_prod_symm f hf,integral_count]
    rfl
  rw [←hsum,he,integral_const_mul,h1,mul_one]

def cavityPathMarkedExpectation (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (F : TerminalSpins (Configuration n) T→ℝ) (b : ℝ) : ℝ :=
  ∫p,F (finiteCascadeRecordTerminalSpins T p.2)
    ∂finiteCascadeTreeGaussianJointLaw (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T (anisotropicRootEnergyMap D) 0

theorem cavityPathMarkedExpectation_eq_weighted_sum (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (b : ℝ) (hb : 0<b) :
    cavityPathMarkedExpectation D s a i T F b=
      (∑σ,F σ*cavityPathSpinWeight D s a i T σ b)/cavityPathNormalizer D s a i j b := by
  let density:=finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n=>0)
    (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s)
      a T (anisotropicRootEnergyMap D) 0
  let P:=(stdGaussian (CavityPathGaussianSpace T n)).prod
    (Measure.count : Measure (TerminalSpins (Configuration n) T))
  have hi : Integrable density P := by
    have hh:=integrable_finiteCascadeTreeGaussianFlatDensity (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (anisotropicSchemeMass_nonneg s)
      (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) a T (anisotropicRootEnergyMap D) 0
    simpa only [finiteCascadeTreeGaussianFlatReferenceMeasure,terminalSpinCountingLaw_eq_count] using hh
  have hm : Measurable (fun p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T=>
      density p*F p.2):=
    (measurable_finiteCascadeTreeGaussianFlatDensity _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _).mul
      ((measurable_of_finite F).comp measurable_snd)
  let C:ℝ:=∑σ : TerminalSpins (Configuration n) T,|F σ|
  have hC : 0≤C:=Finset.sum_nonneg (fun σ _=>abs_nonneg _)
  have hF (σ : TerminalSpins (Configuration n) T) : |F σ|≤C:=
    Finset.single_le_sum (fun τ _=>abs_nonneg (F τ)) (Finset.mem_univ σ)
  have hdpos (p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) : 0≤density p:=
    (finiteCascadeTreeGaussianFlatDensity_pos _ _ (anisotropicSchemeMass_nonneg s) _ _ _ _ _ p).le
  have hiF : Integrable (fun p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T=>
      density p*F p.2) P := by
    apply (hi.const_mul C).mono' hm.aestronglyMeasurable
    exact .of_forall fun p=>by
      simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hdpos p)]
      exact (mul_le_mul_of_nonneg_left (hF p.2) (hdpos p)).trans_eq (mul_comm _ _)
  unfold cavityPathMarkedExpectation
  rw [integral_finiteCascadeTreeGaussianJointLaw_eq_flat_density _ _ (anisotropicSchemeMass_nonneg s)
    _ _ T _ _ (fun p : FiniteStateField (Configuration n)×Records (FiniteStateField (Configuration n))
      (Configuration n) T=>F (finiteCascadeRecordTerminalSpins T p.2)) ((measurable_of_finite F).comp
      ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd))]
  have hsp (p : CavityPathGaussianSpace T n×TerminalSpins (Configuration n) T) :
      finiteCascadeRecordTerminalSpins T (finiteCascadeTreeReferenceRootFlatRecord
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i b) s) T
          (anisotropicRootEnergyMap D) 0 p).2=p.2:=
    finiteCascadeRecordTerminalSpins_referenceRoot _ T _ _ p.1 p.2
  simp_rw [hsp]
  change (∫p,density p*F p.2∂finiteCascadeTreeGaussianFlatReferenceMeasure
    (S:=Configuration n) (I:=Fin n) (J:=AnisotropicCouplingIndex n) T)=_
  rw [finiteCascadeTreeGaussianFlatReferenceMeasure,terminalSpinCountingLaw_eq_count,
    integral_prod_symm _ hiF,integral_count]
  simp_rw [show ∀z σ,density (z,σ)=
      cavityPathNumerator D s a i T σ (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)/
        cavityPathNormalizer D s a i j b from fun z σ=>
      (cavityPathNumerator_scaled_eq_actual_density D s a i T σ b hb z).symm,
    div_mul_eq_mul_div,integral_div,integral_mul_const]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  change cavityPathSpinWeight D s a i T σ b*F σ/cavityPathNormalizer D s a i j b=
    F σ*cavityPathSpinWeight D s a i T σ b/cavityPathNormalizer D s a i j b
  rw [mul_comm]

def cavityPathSpinResponse (D : AnisotropicSpinModel n) (s : RSBScheme k) (a : ℝ) (i : Fin n)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (σ : TerminalSpins (Configuration n) T) (b : ℝ) : ℝ :=
  ∫z : CavityPathGaussianSpace T n,
    cavityPathNumerator D s a i T σ (b,gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)*
      cavityPathScoreGenerator D s a i T σ b (gaussianSelectedScale (cavitySelectedRootPathMask i T) b z)
        ∂stdGaussian (CavityPathGaussianSpace T n)

theorem hasDerivAt_cavityPathMarkedExpectation (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (i : Fin n) {j : ℕ} (T : FiniteTerminalGenealogy j) (hj : j≤k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F : TerminalSpins (Configuration n) T→ℝ) (b : ℝ) (hb : 0<b) :
    HasDerivAt (cavityPathMarkedExpectation D s a i T F)
      ((∑σ,F σ*cavityPathSpinResponse D s a i T σ b)/cavityPathNormalizer D s a i j b-
        cavityPathMarkedExpectation D s a i T F b*
          ((∑σ,cavityPathSpinResponse D s a i T σ b)/cavityPathNormalizer D s a i j b)) b := by
  have hnum : HasDerivAt (fun u=>∑σ,F σ*cavityPathSpinWeight D s a i T σ u)
      (∑σ,F σ*cavityPathSpinResponse D s a i T σ b) b:=by
    apply HasDerivAt.fun_sum
    intro σ _
    exact (hasDerivAt_cavityPathSpinWeight_score D s a i T hj σ b hb).const_mul _
  have hden : HasDerivAt (fun u=>∑σ,cavityPathSpinWeight D s a i T σ u)
      (∑σ,cavityPathSpinResponse D s a i T σ b) b:=by
    apply HasDerivAt.fun_sum
    intro σ _
    exact hasDerivAt_cavityPathSpinWeight_score D s a i T hj σ b hb
  have hn : (∑σ,cavityPathSpinWeight D s a i T σ b)≠0:=by
    rw [sum_cavityPathSpinWeight_eq_normalizer D s a i T b hb]
    exact (cavityPathNormalizer_pos D s a i j b).ne'
  have hd:=hnum.div hden hn
  rw [sum_cavityPathSpinWeight_eq_normalizer D s a i T b hb] at hd
  have he : ((∑σ,F σ*cavityPathSpinResponse D s a i T σ b)*cavityPathNormalizer D s a i j b-
      (∑σ,F σ*cavityPathSpinWeight D s a i T σ b)*(∑σ,cavityPathSpinResponse D s a i T σ b))/
      (cavityPathNormalizer D s a i j b)^2=
      (∑σ,F σ*cavityPathSpinResponse D s a i T σ b)/cavityPathNormalizer D s a i j b-
        cavityPathMarkedExpectation D s a i T F b*
          ((∑σ,cavityPathSpinResponse D s a i T σ b)/cavityPathNormalizer D s a i j b):=by
    rw [cavityPathMarkedExpectation_eq_weighted_sum D s a i T F b hb]
    field_simp [(cavityPathNormalizer_pos D s a i j b).ne']
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hb] with u hu
  dsimp only [Pi.div_apply]
  rw [cavityPathMarkedExpectation_eq_weighted_sum D s a i T F u hu,
    sum_cavityPathSpinWeight_eq_normalizer D s a i T u hu]

end QuantitativeFollowup
