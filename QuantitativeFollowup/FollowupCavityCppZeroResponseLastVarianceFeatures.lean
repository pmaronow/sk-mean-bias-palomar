module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVarianceKernels
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalar
public import QuantitativeFollowup.FollowupCavityFixedRowObservableBounds

@[expose] public section

/-! Literal retained-node scalar/rest observables separate under the
actual finite recursion for every independently varied last variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem cavityLastVariance_terminalJointFeature (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (v : ℝ) (hv : 0 < v)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1))
    (f : Configuration n → ℝ) (b : Bool → ℝ) :
    anisotropicTerminalFeatureMean (cavityLastVarianceModel n β ρ hβ hρ v hv)
      (fun σ=>f (cavityRestConfiguration σ)*b (σ (Fin.last n)))
      (anisotropicParameterPoint g x) =
      anisotropicTerminalFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) f
        (anisotropicParameterPoint (cavityRestDisorderProjection n g) (cavityRestFieldProjection n x)) *
      (∫e,b e ∂scalarSpinLaw (x (Fin.last n))) :=
  cavityTerminalJointFeature_zero n β ρ hβ hρ g x f b

 theorem cavityScalarFiniteFeatureMean_one (s : RSBScheme k) (β : ℝ) (j : ℕ) (x : ℝ) :
    cavityScalarFiniteFeatureMean s β j (fun _=>1) x = 1 := by
  induction j generalizing x with
  | zero =>
    simp only [cavityScalarFiniteFeatureMean_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
  | succ j ih =>
    rw [cavityScalarFiniteFeatureMean_succ]
    simp_rw [ih]
    simp

 theorem anisotropicFiniteFeatureMean_one (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (j : ℕ) (P : AnisotropicParameter n) :
    anisotropicFiniteFeatureMean D s j (fun _=>1) P = 1 := by
  simp [anisotropicFiniteFeatureMean]

theorem cavityLastVariance_finiteJointFeature_product (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (v : ℝ) (hv : 0 < v) (j : ℕ)
    (f : Configuration n → ℝ) (b : Bool → ℝ) (P : AnisotropicParameter (n+1)) :
    anisotropicFiniteFeatureMean
      (cavityLastVarianceModel n β ρ hβ hρ v hv) s j
        (fun σ => f (cavityRestConfiguration σ) * b (σ (Fin.last n))) P =
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j f
        (cavityRestParameterProjection n P) *
      cavityScalarFiniteFeatureMean s (Real.sqrt v) j b (P (Sum.inr (Fin.last n))) := by
  let D := cavityLastVarianceModel n β ρ hβ hρ v hv
  let R := followupCavityRestSpinModel n β ρ hβ hρ
  let β0 := Real.sqrt v
  induction j generalizing P with
  | zero =>
      let g : AnisotropicDisorder (n+1) := WithLp.toLp 2 (fun e => P (Sum.inl e))
      let x : QuantitativePaper.Field (n+1) := WithLp.toLp 2 (fun i => P (Sum.inr i))
      have hid : anisotropicParameterPoint g x = P := by ext i; cases i <;> rfl
      rw [←hid, cavityRestParameterProjection_point, anisotropicFiniteFeatureMean_zero,
        anisotropicFiniteFeatureMean_zero, cavityScalarFiniteFeatureMean_zero]
      exact cavityLastVariance_terminalJointFeature n β ρ hβ hρ v hv g x f b
  | succ j ih =>
      let g : AnisotropicDisorder (n+1) := WithLp.toLp 2 (fun e => P (Sum.inl e))
      let x : QuantitativePaper.Field (n+1) := WithLp.toLp 2 (fun i => P (Sum.inr i))
      have hid : anisotropicParameterPoint g x = P := by ext i; cases i <;> rfl
      rw [anisotropicFiniteFeatureMean_succ_kernel,
        anisotropicFiniteFeatureMean_succ_kernel, cavityScalarFiniteFeatureMean_succ]
      simp_rw [ih]
      have hm : Measurable (fun z : AnisotropicParameter n × ℝ =>
          anisotropicFiniteFeatureMean R s j f z.1 * cavityScalarFiniteFeatureMean s β0 j b z.2) :=
        ((measurable_anisotropicFiniteFeatureMean R s j f).comp measurable_fst).mul
          ((measurable_cavityScalarFiniteFeatureMean s β0 j b).comp measurable_snd)
      change (∫ Q, (fun z : AnisotropicParameter n × ℝ =>
        anisotropicFiniteFeatureMean R s j f z.1 * cavityScalarFiniteFeatureMean s β0 j b z.2)
          (cavityIndependentParameterSplit n Q) ∂anisotropicDepthKernel D s j P) = _
      rw [←integral_map (measurable_cavityIndependentParameterSplit n).aemeasurable hm.aestronglyMeasurable,
        ←hid, cavityLastVariance_depthKernel_product, integral_prod_mul, cavityRestParameterProjection_point]
      rfl


 theorem cavityLastVariance_finiteSpinFeature (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (v : ℝ) (hv : 0 < v)
    (j : ℕ) (P : AnisotropicParameter (n+1)) :
    anisotropicFiniteFeatureMean (cavityLastVarianceModel n β ρ hβ hρ v hv) s j
      (fun σ=>Paper.spinSign (σ (Fin.last n))) P =
      parisiFDeriv s (Real.sqrt v) j (P (Sum.inr (Fin.last n))) := by
  simpa only [one_mul, anisotropicFiniteFeatureMean_one, cavityScalarFiniteFeatureMean_sign] using
    cavityLastVariance_finiteJointFeature_product s n β ρ hβ hρ v hv j (fun _=>1) Paper.spinSign P

 theorem cavityLastVariance_finiteRestFeature (s : RSBScheme k) (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) (v : ℝ) (hv : 0 < v)
    (j : ℕ) (f : Configuration n → ℝ) (P : AnisotropicParameter (n+1)) :
    anisotropicFiniteFeatureMean (cavityLastVarianceModel n β ρ hβ hρ v hv) s j
      (fun σ=>f (cavityRestConfiguration σ)) P =
      anisotropicFiniteFeatureMean (followupCavityRestSpinModel n β ρ hβ hρ) s j f
        (cavityRestParameterProjection n P) := by
  simpa only [mul_one, cavityScalarFiniteFeatureMean_one] using
    cavityLastVariance_finiteJointFeature_product s n β ρ hβ hρ v hv j f (fun _=>1) P

end QuantitativeFollowup
