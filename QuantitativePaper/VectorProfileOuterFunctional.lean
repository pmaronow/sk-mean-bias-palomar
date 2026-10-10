module
public import QuantitativePaper.VectorProfileOuterEnergySecondVariation
public import QuantitativePaper.VectorProfileOuterRegularity
public import QuantitativePaper.VectorProfileSchemeMix
public import QuantitativePaper.FiniteVectorFunctional
public import FourPapersCommon.AffineSecondDerivative

@[expose] public section

/-! The full finite-profile energy functional, with its actual CDF correction.
Its definition includes the ordinary-expectation extension at zero tilt. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2000000
variable {n k : ℕ}

def vectorProfileFiniteEnergyFunctional (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) : ℝ :=
  vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam θ - ((1-t)*β/2)*
    ∫ q in (0:ℝ)..1, q*Paper.parisiCDF
      (Paper.parisiMix (Paper.parisiSchemeMeasure s₀) (Paper.parisiSchemeMeasure s₁) θ) q

theorem vectorProfileFiniteEnergyFunctional_eq (s₀ s₁ : RSBScheme k)
    (hq : ∀ i, i ≤ k+2 → s₀.q i = s₁.q i)
    (β t lam θ : ℝ) (hn : 0 < n) (hβ : β ≠ 0) (hlam : lam ≠ 0)
    (hθ : θ ∈ Icc (0:ℝ) 1) :
    vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam θ =
      finiteVectorFunctional n (vectorProfileScheme s₀ s₁ θ hθ) β t (lam/β)/β := by
  unfold vectorProfileFiniteEnergyFunctional vectorProfileOuterEnergy
  rw [vectorProfileOuterNormalized_of_ne s₀ s₁ β t (lam/β) θ (div_ne_zero hlam hβ),
    vectorProfileOuterPartition_eq s₀ s₁ β t (lam/β) θ hθ,
    ←vectorProfileSchemeMeasure_mix s₀ s₁ hq θ hθ]
  unfold finiteVectorFunctional vectorOuterPartition
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hn0,hβ,hlam]

theorem vectorProfileFiniteEnergyFunctional_eventually_affine (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) 1) :
    vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam =ᶠ[𝓝 θ]
      (fun y => vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam y - ((1-t)*β/2)*
        ((1-y)*(∫ q in (0:ℝ)..1, q*Paper.parisiCDF (Paper.parisiSchemeMeasure s₀) q)+
          y*(∫ q in (0:ℝ)..1, q*Paper.parisiCDF (Paper.parisiSchemeMeasure s₁) q))) := by
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
  exact congrArg (fun r => vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam y -
    ((1-t)*β/2)*r) (Paper.parisiCorrection_integral_mix
      (Paper.parisiSchemeMeasure s₀) (Paper.parisiSchemeMeasure s₁) y ⟨hy.1.le,hy.2.le⟩)

theorem contDiffAt_vectorProfileOuterEnergy (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (lam θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam) θ :=
  (contDiffAt_vectorProfileOuterNormalized s₀ s₁ β t ht (lam/β) θ hθ).div_const ((n:ℝ)*β)

theorem vectorProfileFiniteEnergyFunctional_second_derivative_eq (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (lam θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) 1) :
    iteratedDeriv 2 (vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam) θ =
      iteratedDeriv 2 (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam) θ := by
  let I₀ := ∫ q in (0:ℝ)..1, q*Paper.parisiCDF (Paper.parisiSchemeMeasure s₀) q
  let I₁ := ∫ q in (0:ℝ)..1, q*Paper.parisiCDF (Paper.parisiSchemeMeasure s₁) q
  have he : vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam =ᶠ[𝓝 θ]
      (fun y => 1*vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam y +
        (-((1-t)*β/2)*(I₁-I₀))*y + (-((1-t)*β/2)*I₀)) := by
    filter_upwards [vectorProfileFiniteEnergyFunctional_eventually_affine s₀ s₁ β t lam θ hθ]
      with y hy
    rw [hy]
    dsimp [I₀,I₁]
    ring
  rw [he.iteratedDeriv_eq 2]
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,one_mul] using
    deriv_deriv_affine_add (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam) θ 1
      (-((1-t)*β/2)*(I₁-I₀)) (-((1-t)*β/2)*I₀)
      (contDiffAt_vectorProfileOuterEnergy s₀ s₁ β t ht lam θ hθ)

theorem vectorProfileFiniteEnergyFunctional_second_variation (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β ≠ 0) (ht : t ≤ 1) (hn : 0 < n)
    (lam θ : ℝ) (hθ : θ ∈ Ioo (0:ℝ) 1) :
    iteratedDeriv 2 (vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam) θ =
      (∫ p : Couplings n×ℝ, vectorProfileOuterDerivative s₀ s₁ β t 2 θ p
        ∂vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t (lam/β))/((n:ℝ)*β)+
      (lam/(n:ℝ))*variance (fun p : Couplings n×ℝ =>
        vectorProfileOuterDerivative s₀ s₁ β t 1 θ p/β)
        (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t (lam/β)) := by
  rw [vectorProfileFiniteEnergyFunctional_second_derivative_eq s₀ s₁ β t ht lam θ hθ]
  exact vectorProfileOuterEnergy_second_variation s₀ s₁ β t hβ ht hn lam θ hθ

end QuantitativePaper
