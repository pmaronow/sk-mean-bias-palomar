module
public import QuantitativePaper.VectorProfileEndpointSecondVariation
public import QuantitativePaper.VectorProfileOuterFunctional

@[expose] public section

/-! Smooth affine-penalty extension of the physical profile functional.
The physical formula agrees on [0,1]; its endpoint derivatives are within
that interval, as in the paper's one-sided convention. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2600000
variable {n k : ℕ}

def vectorProfileAffineEnergyFunctional (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) : ℝ :=
  vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam θ - ((1-t)*β/2)*
    ((1-θ)*(∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s₀) q)+
      θ*(∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s₁) q))

theorem vectorProfileFiniteEnergyFunctional_eq_affine (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam θ=
      vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam θ := by
  unfold vectorProfileFiniteEnergyFunctional vectorProfileAffineEnergyFunctional
  rw [Paper.parisiCorrection_integral_mix _ _ θ hθ]

theorem contDiff_vectorProfileOuterEnergy_all_theta (s₀ s₁ : RSBScheme k)
    (β t lam : ℝ) :
    ContDiff ℝ ∞ (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam) :=
  (contDiff_vectorProfileOuterNormalized_all_theta s₀ s₁ β t (lam/β)).div_const ((n:ℝ)*β)

theorem contDiff_vectorProfileAffineEnergyFunctional (s₀ s₁ : RSBScheme k)
    (β t lam : ℝ) :
    ContDiff ℝ ∞ (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam) := by
  unfold vectorProfileAffineEnergyFunctional
  exact (contDiff_vectorProfileOuterEnergy_all_theta s₀ s₁ β t lam).sub
    (contDiff_const.mul (((contDiff_const.sub contDiff_id).mul contDiff_const).add
      (contDiff_id.mul contDiff_const)))

theorem vectorProfileAffineEnergyFunctional_second_derivative_eq (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) :
    iteratedDeriv 2 (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam) θ=
      iteratedDeriv 2 (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam) θ := by
  let I₀:=∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s₀) q
  let I₁:=∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s₁) q
  have he : vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam=
      (fun y=>1*vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam y+
        (-((1-t)*β/2)*(I₁-I₀))*y+(-((1-t)*β/2)*I₀)):=by
    funext y
    dsimp [vectorProfileAffineEnergyFunctional,I₀,I₁]
    ring
  rw [he]
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,one_mul] using
    deriv_deriv_affine_add (vectorProfileOuterEnergy (n:=n) s₀ s₁ β t lam) θ 1
      (-((1-t)*β/2)*(I₁-I₀)) (-((1-t)*β/2)*I₀)
      (contDiff_vectorProfileOuterEnergy_all_theta s₀ s₁ β t lam).contDiffAt

theorem vectorProfileFiniteEnergyFunctional_hasDerivWithinAt_closed (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam)
      (deriv (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam) θ)
      (Icc (0:ℝ) 1) θ := by
  exact (((contDiff_vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam).differentiable
    (by simp) θ).hasDerivAt.hasDerivWithinAt).congr
    (fun y hy=>vectorProfileFiniteEnergyFunctional_eq_affine s₀ s₁ β t lam y hy)
    (vectorProfileFiniteEnergyFunctional_eq_affine s₀ s₁ β t lam θ hθ)

theorem vectorProfileFiniteEnergyFunctional_derivWithin_closed (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    derivWithin (vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam) (Icc (0:ℝ) 1) θ=
      deriv (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam) θ :=
  (vectorProfileFiniteEnergyFunctional_hasDerivWithinAt_closed s₀ s₁ β t lam θ hθ).derivWithin
    (uniqueDiffOn_Icc (by norm_num : (0:ℝ)<1) θ hθ)

theorem vectorProfileFiniteEnergyFunctional_second_hasDerivWithinAt_closed (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (derivWithin (vectorProfileFiniteEnergyFunctional (n:=n) s₀ s₁ β t lam) (Icc (0:ℝ) 1))
      (iteratedDeriv 2 (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam) θ)
      (Icc (0:ℝ) 1) θ := by
  have hs : ContDiff ℝ 2 (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam):=
    (contDiff_vectorProfileAffineEnergyFunctional s₀ s₁ β t lam).of_le (by simp)
  have hd : HasDerivWithinAt (deriv (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam))
      (iteratedDeriv 2 (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam) θ)
      (Icc (0:ℝ) 1) θ:=by
    simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using
      (hs.differentiable_deriv_two θ).hasDerivAt.hasDerivWithinAt (s:=Icc (0:ℝ) 1)
  exact hd.congr
    (fun y hy=>vectorProfileFiniteEnergyFunctional_derivWithin_closed s₀ s₁ β t lam y hy)
    (vectorProfileFiniteEnergyFunctional_derivWithin_closed s₀ s₁ β t lam θ hθ)

theorem vectorProfileAffineEnergyFunctional_second_variation_closed (s₀ s₁ : RSBScheme k)
    (β t lam θ : ℝ) (hβ : β≠0) (hn : 0<n) (hθ : θ∈Icc (0:ℝ) 1) :
    iteratedDeriv 2 (vectorProfileAffineEnergyFunctional (n:=n) s₀ s₁ β t lam) θ=
      (∫p : Couplings n×ℝ,vectorProfileOuterDerivative s₀ s₁ β t 2 θ p
        ∂vectorOuterLaw (vectorProfileScheme s₀ s₁ θ hθ) β t (lam/β))/((n:ℝ)*β)+
      (lam/(n:ℝ))*variance (fun p : Couplings n×ℝ=>
        vectorProfileOuterDerivative s₀ s₁ β t 1 θ p/β)
        (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ hθ) β t (lam/β)) := by
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  rw [vectorProfileAffineEnergyFunctional_second_derivative_eq]
  change iteratedDeriv 2 (fun y=>vectorProfileOuterNormalized (n:=n) s₀ s₁ β t (lam/β) y/((n:ℝ)*β)) θ=_
  rw [iteratedDeriv_div_const,vectorProfileOuterNormalized_second_variation_closed s₀ s₁ β t (lam/β) θ hθ]
  have he : (fun p : Couplings n×ℝ=>vectorProfileOuterDerivative s₀ s₁ β t 1 θ p/β)=
      (fun p=>β⁻¹*vectorProfileOuterDerivative s₀ s₁ β t 1 θ p):=by
    funext p
    ring
  rw [he,variance_const_mul]
  field_simp [hn0,hβ]
  <;>ring

end QuantitativePaper
