module
public import QuantitativePaper.VectorProfileUniformGradientSecondVariation

@[expose] public section

/-! The actual second profile gradient and the third linearized reaction
have scheme-independent bounds. No generator or source bound is assumed. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellSecondVariation_gradient_eq_second_profile_deriv
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (q : ℝ) (hq : q∈Ico (s₀.q i) (s₀.q (i+1)))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    gradient (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,θ,p)) x=
      deriv (deriv (fun φ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2)) x)) θ := by
  let P : ℝ×Field n→ℝ:=fun z=>
    vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,z.1,p) z.2
  have hP : ContDiffAt ℝ ∞ P (θ,x):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((q,z.1,p),z.2))
    (g := fun z : VectorProfileCellParameter n×Field n=>
      vectorProfileCellPotentialFirstVariation s₀ s₁ β t i z.1 z.2) (θ,x)
    (contDiffAt_vectorProfileCellPotentialFirstVariation s₀ s₁ β t hβ ht i hi
      (q,θ,p) hq.2 hθ x) (by fun_prop)
  have hd:=deriv_partial_gradient P θ x hP
  have he : (fun φ=>gradient (fun y=>P (φ,y)) x)=ᶠ[𝓝 θ]
      (deriv (fun φ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2)) x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    exact vectorProfileCellFirstVariation_gradient_eq_profile_deriv s₀ s₁ β t hβ ht i hi q hq φ hφ p x
  rw [he.deriv_eq] at hd
  exact hd.symm

theorem norm_vectorGridProfileCellSecondVariation_gradient_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤vectorDyadicIndex j+2) (q : Paper.Overlap)
    (hq : (q:ℝ)∈Ico ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    ‖gradient (vectorProfileCellPotentialSecondVariation
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t i (q,θ,p)) x‖≤
        vectorProfileGradientSecondVariationBound n β t := by
  rw [vectorProfileCellSecondVariation_gradient_eq_second_profile_deriv _ _ β t hβ ht i hi q hq θ hθ p x]
  exact norm_vectorGridProfileTailRecursion_gradient_second_profile_deriv_le μ ν j β t hβ ht q p x θ hθ

def vectorProfileThirdReactionBound (n : ℕ) (β t : ℝ) : ℝ :=
  3*((1-t)*β^2)*(vectorProfileGradientVariationBound n β t*
    vectorProfileGradientSecondVariationBound n β t+vectorProfileGradientVariationBound n β t^2+
      Real.sqrt (n:ℝ)*vectorProfileGradientSecondVariationBound n β t)

theorem vectorProfileThirdReactionBound_nonneg (n : ℕ) (β t : ℝ) (ht : t≤1) :
    0≤vectorProfileThirdReactionBound n β t := by
  unfold vectorProfileThirdReactionBound
  have hK:=vectorProfileGradientVariationBound_nonneg n β t ht
  have hK2:=vectorProfileGradientSecondVariationBound_nonneg n β t ht
  positivity

theorem abs_vectorGridProfile_third_reaction_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤vectorDyadicIndex j+2) (q : Paper.Overlap)
    (hq : (q:ℝ)∈Ico ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
    let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
    let G:=gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,θ,p),y)) x
    let P:=gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,θ,p)) x
    let Q:=gradient (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,θ,p)) x
    |3*((1-t)*β^2)*(vectorProfileMass s₀ s₁ θ i*inner ℝ P Q+
      (s₁.m i-s₀.m i)*(‖P‖^2+inner ℝ G Q))|≤vectorProfileThirdReactionBound n β t := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let G:=gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,θ,p),y)) x
  let P:=gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,θ,p)) x
  let Q:=gradient (vectorProfileCellPotentialSecondVariation s₀ s₁ β t i (q,θ,p)) x
  let K:=vectorProfileGradientVariationBound n β t
  let K2:=vectorProfileGradientSecondVariationBound n β t
  have hK : 0≤K:=vectorProfileGradientVariationBound_nonneg n β t ht.le
  have hK2 : 0≤K2:=vectorProfileGradientSecondVariationBound_nonneg n β t ht.le
  have hP : ‖P‖≤K:=norm_vectorGridProfileCellFirstVariation_gradient_le μ ν j β t hβ ht i hi q hq θ hθ p x
  have hQ : ‖Q‖≤K2:=norm_vectorGridProfileCellSecondVariation_gradient_le μ ν j β t hβ ht i hi q hq θ hθ p x
  have hG : ‖G‖≤Real.sqrt (n:ℝ):=by
    have he : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,θ,p),y))=
        vectorFiniteCellPotential (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t p i q:=by
      funext y
      exact vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i q θ ⟨hθ.1.le,hθ.2.le⟩ p y
    dsimp only [G]
    rw [he]
    exact norm_vectorFiniteCellGradient_le (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩)
      β t q p i hi ⟨hq.1,hq.2.le⟩ x
  have hm : |vectorProfileMass s₀ s₁ θ i|≤1:=by
    have hmn : 0≤vectorProfileMass s₀ s₁ θ i:=
      (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩).m_nonneg hi
    rw [abs_of_nonneg hmn]
    exact (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩).m_le_one hi
  have hd : |s₁.m i-s₀.m i|≤1:=abs_le.mpr ⟨by
    linarith [s₀.m_nonneg hi,s₀.m_le_one hi,s₁.m_nonneg hi,s₁.m_le_one hi],by
    linarith [s₀.m_nonneg hi,s₀.m_le_one hi,s₁.m_nonneg hi,s₁.m_le_one hi]⟩
  have hPQ : |inner ℝ P Q|≤K*K2:=
    (abs_real_inner_le_norm P Q).trans (mul_le_mul hP hQ (norm_nonneg _) hK)
  have hGQ : |inner ℝ G Q|≤Real.sqrt (n:ℝ)*K2:=
    (abs_real_inner_le_norm G Q).trans (mul_le_mul hG hQ (norm_nonneg _) (Real.sqrt_nonneg _))
  have hSq : ‖P‖^2≤K^2:=sq_le_sq₀ (norm_nonneg _) hK |>.mpr hP
  have hfirst : |vectorProfileMass s₀ s₁ θ i*inner ℝ P Q|≤K*K2:=by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hm hPQ (abs_nonneg _) zero_le_one
  have hsecond : |(s₁.m i-s₀.m i)*(‖P‖^2+inner ℝ G Q)|≤K^2+Real.sqrt (n:ℝ)*K2:=by
    rw [abs_mul]
    have hh : |‖P‖^2+inner ℝ G Q|≤K^2+Real.sqrt (n:ℝ)*K2:=
      (abs_add_le _ _).trans (add_le_add (by rw [abs_of_nonneg (sq_nonneg ‖P‖)];exact hSq) hGQ)
    simpa only [one_mul] using mul_le_mul hd hh (abs_nonneg _) zero_le_one
  change |3*((1-t)*β^2)*(vectorProfileMass s₀ s₁ θ i*inner ℝ P Q+
    (s₁.m i-s₀.m i)*(‖P‖^2+inner ℝ G Q))|≤_
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤3*((1-t)*β^2))]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hfirst hsecond) |>.trans_eq
    (by ring)) (by positivity)

end QuantitativePaper
