module
public import QuantitativePaper.VectorProfileSecondLinearizedPDE
public import QuantitativePaper.VectorProfileGradientLipschitz
public import QuantitativePaper.VectorFiniteCellGradientBounds

@[expose] public section

/-! Actual dimension-only bounds on the first profile gradient and the
second linearized source in each strict dyadic cell. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellFirstVariation_gradient_eq_profile_deriv
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤k+1) (q : ℝ) (hq : q∈Ico (s₀.q i) (s₀.q (i+1)))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,θ,p)) x=
      deriv (fun φ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2)) x) θ := by
  let U : ℝ×Field n→ℝ:=fun z=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,z.1,p),z.2)
  have hU : ContDiffAt ℝ ∞ U (θ,x):=ContDiffAt.comp
    (f := fun z : ℝ×Field n=>((q,z.1,p),z.2))
    (g := vectorProfileCellJointPotential s₀ s₁ β t i) (θ,x)
    (contDiffAt_vectorProfileCellJointPotential s₀ s₁ β t hβ ht i hi ((q,θ,p),x) hq.2 hθ)
    (by fun_prop)
  have hd:=deriv_partial_gradient U θ x hU
  have he : (fun φ=>gradient (fun y=>U (φ,y)) x)=ᶠ[𝓝 θ]
      (fun φ=>gradient (vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2)) x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    have hef : (fun y=>U (φ,y))=vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2):=by
      funext y
      exact vectorProfilePhysicalCell_eq_tail s₀ s₁ β t i hi q φ
        ⟨hφ.1.le,hφ.2.le⟩ ⟨hq.1,hq.2.le⟩ p y
    rw [hef]
  rw [he.deriv_eq] at hd
  exact hd.symm

theorem norm_vectorGridProfileCellFirstVariation_gradient_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤vectorDyadicIndex j+2) (q : Paper.Overlap)
    (hq : (q:ℝ)∈Ico ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    ‖gradient (vectorProfileCellPotentialFirstVariation
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t i (q,θ,p)) x‖≤
        vectorProfileGradientVariationBound n β t := by
  rw [vectorProfileCellFirstVariation_gradient_eq_profile_deriv _ _ β t hβ ht i hi q hq θ hθ p x]
  exact norm_vectorGridProfileTailRecursion_gradient_profile_deriv_le μ ν j β t hβ ht q p x θ hθ

def vectorProfileSecondReactionBound (n : ℕ) (β t : ℝ) : ℝ :=
  ((1-t)*β^2)*(vectorProfileGradientVariationBound n β t^2+
    2*Real.sqrt (n:ℝ)*vectorProfileGradientVariationBound n β t)

theorem vectorProfileSecondReactionBound_nonneg (n : ℕ) (β t : ℝ) (ht : t≤1) :
    0≤vectorProfileSecondReactionBound n β t := by
  unfold vectorProfileSecondReactionBound
  have hK:=vectorProfileGradientVariationBound_nonneg n β t ht
  positivity

theorem abs_vectorGridProfile_second_reaction_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (i : ℕ) (hi : i≤vectorDyadicIndex j+2) (q : Paper.Overlap)
    (hq : (q:ℝ)∈Ico ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1)))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
    let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
    let G:=gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,θ,p),y)) x
    let P:=gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,θ,p)) x
    |((1-t)*β^2)*(vectorProfileMass s₀ s₁ θ i*‖P‖^2+
      2*(s₁.m i-s₀.m i)*inner ℝ G P)|≤vectorProfileSecondReactionBound n β t := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let G:=gradient (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,θ,p),y)) x
  let P:=gradient (vectorProfileCellPotentialFirstVariation s₀ s₁ β t i (q,θ,p)) x
  let K:=vectorProfileGradientVariationBound n β t
  have hK : 0≤K:=vectorProfileGradientVariationBound_nonneg n β t ht.le
  have hP : ‖P‖≤K:=norm_vectorGridProfileCellFirstVariation_gradient_le μ ν j β t hβ ht i hi q hq θ hθ p x
  have hG : ‖G‖≤Real.sqrt (n:ℝ):=by
    have he : (fun y=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,θ,p),y))=
        vectorFiniteCellPotential (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t p i q:=by
      funext y
      exact vectorProfilePhysicalCell_eq_finiteCell s₀ s₁ β t i q θ ⟨hθ.1.le,hθ.2.le⟩ p y
    dsimp only [G]
    rw [he]
    exact norm_vectorFiniteCellGradient_le (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩)
      β t q p i hi ⟨hq.1,hq.2.le⟩ x
  have hm : 0≤vectorProfileMass s₀ s₁ θ i ∧ vectorProfileMass s₀ s₁ θ i≤1:=
    ⟨(vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩).m_nonneg hi,
      (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩).m_le_one hi⟩
  have hd : |s₁.m i-s₀.m i|≤1:=abs_le.mpr ⟨by
    linarith [s₀.m_nonneg hi,s₀.m_le_one hi,s₁.m_nonneg hi,s₁.m_le_one hi],by
    linarith [s₀.m_nonneg hi,s₀.m_le_one hi,s₁.m_nonneg hi,s₁.m_le_one hi]⟩
  have hInner : |inner ℝ G P|≤Real.sqrt (n:ℝ)*K:=
    (abs_real_inner_le_norm G P).trans (mul_le_mul hG hP (norm_nonneg _) (Real.sqrt_nonneg _))
  have hSq : ‖P‖^2≤K^2:=sq_le_sq₀ (norm_nonneg _) hK |>.mpr hP
  have hfirst : |vectorProfileMass s₀ s₁ θ i*‖P‖^2|≤K^2:=by
    rw [abs_of_nonneg (mul_nonneg hm.1 (sq_nonneg _))]
    exact (mul_le_of_le_one_left (sq_nonneg _) hm.2).trans hSq
  have hsecond : |2*(s₁.m i-s₀.m i)*inner ℝ G P|≤2*Real.sqrt (n:ℝ)*K:=by
    rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh:=mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ)≤2)) hInner
      (abs_nonneg _) (by norm_num : (0:ℝ)≤2*1)
    simpa only [mul_one,mul_assoc] using hh
  change |((1-t)*β^2)*(vectorProfileMass s₀ s₁ θ i*‖P‖^2+
    2*(s₁.m i-s₀.m i)*inner ℝ G P)|≤_
  rw [abs_mul,abs_of_nonneg (mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg β))]
  exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hfirst hsecond))
    (mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg β))

end QuantitativePaper
