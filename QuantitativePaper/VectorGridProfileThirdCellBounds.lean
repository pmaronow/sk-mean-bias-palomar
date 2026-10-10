module
public import QuantitativePaper.VectorGridProfileThirdClosedCells

@[expose] public section

/-! Exact closed-cell second profile variations agree with the actual
tail derivatives, and their expected increments have a uniform bound. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellPotentialThirdVariation_eq_tail
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (i : ℕ) (hi : i≤k+1)
    (q : ℝ) (hq : q∈Icc (s₀.q i) (s₀.q (i+1)))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    vectorProfileCellPotentialThirdVariation s₀ s₁ β t i (q,θ,p) x=
      deriv (deriv (deriv (fun φ=>vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2) x))) θ := by
  have he : (fun φ=>vectorProfileCellJointPotential s₀ s₁ β t i ((q,φ,p),x))=ᶠ[𝓝 θ]
      (fun φ=>vectorProfileTailRecursion s₀ s₁ β t q φ p (k+2) x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    exact vectorProfilePhysicalCell_eq_tail s₀ s₁ β t i hi q φ ⟨hφ.1.le,hφ.2.le⟩ hq p x
  exact he.deriv.deriv.deriv_eq

theorem vectorProfileTailRecursion_third_profile_terminal_zero
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    deriv (deriv (deriv (fun φ=>vectorProfileTailRecursion s₀ s₁ β t 1 φ p (k+2) x))) θ=0 := by
  have he : (fun φ=>vectorProfileTailRecursion s₀ s₁ β t 1 φ p (k+2) x)=ᶠ[𝓝 θ]
      (fun _ : ℝ=>vectorTerminalPotential n β t p x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    rw [vectorProfileTailRecursion_eq_scheme s₀ s₁ β t 1 φ ⟨hφ.1.le,hφ.2.le⟩,
      vectorTailRecursion_one _ β t p le_rfl]
  rw [he.deriv.deriv.deriv_eq]
  have hd : deriv (fun _ : ℝ=>vectorTerminalPotential n β t p x)=(fun _=>0):=by
    funext φ
    exact deriv_const φ _
  rw [hd]
  have hz : deriv (fun _ : ℝ=>(0:ℝ))=(fun _=>0):=by funext φ;exact deriv_const φ _
  rw [hz,deriv_const]

theorem vectorGridProfile_third_restart_cell_bound
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (q : Paper.Overlap)
    (p : Couplings n×ℝ) (x : Field n) (i : ℕ) (hi : i≤vectorDyadicIndex j+2)
    (a b : ℝ) (ha : 0≤a) (hab : a≤b) (hb : b≤1)
    (hcell : ∀r∈Icc a b,(q:ℝ)+r∈Icc
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))) :
    |vectorGridProfileThirdRestartMoment μ ν j β t θ ht.le q p x i b-
      vectorGridProfileThirdRestartMoment μ ν j β t θ ht.le q p x i a|≤
        vectorProfileThirdReactionBound n β t*(b-a) := by
  obtain ⟨hI,hD⟩:=vectorGridProfile_third_restart_closed μ ν j β t hβ ht θ hθ q p x i hi
    a b ha hab hb hcell
  rw [hD,←Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_of_norm_le_const_ae (C:=vectorProfileThirdReactionBound n β t) ?_).trans_eq
    (by rw [abs_of_nonneg (sub_nonneg.mpr hab)])
  filter_upwards [volume.ae_ne b] with r hr hmem
  rw [uIoc_of_le hab] at hmem
  have hleft:=(hcell a ⟨le_rfl,hab⟩).1
  have hright:=(hcell b ⟨hab,le_rfl⟩).2
  rw [Real.norm_eq_abs]
  exact abs_vectorGridProfileThirdRestartSourceMean_le μ ν j β t hβ ht θ hθ q p x i hi r
    (ha.trans hmem.1.le) ⟨by linarith [hmem.1],by
      have hh : r<b:=lt_of_le_of_ne hmem.2 hr
      linarith⟩

end QuantitativePaper
