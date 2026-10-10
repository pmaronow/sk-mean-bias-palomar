module
public import QuantitativeFollowup.AnisotropicSpinModel

@[expose] public section

/-! The literal one-site row interpolation: the incident coupling variance
is alpha*u/n, the rest auxiliary variance is c, and the final auxiliary
variance is d-alpha*u. Both endpoints and positivity are derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup

def followupCavityC (β ρ : ℝ) : ℝ := β^2*ρ
def followupCavityAlpha (n : ℕ) (β ρ : ℝ) : ℝ :=
  β^2*(1-ρ)*(n:ℝ)/(n+1)
def followupCavityD (n : ℕ) (β ρ : ℝ) : ℝ :=
  followupCavityC β ρ + followupCavityAlpha n β ρ
def followupCavityB (n : ℕ) (β ρ u : ℝ) : ℝ :=
  followupCavityD n β ρ - followupCavityAlpha n β ρ*u

theorem followupCavityAlpha_nonneg (n : ℕ) (β ρ : ℝ) (hρ : ρ ≤ 1) :
    0 ≤ followupCavityAlpha n β ρ := by
  unfold followupCavityAlpha
  exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hρ))
    (Nat.cast_nonneg n)) (by positivity)

theorem followupCavityD_identity (n : ℕ) (β ρ : ℝ) :
    followupCavityD n β ρ = β^2*(1-(1-ρ)/(n+1)) := by
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  unfold followupCavityD followupCavityC followupCavityAlpha
  field_simp
  <;> ring

theorem followupCavityD_window (n : ℕ) (hn : 0 < n) (β ρ : ℝ)
    (hρ : ρ ∈ Icc 0 1) : followupCavityD n β ρ ∈ Icc (β^2/2) (β^2) := by
  have hN : (2:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast (show 2 ≤ n+1 by omega)
  have hfrac : (1-ρ)/((n:ℝ)+1) ∈ Icc (0:ℝ) (1/2) := by
    constructor
    · exact div_nonneg (by linarith [hρ.2]) (by positivity)
    · apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
      nlinarith [hρ.1]
  rw [followupCavityD_identity]
  constructor <;> nlinarith [sq_nonneg β,hfrac.1,hfrac.2]

theorem followupCavityB_window (n : ℕ) (β ρ u : ℝ) (hρ : ρ ≤ 1)
    (hu : u ∈ Icc 0 1) :
    followupCavityB n β ρ u ∈ Icc (followupCavityC β ρ) (followupCavityD n β ρ) := by
  have hα := followupCavityAlpha_nonneg n β ρ hρ
  unfold followupCavityB followupCavityD
  constructor <;> nlinarith [hu.1,hu.2]

@[simp] theorem followupCavityB_zero (n : ℕ) (β ρ : ℝ) :
    followupCavityB n β ρ 0 = followupCavityD n β ρ := by simp [followupCavityB]

@[simp] theorem followupCavityB_one (n : ℕ) (β ρ : ℝ) :
    followupCavityB n β ρ 1 = followupCavityC β ρ := by
  simp [followupCavityB,followupCavityD]

def followupCavityRestCoupling (n : ℕ) (β ρ : ℝ) : ℝ :=
  β*Real.sqrt (1-ρ)/Real.sqrt (n+1)

def followupCavityRowCoupling (n : ℕ) (β ρ u : ℝ) : ℝ :=
  Real.sqrt (followupCavityAlpha n β ρ*u/(n:ℝ))

theorem followupCavityRowCoupling_square (n : ℕ) (β ρ u : ℝ)
    (hρ : ρ ≤ 1) (hu : 0 ≤ u) :
    followupCavityRowCoupling n β ρ u ^ 2 = followupCavityAlpha n β ρ*u/(n:ℝ) := by
  exact Real.sq_sqrt (div_nonneg (mul_nonneg (followupCavityAlpha_nonneg n β ρ hρ) hu)
    (Nat.cast_nonneg n))

@[simp] theorem followupCavityRowCoupling_zero (n : ℕ) (β ρ : ℝ) :
    followupCavityRowCoupling n β ρ 0 = 0 := by
  simp [followupCavityRowCoupling]

theorem followupCavityRowCoupling_one (n : ℕ) (hn : 0 < n) (β ρ : ℝ)
    (hβ : 0 ≤ β) (hρ : ρ ≤ 1) :
    followupCavityRowCoupling n β ρ 1 = followupCavityRestCoupling n β ρ := by
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hN : (n:ℝ)+1 ≠ 0 := by positivity
  have hrow := followupCavityRowCoupling_square n β ρ 1 hρ zero_le_one
  have hrest : followupCavityRestCoupling n β ρ ^ 2 = β^2*(1-ρ)/(n+1) := by
    unfold followupCavityRestCoupling
    rw [div_pow,mul_pow,Real.sq_sqrt (by linarith),Real.sq_sqrt (by positivity)]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by unfold followupCavityRestCoupling; positivity)).mp
  change followupCavityRowCoupling n β ρ 1 ^ 2 = followupCavityRestCoupling n β ρ ^ 2
  rw [hrow,hrest]
  unfold followupCavityAlpha
  field_simp

/-- Concrete Gaussian pair-coupling model, with all diagonal couplings zero.
The independent Gaussian coordinates are those of anisotropicDisorderLaw. -/
def followupCavitySpinModel (n : ℕ) (β ρ : ℝ) (hβ : 0 < β)
    (hρ : ρ ∈ Ioc 0 1) (u : ℝ) (hu : u ∈ Icc 0 1) : AnisotropicSpinModel (n+1) where
  variance i := if i = Fin.last n then followupCavityB n β ρ u else followupCavityC β ρ
  variance_pos i := by
    have hc : 0 < followupCavityC β ρ := mul_pos (sq_pos_of_pos hβ) hρ.1
    split_ifs
    · exact hc.trans_le (followupCavityB_window n β ρ u hρ.2 hu).1
    · exact hc
  coupling e := if e.1.1 = e.1.2 then 0 else
    if e.1.2 = Fin.last n then followupCavityRowCoupling n β ρ u
    else followupCavityRestCoupling n β ρ

@[simp] theorem followupCavitySpinModel_variance_last (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc 0 1) (u : ℝ) (hu : u ∈ Icc 0 1) :
    (followupCavitySpinModel n β ρ hβ hρ u hu).variance (Fin.last n) =
      followupCavityB n β ρ u := by simp [followupCavitySpinModel]

theorem followupCavitySpinModel_variance_rest (n : ℕ) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc 0 1) (u : ℝ) (hu : u ∈ Icc 0 1) (i : Fin n) :
    (followupCavitySpinModel n β ρ hβ hρ u hu).variance i.castSucc = followupCavityC β ρ := by
  simp [followupCavitySpinModel,Fin.castSucc_ne_last]

theorem followupCavitySpinModel_coupling_one (n : ℕ) (hn : 0 < n) (β ρ : ℝ)
    (hβ : 0 < β) (hρ : ρ ∈ Ioc 0 1) (e : AnisotropicCouplingIndex (n+1))
    (he : e.1.1 ≠ e.1.2) :
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩).coupling e =
      followupCavityRestCoupling n β ρ := by
  simp only [followupCavitySpinModel,he,ite_false]
  split_ifs
  · exact followupCavityRowCoupling_one n hn β ρ hβ.le hρ.2
  · rfl

end QuantitativeFollowup
