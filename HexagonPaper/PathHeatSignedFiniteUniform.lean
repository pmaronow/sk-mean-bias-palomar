module
public import HexagonPaper.PathHeatSignedFiniteData

@[expose] public section

/-! Explicit common constants for the finite signed-jet heat data. These
constants depend only on the source bounds, and are shared over transport
parameter families. -/
noncomputable section
open scoped Topology NNReal ContDiff
namespace HexagonPaper
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def pathHeatFiniteGrowthBound (B Sf Mf Pg Qg C0 : ℝ≥0) : ℝ≥0 :=
  let T : ℝ := 1+Sf+Mf
  let G : ℕ→ℝ := fun _=>B+Pg+Qg
  let P := gaussianWeightedJetCoefficient 1 T G
  ⟨(P 0+P 1+P 2)*Real.exp C0,by
    have hp (j : ℕ) : 0≤P j := gaussianWeightedJetCoefficient_nonneg 1 T
      (by dsimp [T];positivity) G (by intro i;dsimp [G];positivity) j
    exact mul_nonneg (add_nonneg (add_nonneg (hp 0) (hp 1)) (hp 2)) (Real.exp_pos _).le⟩

theorem pathHeat_finiteDatum_growthBound
    (f g : Field n→ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (B Sf Mf Pg Qg C0 C1 : ℝ≥0)
    (hg0 : ∀x,‖g x‖≤B) (hf1 : ∀x,‖fderiv ℝ f x‖≤Sf)
    (hf2 : ∀x,‖vectorHessian f x‖≤Mf)
    (hg1 : ∀x,‖fderiv ℝ g x‖≤Pg) (hg2 : ∀x,‖vectorHessian g x‖≤Qg)
    (hval : ∀x,|f x|≤C0+C1*‖x‖) :
    (pathHeat_heatDatum_of_bounded_finite_jets f g hf hg B Sf Mf Pg Qg C0 C1
      hg0 hf1 hf2 hg1 hg2 hval).growthBound=pathHeatFiniteGrowthBound B Sf Mf Pg Qg C0 := rfl

theorem pathHeat_finiteDatum_rate
    (f g : Field n→ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (B Sf Mf Pg Qg C0 C1 : ℝ≥0)
    (hg0 : ∀x,‖g x‖≤B) (hf1 : ∀x,‖fderiv ℝ f x‖≤Sf)
    (hf2 : ∀x,‖vectorHessian f x‖≤Mf)
    (hg1 : ∀x,‖fderiv ℝ g x‖≤Pg) (hg2 : ∀x,‖vectorHessian g x‖≤Qg)
    (hval : ∀x,|f x|≤C0+C1*‖x‖) :
    (pathHeat_heatDatum_of_bounded_finite_jets f g hf hg B Sf Mf Pg Qg C0 C1
      hg0 hf1 hf2 hg1 hg2 hval).rate=C1 := rfl

theorem pathHeat_finite_exponential_bounds
    (f g : Field n→ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (B Sf Mf Pg Qg C0 C1 : ℝ≥0)
    (hg0 : ∀x,‖g x‖≤B) (hf1 : ∀x,‖fderiv ℝ f x‖≤Sf)
    (hf2 : ∀x,‖vectorHessian f x‖≤Mf)
    (hg1 : ∀x,‖fderiv ℝ g x‖≤Pg) (hg2 : ∀x,‖vectorHessian g x‖≤Qg)
    (hval : ∀x,|f x|≤C0+C1*‖x‖) (x : Field n) :
    ‖Real.exp (f x)*g x‖≤pathHeatFiniteGrowthBound B Sf Mf Pg Qg C0*Real.exp (C1*‖x‖) ∧
    ‖fderiv ℝ (fun y=>Real.exp (f y)*g y) x‖≤
      pathHeatFiniteGrowthBound B Sf Mf Pg Qg C0*Real.exp (C1*‖x‖) ∧
    ‖vectorHessian (fun y=>Real.exp (f y)*g y) x‖≤
      pathHeatFiniteGrowthBound B Sf Mf Pg Qg C0*Real.exp (C1*‖x‖) := by
  let d := pathHeat_heatDatum_of_bounded_finite_jets f g hf hg B Sf Mf Pg Qg C0 C1
    hg0 hf1 hf2 hg1 hg2 hval
  have hv := d.value_bound x
  have h1 := d.first_bound x
  have h2 := d.second_bound x
  have hdG : d.growthBound=pathHeatFiniteGrowthBound B Sf Mf Pg Qg C0 :=
    pathHeat_finiteDatum_growthBound f g hf hg B Sf Mf Pg Qg C0 C1 hg0 hf1 hf2 hg1 hg2 hval
  have hdR : d.rate=C1 :=
    pathHeat_finiteDatum_rate f g hf hg B Sf Mf Pg Qg C0 C1 hg0 hf1 hf2 hg1 hg2 hval
  rw [hdG,hdR] at hv h1 h2
  exact ⟨hv,h1,h2⟩

end HexagonPaper
