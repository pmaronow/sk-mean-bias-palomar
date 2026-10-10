module
public import QuantitativePaper.UniformScalarSmoothingStep
public import QuantitativePaper.ScalarEnergySublevel

@[expose] public section

/-! Actual energy-coordinate spatial jets have temperature-independent
bounds on the early quarter strip for every scalar energy sublevel ≤2. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 3500000

def scalarSmoothingWeight (L : ℝ) : ℝ := (6*L*gaussianAbsMoment+1)^2

def scalarSmoothingNext (C L delta : ℝ) : ℝ :=
  max 1 (2*scalarSmoothingStepConstant (scalarSmoothingWeight L) C L/delta)

theorem scalarSmoothingWeight_pos (L : ℝ) (hL : 0≤L) :
    0<scalarSmoothingWeight L := by
  have := gaussianAbsMoment_nonneg
  unfold scalarSmoothingWeight
  positivity

theorem scalarSmoothingWeight_small (L : ℝ) (hL : 0≤L) :
    3*L*gaussianAbsMoment*Real.sqrt (scalarSmoothingWeight L)⁻¹≤1/2 := by
  have hg:=gaussianAbsMoment_nonneg
  have hs : 0<6*L*gaussianAbsMoment+1 := by positivity
  unfold scalarSmoothingWeight
  rw [Real.sqrt_inv,Real.sqrt_sq_eq_abs,abs_of_pos hs]
  rw [←div_eq_mul_inv]
  apply (div_le_iff₀ hs).mpr
  nlinarith [mul_nonneg hL hg]

theorem scalarEnergySpatialJet_smoothing_step (β : ℝ) (hβ : 0<β) (μ : ParisiMeasure)
    (j : ℕ) (hj : j∈Finset.Icc 1 4) (b : ℝ) (hb : b∈Icc (0:ℝ) 1)
    (C L delta : ℝ) (hC : 0≤C) (hL : 0≤L) (hd : 0<delta)
    (hcoeff : ∀s∈Icc (0:ℝ) b,β*parisiCDF μ s≤L)
    (hlower : ∀i<j,∀s∈Icc (0:ℝ) b,∀y,‖scalarEnergySpatialJet β μ i (s,y)‖≤C)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) (b-delta)) :
    ‖scalarEnergySpatialJet β μ j (q,x)‖≤ scalarSmoothingNext C L delta := by
  let ell:=scalarSmoothingWeight L
  have hell : 0<ell:=scalarSmoothingWeight_pos L hL
  have hq0 : q∈Icc (0:ℝ) b := ⟨hq.1,by linarith [hq.2]⟩
  have hn:=scalarEnergyWeightedCutJet_norm_bound β hβ μ j hj b hb ell hell C L hC hL
    (scalarSmoothingWeight_small L hL) hcoeff hlower
  have hp:=(scalarEnergyWeightedCutJet β μ j b hb ell hell.le).norm_coe_le_norm (⟨q,hq0⟩,x)
  rw [scalarEnergyWeightedCutJet_apply,norm_mul,norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (sub_nonneg.mpr hq0.2)] at hp
  have he : 1≤Real.exp (ell*q) := Real.one_le_exp_iff.mpr (mul_nonneg hell.le hq.1)
  have hc : delta≤Real.exp (ell*q)*(b-q) := by
    have hh:=mul_le_mul_of_nonneg_right he (sub_nonneg.mpr hq0.2)
    nlinarith [hq.2]
  have hdj:=mul_le_mul_of_nonneg_right hc (norm_nonneg (scalarEnergySpatialJet β μ j (q,x)))
  have hh : delta*‖scalarEnergySpatialJet β μ j (q,x)‖≤
      2*scalarSmoothingStepConstant ell C L := hdj.trans (hp.trans hn)
  exact ((le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hh)).trans (le_max_right _ _)

/-- Each successive derivative is smoothed across a strip of width 1/16. -/
def scalarUniformJetConstant : ℕ→ℝ
  | 0=>1
  | n+1=>max (scalarUniformJetConstant n) (scalarSmoothingNext (scalarUniformJetConstant n) 32 (1/16))

theorem scalarUniformJetConstant_ge_one (n : ℕ) : 1≤ scalarUniformJetConstant n := by
  induction n with
  | zero=>simp [scalarUniformJetConstant]
  | succ n ih=>exact ih.trans (le_max_left _ _)

theorem scalarEnergySpatialJet_uniform_early_induction (n : ℕ) (hn : n≤4)
    (β : ℝ) (hβ : 0<β) (μ : ParisiMeasure)
    (hcoeff : ∀q∈Icc (0:ℝ) (1/2),β*parisiCDF μ q≤32) :
    ∀j≤n,∀q∈Icc (0:ℝ) (1/2-(n:ℝ)/16),∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤ scalarUniformJetConstant n := by
  induction n with
  | zero=>
    intro j hj q hq x
    have hj0 : j=0 := by omega
    subst j
    exact norm_scalarEnergySpatialJet_zero_le_one β μ (q,x)
  | succ n ih=>
    have hn4 : n≤4 := by omega
    have hn3 : n≤3 := by omega
    have hcast : ((n+1:ℕ):ℝ)=(n:ℝ)+1 := by norm_num
    intro j hj q hq x
    have hqold : q∈Icc (0:ℝ) (1/2-(n:ℝ)/16) := by
      refine ⟨hq.1,?_⟩
      rw [hcast] at hq
      linarith [hq.2]
    by_cases hjold : j≤n
    · exact (ih hn4 j hjold q hqold x).trans (le_max_left _ _)
    have hjeq : j=n+1 := by omega
    subst j
    have hb : (1/2-(n:ℝ)/16)∈Icc (0:ℝ) 1 := by
      have hnn : (0:ℝ)≤(n:ℝ) := Nat.cast_nonneg n
      have hnu : (n:ℝ)≤3 := by exact_mod_cast hn3
      constructor <;> linarith
    have hC : 0≤ scalarUniformJetConstant n := (by norm_num : (0:ℝ)≤1).trans (scalarUniformJetConstant_ge_one n)
    have hqnew : q∈Icc (0:ℝ) ((1/2-(n:ℝ)/16)-1/16) := by
      refine ⟨hq.1,?_⟩
      rw [hcast] at hq
      linarith [hq.2]
    have hh:=scalarEnergySpatialJet_smoothing_step β hβ μ (n+1) (Finset.mem_Icc.mpr ⟨by omega,hn⟩)
      (1/2-(n:ℝ)/16) hb (scalarUniformJetConstant n) 32 (1/16) hC (by norm_num) (by norm_num)
      (fun s hs=>hcoeff s ⟨hs.1,hs.2.trans (by linarith [Nat.cast_nonneg (α:=ℝ) n])⟩)
      (fun i hi s hs y=>ih hn4 i (by omega) s hs y) q x hqnew
    exact hh.trans (le_max_right _ _)

/-- Genuine universal early-strip smoothing, with no minimizer or supplied
regularity premise. The scalar energy sublevel gives the coefficient bound. -/
theorem scalarEnergySpatialJet_uniform_early :
    ∃ C≥1,∀(β:ℝ),0<β→∀(μ:ParisiMeasure),scalarParisiFunctional β μ/β≤2→
      ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) (1/4),∀x,
        ‖scalarEnergySpatialJet β μ j (q,x)‖≤C := by
  refine ⟨scalarUniformJetConstant 4,scalarUniformJetConstant_ge_one 4,?_⟩
  intro β hβ μ hcost j hj q hq x
  have hc (s : ℝ) (hs : s∈Icc (0:ℝ) (1/2)) : β*parisiCDF μ s≤32 :=
    scalarEnergy_sublevel_two_cdf_le β hβ μ hcost s hs.2
  have hh:=scalarEnergySpatialJet_uniform_early_induction 4 (by omega) β hβ μ hc
    j (Finset.mem_Icc.mp hj).2 q (by norm_num at hq ⊢;exact hq) x
  exact hh

end QuantitativePaper
