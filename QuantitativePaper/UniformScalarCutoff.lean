module
public import QuantitativePaper.UniformScalarJetAlgebra
public import QuantitativePaper.UniformScalarVolterra

@[expose] public section

/-! A time cutoff removes the terminal derivative bound from the actual
scalar mild equation. Its weighted norm will absorb the sole highest jet. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 2300000

def scalarEnergyWeightedCutJet (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (b : ℝ) (hb : b∈Icc (0:ℝ) 1) (ell : ℝ) (hell : 0≤ell) :
    (Icc (0:ℝ) b×ℝ) →ᵇ ℝ := by
  let M := Classical.choose (scalarEnergySpatialJet_bounded β μ j)
  have hM := (Classical.choose_spec (scalarEnergySpatialJet_bounded β μ j)).2
  exact BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p=>Real.exp (ell*p.1)*(b-p.1)*scalarEnergySpatialJet β μ j (p.1,p.2))
    ((show Continuous (fun p : Icc (0:ℝ) b×ℝ=>Real.exp (ell*p.1)*(b-p.1)) by
      fun_prop).mul ((continuous_scalarEnergySpatialJet β μ j).comp (by fun_prop)))
    (Real.exp ell*M) (fun p=>by
      have hp := p.1.property
      have he : Real.exp (ell*(p.1:ℝ))≤Real.exp ell :=
        Real.exp_le_exp.mpr (by nlinarith [hp.2,hb.2])
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (sub_nonneg.mpr hp.2)]
      have hc : Real.exp (ell*(p.1:ℝ))*(b-p.1)≤Real.exp ell := by
        have hh:=mul_le_mul he (show b-(p.1:ℝ)≤1 by linarith [hp.1,hb.2])
          (sub_nonneg.mpr hp.2) (Real.exp_pos ell).le
        simpa only [mul_one] using hh
      exact mul_le_mul hc (hM _) (norm_nonneg _) (Real.exp_pos ell).le)

@[simp] theorem scalarEnergyWeightedCutJet_apply (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (b : ℝ) (hb : b∈Icc (0:ℝ) 1) (ell : ℝ) (hell : 0≤ell)
    (p : Icc (0:ℝ) b×ℝ) :
    scalarEnergyWeightedCutJet β μ j b hb ell hell p=
      Real.exp (ell*p.1)*(b-p.1)*scalarEnergySpatialJet β μ j (p.1,p.2) := by
  rfl

theorem scalarEnergyWeightedCutJet_slice_bound (β : ℝ) (μ : ParisiMeasure) (j : ℕ)
    (b : ℝ) (hb : b∈Icc (0:ℝ) 1) (ell : ℝ) (hell : 0≤ell)
    (q s y : ℝ) (hs : s ∈ Icc (0 : ℝ) b) (hqs : q ≤ s) :
    Real.exp (ell*q)*(b-s)*‖scalarEnergySpatialJet β μ j (s,y)‖≤
      ‖scalarEnergyWeightedCutJet β μ j b hb ell hell‖*parisiDecayWeight ell q s := by
  have hh := (scalarEnergyWeightedCutJet β μ j b hb ell hell).norm_coe_le_norm (⟨s,hs⟩,y)
  rw [scalarEnergyWeightedCutJet_apply,norm_mul,norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (sub_nonneg.mpr hs.2)] at hh
  have hp:=mul_le_mul_of_nonneg_left hh (Real.exp_pos (-ell*(s-q))).le
  rw [←mul_assoc,←mul_assoc,←Real.exp_add] at hp
  have he : -ell*(s-q)+ell*s=ell*q := by ring
  rw [he] at hp
  simpa only [parisiDecayWeight,max_eq_left (sub_nonneg.mpr hqs),mul_comm,mul_left_comm] using hp

theorem scalar_heatGradient_const_mul (v c : ℝ) (f : ℝ→ℝ) (x : ℝ) :
    heatGradient v (fun y=>c*f y) x=c*heatGradient v f x := by
  unfold heatGradient gaussianExpectation
  simp_rw [show ∀z:ℝ,z*(c*f (x+Real.sqrt v*z))=c*(z*f (x+Real.sqrt v*z)) by intro z;ring]
  rw [integral_const_mul]
  ring

theorem scalarEnergy_cut_square_heat_bound (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (hj : j∈Finset.Icc 1 4) (b : ℝ) (hb : b∈Icc (0:ℝ) 1)
    (ell : ℝ) (hell : 0≤ell) (q s x C : ℝ)
    (hq : q∈Icc (0:ℝ) b) (hs : s∈Icc q b) (hC : 0≤C)
    (hlower : ∀i<j,∀y,‖scalarEnergySpatialJet β μ i (s,y)‖≤C) :
    Real.exp (ell*q)*(b-s)*
      ‖heatGradient (s-q) (fun y=>scalarEnergySquareJet β μ j (s,y)) x‖≤
      (Real.sqrt (s-q))⁻¹*gaussianAbsMoment*
        (2*‖scalarEnergyWeightedCutJet β μ j b hb ell hell‖*parisiDecayWeight ell q s+
          14*C^2*Real.exp ell) := by
  let c:=Real.exp (ell*q)*(b-s)
  have hc : 0≤c:=mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hs.2)
  have he : Real.exp (ell*q)≤Real.exp ell :=
    Real.exp_le_exp.mpr (by nlinarith [hq.2,hb.2])
  have hcb : c≤Real.exp ell := by
    have hh:=mul_le_mul he (show b-s≤1 by linarith [hq.1,hs.1,hb.2])
      (sub_nonneg.mpr hs.2) (Real.exp_pos ell).le
    simpa only [mul_one,c] using hh
  have hf (y : ℝ) : ‖c*scalarEnergySquareJet β μ j (s,y)‖≤
      2*‖scalarEnergyWeightedCutJet β μ j b hb ell hell‖*parisiDecayWeight ell q s+
        14*C^2*Real.exp ell := by
    have hr:=scalarEnergySquareJet_remainder_bound β μ j hj s y C
      ⟨hq.1.trans hs.1,hs.2.trans hb.2⟩ hC (fun i hi=>hlower i hi y)
    have hp : ‖2*scalarEnergySpatialJet β μ 0 (s,y)*scalarEnergySpatialJet β μ j (s,y)‖≤
        2*‖scalarEnergySpatialJet β μ j (s,y)‖ := by
      rw [norm_mul,norm_mul]
      norm_num only [Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2), Real.norm_of_nonneg (by norm_num : (0:ℝ)≤6), Real.norm_of_nonneg (by norm_num : (0:ℝ)≤8)]
      nlinarith [mul_le_mul_of_nonneg_right (norm_scalarEnergySpatialJet_zero_le_one β μ (s,y))
        (norm_nonneg (scalarEnergySpatialJet β μ j (s,y)))]
    have hnorm : ‖scalarEnergySquareJet β μ j (s,y)‖≤
        2*‖scalarEnergySpatialJet β μ j (s,y)‖+14*C^2 := by
      have hh:=norm_sub_le (scalarEnergySquareJet β μ j (s,y)-
        2*scalarEnergySpatialJet β μ 0 (s,y)*scalarEnergySpatialJet β μ j (s,y))
        (-(2*scalarEnergySpatialJet β μ 0 (s,y)*scalarEnergySpatialJet β μ j (s,y)))
      simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at hh
      linarith
    have ht:=scalarEnergyWeightedCutJet_slice_bound β μ j b hb ell hell q s y
      ⟨hq.1.trans hs.1,hs.2⟩ hs.1
    rw [norm_mul,Real.norm_of_nonneg hc]
    have ha:=mul_le_mul_of_nonneg_left hnorm hc
    have hcc:=mul_le_mul_of_nonneg_right hcb (show 0≤14*C^2 by positivity)
    change c*‖scalarEnergySpatialJet β μ j (s,y)‖≤_ at ht
    nlinarith
  have hh:=norm_heatGradient_le (s-q)
    (fun y=>c*scalarEnergySquareJet β μ j (s,y)) _ hf x
  rw [scalar_heatGradient_const_mul,norm_mul,Real.norm_of_nonneg hc] at hh
  exact hh

/-- The complementary time-cutoff term transfers two heat derivatives to
Gaussian kernels, using only already bounded lower spatial jets. -/
theorem scalarEnergy_cut_near_heat_bound (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (hj : j∈Finset.Icc 1 4) (b : ℝ) (hb : b∈Icc (0:ℝ) 1)
    (ell : ℝ) (hell : 0≤ell) (q s x C : ℝ)
    (hq : q∈Icc (0:ℝ) b) (hs : s∈Ioc q b) (hC : 0≤C)
    (hlower : ∀i<j,∀y,‖scalarEnergySpatialJet β μ i (s,y)‖≤C) :
    Real.exp (ell*q)*(s-q)*
      ‖heatGradient (s-q) (fun y=>scalarEnergySquareJet β μ j (s,y)) x‖≤
        32*gaussianAbsMoment^2*C^2*Real.exp ell := by
  have hj1 := (Finset.mem_Icc.mp hj).1
  have hj4 := (Finset.mem_Icc.mp hj).2
  have hjprev : j-1+1=j := by omega
  obtain ⟨K,hK0,hK⟩ := scalarEnergySquareJet_bounded β μ j
  have hs0 : s∈Icc (0:ℝ) 1 := ⟨hq.1.trans hs.1.le,hs.2.trans hb.2⟩
  have hbound (y : ℝ) : ‖scalarEnergySquareJet β μ (j-1) (s,y)‖≤16*C^2 :=
    scalarEnergySquareJet_norm_bound β μ (j-1) (by omega) s y C hs0 hC
      (fun i hi=>hlower i (by omega) y)
  have hD : ∀y,HasDerivAt (fun z=>scalarEnergySquareJet β μ (j-1) (s,z))
      (scalarEnergySquareJet β μ j (s,y)) y := by
    simpa only [hjprev] using hasDerivAt_scalarEnergySquareJet β μ (j-1) s
  have hh := scalar_heat_second_derivative_bound (s-q) (sub_pos.mpr hs.1)
    (fun y=>scalarEnergySquareJet β μ (j-1) (s,y))
    (fun y=>scalarEnergySquareJet β μ j (s,y)) (16*C^2) K
    ((continuous_scalarEnergySquareJet β μ (j-1)).comp (by fun_prop))
    ((continuous_scalarEnergySquareJet β μ j).comp (by fun_prop)) hD hbound
    (fun y=>hK (s,y)) x
  have he : Real.exp (ell*q)≤Real.exp ell :=
    Real.exp_le_exp.mpr (by nlinarith [hq.2,hb.2])
  have hcancel := mul_le_mul_of_nonneg_left hh (sub_pos.mpr hs.1).le
  have hv : s-q≠0 := (sub_pos.mpr hs.1).ne'
  have heq : (s-q)*(2*gaussianAbsMoment^2*(16*C^2)/(s-q))=
      32*gaussianAbsMoment^2*C^2 := by field_simp;ring
  rw [heq] at hcancel
  have hh' := mul_le_mul_of_nonneg_left hcancel (Real.exp_pos (ell*q)).le
  have hn : 0≤32*gaussianAbsMoment^2*C^2 := by positivity
  simpa only [mul_assoc] using hh'.trans ((mul_le_mul_of_nonneg_right he hn).trans_eq (by ring))

/-- The terminal heat term requires only the preceding jet. -/
theorem scalarEnergy_cut_terminal_heat_bound (β : ℝ) (μ : ParisiMeasure)
    (j : ℕ) (hj : 1≤j) (b : ℝ) (hb : b∈Icc (0:ℝ) 1)
    (ell : ℝ) (hell : 0≤ell) (q x C : ℝ)
    (hq : q∈Icc (0:ℝ) b) (hC : 0≤C)
    (hlower : ∀y,‖scalarEnergySpatialJet β μ (j-1) (b,y)‖≤C) :
    Real.exp (ell*q)*(b-q)*
      ‖heatSemigroup (b-q) (fun y=>scalarEnergySpatialJet β μ j (b,y)) x‖≤
        Real.exp ell*gaussianAbsMoment*C := by
  by_cases hqb : q=b
  · subst q
    simp only [sub_self,mul_zero,zero_mul]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le gaussianAbsMoment_nonneg) hC
  have hv : 0<b-q := sub_pos.mpr (lt_of_le_of_ne hq.2 hqb)
  have hjprev : j-1+1=j := by omega
  obtain ⟨K,hK0,hK⟩ := scalarEnergySpatialJet_bounded β μ j
  have hD : ∀y,HasDerivAt (fun z=>scalarEnergySpatialJet β μ (j-1) (b,z))
      (scalarEnergySpatialJet β μ j (b,y)) y := by
    intro y
    simpa only [hjprev] using hasDerivAt_scalarEnergySpatialJet β μ (j-1) b y hb
  rw [scalar_heat_derivative_eq (b-q) hv
    (fun y=>scalarEnergySpatialJet β μ (j-1) (b,y))
    (fun y=>scalarEnergySpatialJet β μ j (b,y)) C K
    ((continuous_scalarEnergySpatialJet β μ (j-1)).comp (by fun_prop))
    ((continuous_scalarEnergySpatialJet β μ j).comp (by fun_prop)) hD hlower (fun y=>hK (b,y)) x]
  have hh := norm_heatGradient_le (b-q)
    (fun y=>scalarEnergySpatialJet β μ (j-1) (b,y)) C hlower x
  have hc : 0≤Real.exp (ell*q)*(b-q) := by positivity
  have hroot : (b-q)*(Real.sqrt (b-q))⁻¹=Real.sqrt (b-q) := by
    have ht := Real.sq_sqrt hv.le
    have hne := (Real.sqrt_pos.mpr hv).ne'
    field_simp
    nlinarith [ht]
  have hsqrt : Real.sqrt (b-q)≤1 := (Real.sqrt_le_one).mpr (by linarith [hq.1,hb.2])
  have he : Real.exp (ell*q)≤Real.exp ell :=
    Real.exp_le_exp.mpr (by nlinarith [hq.2,hb.2])
  calc
    _≤Real.exp (ell*q)*(b-q)*((Real.sqrt (b-q))⁻¹*gaussianAbsMoment*C) :=
      mul_le_mul_of_nonneg_left hh hc
    _=Real.exp (ell*q)*Real.sqrt (b-q)*gaussianAbsMoment*C := by
      calc
        _=Real.exp (ell*q)*((b-q)*(Real.sqrt (b-q))⁻¹)*gaussianAbsMoment*C := by ring
        _=_ := by rw [hroot]
    _≤Real.exp ell*gaussianAbsMoment*C := by
      have hh:=mul_le_mul he hsqrt (Real.sqrt_nonneg _) (Real.exp_pos _).le
      have hn : 0≤gaussianAbsMoment*C := mul_nonneg gaussianAbsMoment_nonneg hC
      simpa only [mul_one,mul_assoc] using mul_le_mul_of_nonneg_right hh hn

end QuantitativePaper
