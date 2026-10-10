module
public import QuantitativePaper.UniformScalarCutoff

@[expose] public section

/-! One derivative of genuine early-strip scalar smoothing. Fixed-temperature
jet bounds establish the cutoff norm; the final bound contains only the
coefficient bound and the already uniform lower jets. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 3500000

theorem scalarEnergy_cut_source_bound (β : ℝ) (hβ : 0≤β) (μ : ParisiMeasure)
    (j : ℕ) (hj : j∈Finset.Icc 1 4) (b : ℝ) (hb : b∈Icc (0:ℝ) 1)
    (ell : ℝ) (hell : 0≤ell) (q s x C L : ℝ)
    (hq : q∈Icc (0:ℝ) b) (hs : s∈Ioc q b) (hC : 0≤C) (hL : 0≤L)
    (hcoeff : β*parisiCDF μ s≤L)
    (hlower : ∀i<j,∀y,‖scalarEnergySpatialJet β μ i (s,y)‖≤C) :
    ‖Real.exp (ell*q)*(b-q)*scalarEnergyJetSource β μ j q x s‖≤
      (2*L*gaussianAbsMoment*‖scalarEnergyWeightedCutJet β μ j b hb ell hell‖)*
        (parisiDecayWeight ell q s*(Real.sqrt (s-q))⁻¹)+
      (14*L*gaussianAbsMoment*C^2*Real.exp ell)*(Real.sqrt (s-q))⁻¹+
      32*L*gaussianAbsMoment^2*C^2*Real.exp ell := by
  have htop:=scalarEnergy_cut_square_heat_bound β μ j hj b hb ell hell q s x C hq
    ⟨hs.1.le,hs.2⟩ hC hlower
  have hnear:=scalarEnergy_cut_near_heat_bound β μ j hj b hb ell hell q s x C hq hs hC hlower
  have hsplit : Real.exp (ell*q)*(b-q)*
      ‖heatGradient (s-q) (fun y=>scalarEnergySquareJet β μ j (s,y)) x‖=
      Real.exp (ell*q)*(b-s)*‖heatGradient (s-q) (fun y=>scalarEnergySquareJet β μ j (s,y)) x‖+
      Real.exp (ell*q)*(s-q)*‖heatGradient (s-q) (fun y=>scalarEnergySquareJet β μ j (s,y)) x‖ := by ring
  have hbound:=add_le_add htop hnear
  rw [←hsplit] at hbound
  have hp : 0≤β*parisiCDF μ s := mul_nonneg hβ (parisiCDF_nonneg μ s)
  unfold scalarEnergyJetSource
  rw [norm_mul,norm_mul,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (sub_nonneg.mpr hq.2),Real.norm_of_nonneg hp]
  -- The preceding product comparison applies to the whole positive cutoff.
  have hn' := mul_le_mul_of_nonneg_left hbound hL
  have hc := mul_le_mul_of_nonneg_right hcoeff
    (show 0≤Real.exp (ell*q)*(b-q)*‖heatGradient (s-q)
      (fun y=>scalarEnergySquareJet β μ j (s,y)) x‖ from
        mul_nonneg (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hq.2)) (norm_nonneg _))
  convert (hc.trans hn') using 1 <;> ring

theorem scalarEnergy_cut_source_integral_bound (β : ℝ) (hβ : 0≤β) (μ : ParisiMeasure)
    (j : ℕ) (hj : j∈Finset.Icc 1 4) (b : ℝ) (hb : b∈Icc (0:ℝ) 1)
    (ell : ℝ) (hell : 0<ell) (q x C L : ℝ)
    (hq : q∈Icc (0:ℝ) b) (hC : 0≤C) (hL : 0≤L)
    (hcoeff : ∀s∈Icc (0:ℝ) b,β*parisiCDF μ s≤L)
    (hlower : ∀i<j,∀s∈Icc (0:ℝ) b,∀y,‖scalarEnergySpatialJet β μ i (s,y)‖≤C) :
    Real.exp (ell*q)*(b-q)*‖∫s in q..b,scalarEnergyJetSource β μ j q x s‖≤
      6*L*gaussianAbsMoment*Real.sqrt ell⁻¹*‖scalarEnergyWeightedCutJet β μ j b hb ell hell.le‖+
      28*L*gaussianAbsMoment*C^2*Real.exp ell+
      32*L*gaussianAbsMoment^2*C^2*Real.exp ell := by
  let N:=‖scalarEnergyWeightedCutJet β μ j b hb ell hell.le‖
  let a:=2*L*gaussianAbsMoment*N
  let d:=14*L*gaussianAbsMoment*C^2*Real.exp ell
  let e:=32*L*gaussianAbsMoment^2*C^2*Real.exp ell
  have hgauss:=gaussianAbsMoment_nonneg
  have ha : 0≤a := by dsimp [a,N];positivity
  have hd : 0≤d := by dsimp [d];positivity
  have he : 0≤e := by dsimp [e];positivity
  have hiK:=intervalIntegrable_bdd_mul_inv_sqrt_sub (parisiDecayWeight ell q)
    (show Measurable (parisiDecayWeight ell q) by unfold parisiDecayWeight;fun_prop)
    (parisiDecayWeight_nonneg ell q) (parisiDecayWeight_le_one ell hell.le q) q b hq.2
  have hiI:=intervalIntegrable_inv_sqrt_sub q b hq.2
  have hn:=intervalIntegral.norm_integral_le_of_norm_le hq.2
    (.of_forall fun s hs=>scalarEnergy_cut_source_bound β hβ μ j hj b hb ell hell.le
      q s x C L hq hs hC hL (hcoeff s ⟨hq.1.trans hs.1.le,hs.2⟩)
      (fun i hi y=>hlower i hi s ⟨hq.1.trans hs.1.le,hs.2⟩ y))
    (((hiK.const_mul a).add (hiI.const_mul d)).add intervalIntegrable_const)
  rw [intervalIntegral.integral_const_mul,norm_mul,norm_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (sub_nonneg.mpr hq.2)] at hn
  change _≤(∫s in q..b,a*(parisiDecayWeight ell q s*(Real.sqrt (s-q))⁻¹)+
    d*(Real.sqrt (s-q))⁻¹+e) at hn
  rw [intervalIntegral.integral_add ((hiK.const_mul a).add (hiI.const_mul d)) intervalIntegrable_const,
    intervalIntegral.integral_add (hiK.const_mul a) (hiI.const_mul d)] at hn
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    integral_inv_sqrt_sub q b hq.2,intervalIntegral.integral_const] at hn
  have hk:=integral_parisiDecayWeight_inv_sqrt_le ell hell q b hq.2
  have hroot : Real.sqrt (b-q)≤1 := Real.sqrt_le_one.mpr (by linarith [hq.1,hb.2])
  have hlen : b-q≤1 := by linarith [hq.1,hb.2]
  have ht1:=mul_le_mul_of_nonneg_left hk ha
  have ht2:=mul_le_mul_of_nonneg_left hroot (show 0≤2*d by positivity)
  have ht3:=mul_le_mul_of_nonneg_left hlen he
  simp only [smul_eq_mul] at hn
  change _≤a*(_)+d*(2*Real.sqrt (b-q))+(b-q)*e at hn
  dsimp only [a,d,e,N] at hn ht1 ht2 ht3
  nlinarith

/-- An explicit cutoff bound independent of every terminal derivative. -/
def scalarSmoothingStepConstant (ell C L : ℝ) : ℝ :=
  Real.exp ell*(gaussianAbsMoment*C+14*L*gaussianAbsMoment*C^2+
    16*L*gaussianAbsMoment^2*C^2)

theorem scalarEnergyWeightedCutJet_norm_bound (β : ℝ) (hβ : 0<β) (μ : ParisiMeasure)
    (j : ℕ) (hj : j∈Finset.Icc 1 4) (b : ℝ) (hb : b∈Icc (0:ℝ) 1)
    (ell : ℝ) (hell : 0<ell) (C L : ℝ) (hC : 0≤C) (hL : 0≤L)
    (hsmall : 3*L*gaussianAbsMoment*Real.sqrt ell⁻¹≤1/2)
    (hcoeff : ∀s∈Icc (0:ℝ) b,β*parisiCDF μ s≤L)
    (hlower : ∀i<j,∀s∈Icc (0:ℝ) b,∀y,‖scalarEnergySpatialJet β μ i (s,y)‖≤C) :
    ‖scalarEnergyWeightedCutJet β μ j b hb ell hell.le‖≤
      2*scalarSmoothingStepConstant ell C L := by
  let W:=scalarEnergyWeightedCutJet β μ j b hb ell hell.le
  let N:=‖W‖
  have hN : 0≤N := norm_nonneg _
  have hA : 0≤ scalarSmoothingStepConstant ell C L := by
    unfold scalarSmoothingStepConstant
    have := gaussianAbsMoment_nonneg
    positivity
  have hpoint (p : Icc (0:ℝ) b×ℝ) :
      ‖W p‖≤ scalarSmoothingStepConstant ell C L+
        (3*L*gaussianAbsMoment*Real.sqrt ell⁻¹)*N := by
    have ht:=scalarEnergy_cut_terminal_heat_bound β μ j (Finset.mem_Icc.mp hj).1 b hb
      ell hell.le p.1 p.2 C p.1.property hC
      (fun y=>hlower (j-1) (by have hj1:1≤j:=(Finset.mem_Icc.mp hj).1;omega) b ⟨hb.1,le_rfl⟩ y)
    have hi:=scalarEnergy_cut_source_integral_bound β hβ.le μ j hj b hb ell hell
      p.1 p.2 C L p.1.property hC hL hcoeff hlower
    have hm:=scalarEnergySpatialJet_mild_all β hβ μ j b p.1 p.2 hb p.1.property
    change ‖scalarEnergyWeightedCutJet β μ j b hb ell hell.le p‖≤_
    rw [scalarEnergyWeightedCutJet_apply,norm_mul,norm_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (sub_nonneg.mpr p.1.property.2),hm]
    have hn:=norm_add_le
      (heatSemigroup (b-p.1) (fun y=>scalarEnergySpatialJet β μ j (b,y)) p.2)
      ((1/2:ℝ)*(∫s in (p.1:ℝ)..b,scalarEnergyJetSource β μ j p.1 p.2 s))
    rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)] at hn
    have hc : 0≤Real.exp (ell*(p.1:ℝ))*(b-p.1) :=
      mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr p.1.property.2)
    have hn' := mul_le_mul_of_nonneg_left hn hc
    unfold scalarSmoothingStepConstant
    change _≤_ at ht hi
    dsimp only [N,W]
    nlinarith
  have hbnd:= (BoundedContinuousFunction.norm_le
    (add_nonneg hA (by have:=gaussianAbsMoment_nonneg;positivity))).2 hpoint
  change N≤_ at hbnd
  have hs:=mul_le_mul_of_nonneg_right hsmall hN
  linarith

end QuantitativePaper
