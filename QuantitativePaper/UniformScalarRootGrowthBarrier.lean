module
public import QuantitativePaper.UniformScalarRootGrowthShape
public import QuantitativePaper.UniformScalarRootGrowthTimeClosed
public import QuantitativePaper.UniformBoundaryStrictness

@[expose] public section

/-! The paper's quantitative boundary barrier applied to the actual scalar
Parisi third derivative, with all time, spatial and PDE hypotheses proved. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1800000

theorem scalarEnergy_third_uniform_boundary (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (g : ℝ→ℝ) (hg : Continuous g)
    (τ ell ε C : ℝ) (hτ : τ∈Ioc (0:ℝ) 1) (hell : ell∈Ioc (0:ℝ) 4)
    (hε : 0<ε) (he : EqOn (parisiCDF μ) g (Icc 0 τ))
    (hg32 : ∀q∈Icc (0:ℝ) τ,β*parisiCDF μ q≤32)
    (hH : ∀q∈Icc (0:ℝ) τ,∀x,scalarEnergySpatialJet β μ 1 (q,x)≤C)
    (hright : ∀q∈Icc (0:ℝ) τ,ε≤-scalarEnergySpatialJet β μ 2 (q,ell)) :
    ∀q∈Icc (0:ℝ) τ,∀x∈Icc (0:ℝ) ell,
      (1/4:ℝ)*uniformBoundaryAlpha τ*ε*Real.exp (-uniformBoundaryAlpha τ)*
        (x-4*q/τ)≤-scalarEnergySpatialJet β μ 2 (q,x) := by
  let W : ℝ×ℝ→ℝ:=fun p=>-scalarEnergySpatialJet β μ 2 (τ-p.1,p.2)
  let W1 : ℝ×ℝ→ℝ:=fun p=>-scalarEnergySpatialJet β μ 3 (τ-p.1,p.2)
  let W2 : ℝ×ℝ→ℝ:=fun p=>-scalarEnergySpatialJet β μ 4 (τ-p.1,p.2)
  let Wt : ℝ×ℝ→ℝ:=fun p=>β^2*QuantitativeFollowup.continuousProfileTimeField β μ g 3 (τ-p.1,β*p.2)
  let B : ℝ×ℝ→ℝ:=fun p=>(β*parisiCDF μ (τ-p.1))*scalarEnergySpatialJet β μ 0 (τ-p.1,p.2)
  let R : ℝ×ℝ→ℝ:=fun p=>3*(β*parisiCDF μ (τ-p.1))*scalarEnergySpatialJet β μ 1 (τ-p.1,p.2)
  have htime (r : ℝ) (hr : r∈Icc (0:ℝ) τ) : τ-r∈Icc (0:ℝ) τ:=by constructor <;> linarith [hr.1,hr.2]
  have hphys (r : ℝ) (hr : r∈Icc (0:ℝ) τ) : τ-r∈Icc (0:ℝ) 1:=⟨(htime r hr).1,(htime r hr).2.trans hτ.2⟩
  have hc : Continuous W:=by
    exact ((continuous_scalarEnergySpatialJet β μ 2).comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd)).neg
  have hnon (p : ℝ×ℝ) (hp : p∈Icc 0 τ×ˢIcc 0 ell) : 0≤W p:=
    neg_nonneg.mpr (scalarEnergyJet_two_nonpos β hβ μ (τ-p.1) p.2 (hphys p.1 hp.1) hp.2.1)
  have ht (r : ℝ) (hr : r∈Ioc (0:ℝ) τ) (x : ℝ) (_hx : x∈Ioo (0:ℝ) ell) :
      HasDerivWithinAt (fun s=>W (s,x)) (Wt (r,x)) (Icc 0 τ) r:=by
    have hd:=scalarEnergyJet_two_closed_profile_time β hβ.ne' μ g hg τ hτ
      (he.mono Ioo_subset_Icc_self) (τ-r) x (htime r ⟨hr.1.le,hr.2⟩)
    have hi:=((hasDerivAt_id r).const_sub τ).hasDerivWithinAt (s:=Icc (0:ℝ) τ)
    have hh:=(hd.comp r hi (fun s hs=>htime s hs)).neg
    convert! hh using 1 <;>
      simp only [W,Wt,Function.comp_def,Pi.neg_apply,neg_mul,neg_neg,mul_one,mul_neg,neg_one_mul]
  have h1 (r : ℝ) (hr : r∈Ioc (0:ℝ) τ) (x : ℝ) (_hx : x∈Ioo (0:ℝ) ell) :
      HasDerivAt (fun y=>W (r,y)) (W1 (r,x)) x:=
    (hasDerivAt_scalarEnergySpatialJet β μ 2 (τ-r) x (hphys r ⟨hr.1.le,hr.2⟩)).neg
  have h2 (r : ℝ) (hr : r∈Ioc (0:ℝ) τ) (x : ℝ) (_hx : x∈Ioo (0:ℝ) ell) :
      HasDerivAt (fun y=>W1 (r,y)) (W2 (r,x)) x:=
    (hasDerivAt_scalarEnergySpatialJet β μ 3 (τ-r) x (hphys r ⟨hr.1.le,hr.2⟩)).neg
  have hBn (r : ℝ) (hr : r∈Ioc (0:ℝ) τ) (x : ℝ) (hx : x∈Ioo (0:ℝ) ell) : 0≤B (r,x):=by
    have hgrad:=FRSB.backwardB_nonneg β hβ.ne' μ (τ-r) (β*x)
      (hphys r ⟨hr.1.le,hr.2⟩) (mul_nonneg hβ.le hx.1.le)
    rw [FRSB.backwardB_eq_gradient β μ (τ-r) (β*x) (hphys r ⟨hr.1.le,hr.2⟩)] at hgrad
    simpa only [B,scalarEnergySpatialJet_zero] using
      mul_nonneg (mul_nonneg hβ.le (parisiCDF_nonneg μ (τ-r))) hgrad
  have hRn (r : ℝ) (hr : r∈Ioc (0:ℝ) τ) (x : ℝ) (_hx : x∈Ioo (0:ℝ) ell) :
      0≤R (r,x) ∧ R (r,x)≤96*C:=by
    have hq:=htime r ⟨hr.1.le,hr.2⟩
    have hh : 0 ≤ scalarEnergySpatialJet β μ 1 (τ-r,x):=by
      rw [scalarEnergySpatialJet_one]
      exact mul_nonneg hβ.le (parisiHessian_pos_all β μ (τ-r) (β*x) (hphys r ⟨hr.1.le,hr.2⟩)).le
    have hc0 : 0≤C:=hh.trans (hH _ hq x)
    have hd : 0≤β*parisiCDF μ (τ-r):=mul_nonneg hβ.le (parisiCDF_nonneg μ _)
    have hm:=mul_le_mul (hg32 _ hq) (hH _ hq x) hh (by norm_num : (0:ℝ)≤32)
    dsimp only [R]
    exact ⟨by positivity,by nlinarith⟩
  have hPDE (r : ℝ) (hr : r∈Ioc (0:ℝ) τ) (x : ℝ) (_hx : x∈Ioo (0:ℝ) ell) :
      Wt (r,x)=(1/2:ℝ)*W2 (r,x)+B (r,x)*W1 (r,x)+R (r,x)*W (r,x):=by
    have hq:=htime r ⟨hr.1.le,hr.2⟩
    have hid : QuantitativeFollowup.continuousProfileTimeField β μ g 3 (τ-r,β*x)=
        parisiTimeField β μ 3 (τ-r,β*x):=by
      unfold QuantitativeFollowup.continuousProfileTimeField parisiTimeField
      rw [he hq]
    dsimp only [Wt]
    rw [hid,scalarEnergyJet_two_time_source β μ (τ-r) x (hphys r ⟨hr.1.le,hr.2⟩)]
    dsimp only [W2,B,W1,R,W]
    ring
  have hh:=uniform_boundary_strictness τ ell ε hτ.1 hell hε W Wt W1 W2 B R (96*C)
    hc.continuousOn hnon ht h1 h2 hBn hRn hPDE (fun r hr=>hright (τ-r) (htime r hr))
  intro q hq x hx
  have h:=hh (τ-q,x) ⟨htime q hq,hx⟩
  simpa only [W,sub_sub_cancel] using h

end QuantitativePaper
