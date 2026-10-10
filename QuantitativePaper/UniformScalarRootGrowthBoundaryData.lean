module
public import QuantitativePaper.UniformScalarRootGrowthBarrier

@[expose] public section

/-! Genuine quantitative boundary data obtained from contact, spatial
smoothing and the actual time-Lipschitz estimate. -/
noncomputable section
open Set Paper
namespace QuantitativePaper
set_option maxHeartbeats 1400000

theorem exists_scalarEnergy_uniform_boundary_data (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (hmin : FRSB.IsParisiMinimizer β 0 μ)
    (qend : ℝ) (hqend : qend∈Ioo (0:ℝ) 1)
    (hsupp : FRSB.parisiSupport μ=Icc (0:ℝ) qend)
    (C τ : ℝ) (hC : 1≤C) (hτ : τ∈Ioc (0:ℝ) (1/4)) (hτend : τ<qend)
    (hg32 : ∀q∈Icc (0:ℝ) τ,β*parisiCDF μ q≤32)
    (hj : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) τ,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤C)
    (hsmall : (C/2+32*(C+3*C^2))*τ≤3/32) :
    ∃ell∈Ioo (0:ℝ) 4,3/(16*C)≤ell ∧
      ∀q∈Icc (0:ℝ) τ,∀x∈Icc (0:ℝ) ell,
        ((1/4:ℝ)*uniformBoundaryAlpha τ*(3/32)*Real.exp (-uniformBoundaryAlpha τ))*
          (x-4*q/τ)≤-scalarEnergySpatialJet β μ 2 (q,x) := by
  have hphys : τ∈Icc (0:ℝ) 1:=⟨hτ.1.le,hτ.2.trans (by norm_num)⟩
  have hcontact:=FRSB.GammaPrime_eq_one_on_support_interval β hβ.ne' μ hmin qend
    hqend.1 hqend.2.le hsupp τ ⟨hτ.1.le,hτend.le⟩
  obtain ⟨ell,hell,hlarge⟩:=exists_scalarEnergy_third_large β hβ μ τ hphys hcontact
  have hspace:=norm_image_sub_le_of_norm_deriv_le_segment'
    (a:=(0:ℝ)) (b:=ell) (f:=fun x=>scalarEnergySpatialJet β μ 2 (τ,x))
    (f':=fun x=>scalarEnergySpatialJet β μ 3 (τ,x)) (C:=C)
    (fun x _=>(hasDerivAt_scalarEnergySpatialJet β μ 2 τ x hphys).hasDerivWithinAt)
    (fun x _=>hj 3 (by decide) τ ⟨hτ.1.le,le_rfl⟩ x) ell ⟨hell.1.le,le_rfl⟩
  rw [scalarEnergyJet_two_origin β μ τ hphys,sub_zero,sub_zero] at hspace
  have hellbound : 3/(16*C)≤ell:=by
    have hh:=hlarge.trans ((neg_le_abs (scalarEnergySpatialJet β μ 2 (τ,ell))).trans_eq
      (Real.norm_eq_abs _).symm)
    apply (div_le_iff₀ (by positivity : (0:ℝ)<16*C)).mpr
    nlinarith
  have hright (q : ℝ) (hq : q∈Icc (0:ℝ) τ) : 3/32≤-scalarEnergySpatialJet β μ 2 (q,ell):=by
    have hh:=scalarEnergyJet_two_time_lipschitz β hβ μ C (by linarith) τ
      ⟨hτ.1,hphys.2⟩ hg32 hj q τ ell hq ⟨hτ.1.le,le_rfl⟩
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hq.2),neg_sub] at hh
    have hdelta:=(le_abs_self (scalarEnergySpatialJet β μ 2 (q,ell)-
      scalarEnergySpatialJet β μ 2 (τ,ell))).trans hh
    have hcw : 0≤C/2+32*(C+3*C^2):=by positivity
    have hmul:=mul_le_mul_of_nonneg_left (show τ-q≤τ by linarith [hq.1]) hcw
    nlinarith
  let g:=QuantitativeFollowup.scalarSupportCDF β μ qend hqend.1.le
  have hgc : Continuous g:=QuantitativeFollowup.continuous_scalarSupportCDF β hβ.ne' μ
    hmin qend hqend hsupp
  have he : EqOn (parisiCDF μ) g (Icc 0 τ):=by
    intro q hq
    exact (QuantitativeFollowup.scalarSupportCDF_eq_cdf β hβ.ne' μ hmin qend hqend hsupp
      q ⟨hq.1,hq.2.trans_lt hτend⟩).symm
  have hb:=scalarEnergy_third_uniform_boundary β hβ μ g hgc τ ell (3/32) C
    ⟨hτ.1,hphys.2⟩ ⟨hell.1,hell.2.le⟩ (by norm_num) he hg32
    (fun q hq x=>(le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hj 1 (by decide) q hq x)) hright
  exact ⟨ell,hell,hellbound,hb⟩

end QuantitativePaper
