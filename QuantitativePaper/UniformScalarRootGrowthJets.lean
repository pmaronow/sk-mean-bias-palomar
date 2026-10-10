module
public import QuantitativePaper.UniformScalarJetAlgebra
public import FourPapersCommon.LocalWeakTimeLipschitz
public import QuantitativeFollowup.ScalarClippingFields
public import QuantitativeFollowup.ScalarRootStrictness

@[expose] public section

/-! Energy-coordinate time equations and uniform time bounds for the actual
third spatial derivative. The bounds use only genuine early-strip jets and
CDF mass, and include the time-zero endpoint. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000

theorem scalarEnergyJet_two_time_source (β : ℝ) (μ : ParisiMeasure)
    (q x : ℝ) (hq : q∈Icc (0:ℝ) 1) :
    β^2*parisiTimeField β μ 3 (q,β*x)=
      -(1/2:ℝ)*scalarEnergySpatialJet β μ 4 (q,x)-
      (β*parisiCDF μ q)*(scalarEnergySpatialJet β μ 0 (q,x)*
        scalarEnergySpatialJet β μ 3 (q,x)+
        3*scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 2 (q,x)) := by
  calc
    _=-(1/2:ℝ)*scalarEnergySpatialJet β μ 4 (q,x)-
        (β*parisiCDF μ q/2)*scalarEnergySquareJet β μ 3 (q,x) := by
      dsimp only [parisiTimeField,scalarEnergySpatialJet,scalarEnergySquareJet]
      ring
    _=_ := by rw [scalarEnergySquareJet_three β μ q x hq];ring

theorem scalarEnergyJet_two_time_source_bound (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (C : ℝ) (hC : 0≤C) (q x : ℝ)
    (hq : q∈Icc (0:ℝ) 1) (hg : β*parisiCDF μ q≤32)
    (hj : ∀j∈Finset.Icc 1 4,‖scalarEnergySpatialJet β μ j (q,x)‖≤C) :
    ‖β^2*parisiTimeField β μ 3 (q,β*x)‖≤C/2+32*(C+3*C^2) := by
  have h0:=norm_scalarEnergySpatialJet_zero_le_one β μ (q,x)
  have h1:=hj 1 (by decide)
  have h2:=hj 2 (by decide)
  have h3:=hj 3 (by decide)
  have h4:=hj 4 (by decide)
  have h03 : ‖scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ 3 (q,x)‖≤C := by
    rw [norm_mul]
    simpa using mul_le_mul h0 h3 (norm_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h12 : ‖scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 2 (q,x)‖≤C^2 := by
    rw [norm_mul,pow_two]
    exact mul_le_mul h1 h2 (norm_nonneg _) hC
  have hsum : ‖scalarEnergySpatialJet β μ 0 (q,x)*scalarEnergySpatialJet β μ 3 (q,x)+
      3*scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 2 (q,x)‖≤C+3*C^2 := by
    have he : 3*scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 2 (q,x)=
        3*(scalarEnergySpatialJet β μ 1 (q,x)*scalarEnergySpatialJet β μ 2 (q,x)) := by ring
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Real.norm_ofNat] at h03 h12 ⊢
    linarith
  have hgn : ‖β*parisiCDF μ q‖≤32 := by
    rw [Real.norm_of_nonneg (mul_nonneg hβ.le (parisiCDF_nonneg μ q))]
    exact hg
  rw [scalarEnergyJet_two_time_source β μ q x hq]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_neg,norm_mul]
  norm_num only [Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
  have hh:=mul_le_mul hgn hsum (norm_nonneg _) (by norm_num : (0:ℝ)≤32)
  nlinarith

theorem scalarEnergyJet_two_time_lipschitz (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (C : ℝ) (hC : 0≤C) (b : ℝ)
    (hb : b∈Ioc (0:ℝ) 1)
    (hg : ∀q∈Icc (0:ℝ) b,β*parisiCDF μ q≤32)
    (hj : ∀j∈Finset.Icc 1 4,∀q∈Icc (0:ℝ) b,∀x,
      ‖scalarEnergySpatialJet β μ j (q,x)‖≤C)
    (q r x : ℝ) (hq : q∈Icc (0:ℝ) b) (hr : r∈Icc (0:ℝ) b) :
    ‖scalarEnergySpatialJet β μ 2 (q,x)-scalarEnergySpatialJet β μ 2 (r,x)‖≤
      (C/2+32*(C+3*C^2))*‖q-r‖ := by
  let W:=C/2+32*(C+3*C^2)
  have hW : 0≤W:=by dsimp [W];positivity
  have hsq : 0<β^2:=sq_pos_of_pos hβ
  have hraw (p : ℝ×ℝ) (hp : p.1∈Icc (0:ℝ) b) :
      ‖parisiTimeField β μ 3 p‖≤W/β^2 := by
    have hh:=scalarEnergyJet_two_time_source_bound β hβ μ C hC p.1 (p.2/β)
      ⟨hp.1,hp.2.trans hb.2⟩ (hg p.1 hp) (fun j h=>hj j h p.1 hp (p.2/β))
    have he : β*(p.2/β)=p.2:=by field_simp
    rw [he,norm_mul,Real.norm_of_nonneg hsq.le] at hh
    change β^2*‖parisiTimeField β μ 3 p‖≤W at hh
    exact (le_div_iff₀ hsq).mpr (by simpa only [mul_comm] using hh)
  have hl:=FourPapersCommon.lipschitzOnWith_weakTime_section_on_strip
    (parisiSpatialField β μ 3) (parisiTimeField β μ 3)
    (continuous_parisiSpatialField β μ 3)
    (isParisiWeakTimeDerivative_spatialField β hβ.ne' μ 3)
    (measurable_parisiTimeField β μ 3) 0 b (W/β^2) le_rfl hb.2 hb.1 hraw (β*x)
  have hh:=hl.dist_le_mul q hq r hr
  rw [Real.dist_eq,Real.dist_eq,Real.coe_toNNReal _ (div_nonneg hW hsq.le)] at hh
  have hm:=mul_le_mul_of_nonneg_left hh hsq.le
  have he : β^2*(W/β^2)=W:=by field_simp
  rw [←mul_assoc,he] at hm
  simpa only [scalarEnergySpatialJet,Nat.reduceAdd,←mul_sub,norm_mul,
    Real.norm_of_nonneg hsq.le,Real.norm_eq_abs] using hm

end QuantitativePaper
