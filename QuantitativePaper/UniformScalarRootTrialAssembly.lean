module
public import QuantitativePaper.UniformScalarRootGrowthLowerFamily
public import QuantitativePaper.UniformScalarTrialFromGrowth
public import QuantitativePaper.UniformScalarRootLipschitz

@[expose] public section

/-! Complete literal uniform scalar root/trial target, with the actual
clipped probability measure and its interior energy density included.
The upper-family assembly is supporting calculus; its model-only
instantiation is the separate final numbered endpoint. -/
noncomputable section
open Set MeasureTheory Paper FRSB QuantitativeFollowup
open scoped ENNReal NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1600000

def UniformScalarRootTrialTarget (β₀ : ℝ) : Prop :=
  ∃Tstar k Cs C1 lamstar : ℝ,
    Tstar∈Ioc (0:ℝ) (1/4) ∧ 0<k ∧ 1≤Cs ∧ 1≤C1 ∧
    0<lamstar ∧ lamstar≤1 ∧ lamstar≤β₀/2 ∧ lamstar≤k*Tstar ∧
    ∀β,β₀≤β→∀μ,IsParisiMinimizer β 0 μ→
      AbsolutelyContinuousOnInterval (fun q=>β*parisiCDF μ q) 0 Tstar ∧
      (∀q∈Icc (0:ℝ) Tstar,k*q≤β*parisiCDF μ q ∧ β*parisiCDF μ q≤Cs*q) ∧
      (∀x∈Icc (0:ℝ) Tstar,∀y∈Icc (0:ℝ) Tstar,
        ‖β*parisiCDF μ y-β*parisiCDF μ x‖≤Cs*‖y-x‖) ∧
      (∀ᵐq∂volume.restrict (Icc (0:ℝ) Tstar),
        0≤deriv (fun r=>β*parisiCDF μ r) q ∧ deriv (fun r=>β*parisiCDF μ r) q≤Cs) ∧
      ∀lam∈Icc (0:ℝ) lamstar,∃hs : lam/β∈Icc (0:ℝ) 1,
        let ν:=scalarClippedTrialMeasure (lam/β) hs μ
        ν∈scalarFloor (lam/β) ∧
        (∀q∈Icc (0:ℝ) 1,β*parisiCDF ν q=max lam (β*parisiCDF μ q) ∧
          lam≤β*parisiCDF ν q ∧ β*parisiCDF ν q≤β) ∧
        (∀q∈Icc (0:ℝ) Tstar,k*q≤β*parisiCDF ν q ∧ β*parisiCDF ν q≤2) ∧
        (ENNReal.ofReal β • (parisiCDFPrimitive ν).measure).restrict (Ioo (0:ℝ) Tstar)≤
          ENNReal.ofReal Cs • volume.restrict (Ioo (0:ℝ) Tstar) ∧
        0 ≤ scalarEnergyValue β lam-scalarEnergyValue β 0 ∧
        scalarEnergyValue β lam-scalarEnergyValue β 0≤
          parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0 ∧
        parisiPDEFunctional β 0 ν/β-scalarEnergyValue β 0≤C1*lam^5

theorem uniform_scalar_root_trial_of_upper_family
    (β₀ : ℝ) (hβ₀ : 1<β₀) (Cu Cac Tu : ℝ)
    (hCu : 0<Cu) (hCac : 0<Cac) (hTu : Tu∈Ioc (0:ℝ) (1/4))
    (hupper : ∀β,β₀≤β→∀μ,IsParisiMinimizer β 0 μ→
      (∀q∈Icc (0:ℝ) Tu,β*parisiCDF μ q≤Cu*q) ∧
      LipschitzOnWith Cac.toNNReal (fun q=>β*parisiCDF μ q) (Icc (0:ℝ) Tu)) :
    UniformScalarRootTrialTarget β₀ := by
  obtain ⟨k,Tl,hk,hTl,hlower⟩:=scalar_minimizer_uniform_root_lower β₀ hβ₀
  let Cs:=max 1 (max Cu Cac)
  let T:=min Tl (min Tu (1/Cs))
  have hCs : 1≤Cs:=le_max_left _ _
  have hCspos : 0<Cs:=zero_lt_one.trans_le hCs
  have hCuCs : Cu≤Cs:=(le_max_left _ _).trans (le_max_right _ _)
  have hCacCs : Cac≤Cs:=(le_max_right _ _).trans (le_max_right _ _)
  have hTlT : T≤Tl:=min_le_left _ _
  have hTuT : T≤Tu:=(min_le_right _ _).trans (min_le_left _ _)
  have hTinv : T≤1/Cs:=(min_le_right _ _).trans (min_le_right _ _)
  have hT : T∈Ioc (0:ℝ) (1/4):=
    ⟨lt_min hTl.1 (lt_min hTu.1 (one_div_pos.mpr hCspos)),hTlT.trans hTl.2⟩
  have hTlow : ∀β,β₀≤β→∀μ,IsParisiMinimizer β 0 μ→
      ∀q∈Icc (0:ℝ) T,k*q≤β*parisiCDF μ q:=by
    intro β hβ μ hmin q hq
    exact hlower β hβ μ hmin q ⟨hq.1,hq.2.trans hTlT⟩
  obtain ⟨C1,L,hC1,hL,hL1,hLβ,hLT,hcost⟩:=
    scalar_clipped_trial_uniform_fifth_order_of_root_growth β₀ hβ₀ k T hk hT hTlow
  refine ⟨T,k,Cs,C1,L,hT,hk,hCs,hC1,hL,hL1,hLβ,hLT,?_⟩
  intro β hb μ hmin
  have hβ : 0<β:=zero_lt_one.trans (hβ₀.trans_le hb)
  have hupperμ:=hupper β hb μ hmin
  have hLip (x : ℝ) (hx:x∈Icc (0:ℝ) T) (y : ℝ) (hy:y∈Icc (0:ℝ) T) :
      ‖β*parisiCDF μ y-β*parisiCDF μ x‖≤Cs*‖y-x‖:=by
    have hh:=hupperμ.2.dist_le_mul y ⟨hy.1,hy.2.trans hTuT⟩ x ⟨hx.1,hx.2.trans hTuT⟩
    rw [Real.coe_toNNReal Cac hCac.le] at hh
    have hh' : ‖β*parisiCDF μ y-β*parisiCDF μ x‖≤Cac*‖y-x‖:=by
      simpa only [Real.dist_eq,Real.norm_eq_abs] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right hCacCs (norm_nonneg _))
  have hUp (q : ℝ) (hq:q∈Icc (0:ℝ) T) : β*parisiCDF μ q≤Cs*q:=
    (hupperμ.1 q ⟨hq.1,hq.2.trans hTuT⟩).trans (mul_le_mul_of_nonneg_right hCuCs hq.1)
  refine ⟨scalarEnergyCDF_absoluteContinuous β T Cs μ hT.1.le hCspos.le hLip,
    fun q hq=>⟨hTlow β hb μ hmin q hq,hUp q hq⟩,hLip,
    scalarEnergyCDF_ae_derivative_bound β T Cs μ hβ.le hCspos.le hLip,?_⟩
  intro lam hlam
  obtain ⟨hs,h0,htrial,hbound⟩:=hcost β hb μ hmin lam hlam
  let ν:=scalarClippedTrialMeasure (lam/β) hs μ
  have hlamβ : lam≤β:=by
    have hh:=hlam.2.trans hLβ
    linarith
  have hcdf (q : ℝ) (hq:q∈Icc (0:ℝ) 1) : β*parisiCDF ν q=max lam (β*parisiCDF μ q):=by
    dsimp only [ν]
    rw [scalarClippedTrialMeasure_cdf (lam/β) hs μ q hq,mul_max_of_nonneg _ _ hβ.le,
      mul_div_cancel₀ _ hβ.ne']
  have hTsq : Cs*T≤1:=by simpa only [mul_comm] using (le_div_iff₀ hCspos).mp hTinv
  refine ⟨hs,scalarClippedTrialMeasure_mem_floor (lam/β) hs μ,?_,?_,?_,h0,htrial,hbound⟩
  · intro q hq
    rw [hcdf q hq]
    refine ⟨rfl,le_max_left _ _,max_le hlamβ ?_⟩
    exact (mul_le_mul_of_nonneg_left (parisiCDF_le_one μ q) hβ.le).trans_eq (mul_one _)
  · intro q hq
    rw [hcdf q ⟨hq.1,hq.2.trans (hT.2.trans (by norm_num))⟩]
    refine ⟨(hTlow β hb μ hmin q hq).trans (le_max_right _ _),max_le ?_ ?_⟩
    · exact (hlam.2.trans hL1).trans (by norm_num)
    · have hγ:=(hUp q hq).trans (mul_le_mul_of_nonneg_left hq.2 hCspos.le)
      exact hγ.trans (hTsq.trans (by norm_num))
  · exact scalarClippedTrial_uniform_local_energy_density β lam T Cs hβ ⟨hlam.1,hlamβ⟩
      ⟨hT.1,hT.2.trans (by norm_num)⟩ hCspos.le μ hLip

end QuantitativePaper
