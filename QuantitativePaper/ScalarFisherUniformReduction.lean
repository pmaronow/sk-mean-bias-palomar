module
public import QuantitativePaper.ScalarFisherLowerReduction
public import QuantitativePaper.ScalarEnergyNearMinimum
public import QuantitativePaper.ScalarVectorResponseBounds
public import QuantitativePaper.ScalarFloorContinuity

@[expose] public section

/-! Application of the actual Fisher midpoint to constrained minimizers.
The final uniform scalar root/smoothing package is consumed as a separate
proved input, so no profile attainment or midpoint minimum is assumed. -/
noncomputable section
open Set MeasureTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 1800000

theorem scalar_floor_fisher_lower_of_uniform_smoothing (β0 Cs C2 Tstar L : ℝ)
    (hβ0 : 1<β0) (hCs : 0<Cs) (hC2 : 0<C2) (hT : Tstar∈Ioc (0:ℝ) (1/4))
    (hL : 0<L) (hL1 : L≤1) (hLβ : L≤β0/2) (hLT : L≤Cs*Tstar)
    (hroot : ∀β : ℝ,β0≤β→∀q∈Icc (0:ℝ) Tstar,
      β*parisiCDF (FRSB.parisiMinimizer β 0) q≤Cs*q)
    (hsmooth : ∀β : ℝ,β0≤β→∀ρ : Paper.ParisiMeasure,
      scalarParisiFunctional β ρ/β≤2→∀q∈Icc (0:ℝ) (1/4),∀x:ℝ,β*parisiHessian β ρ (q,x)≤C2) :
    ∃c0 : ℝ,0<c0 ∧ ∀β : ℝ,β0≤β→∀lam : ℝ,lam∈Ioc (0:ℝ) L→
      c0*lam^5≤ scalarEnergyValue β lam-scalarEnergyValue β 0 := by
  let c0:=min (scalarFisherLowerConstant Cs C2) (1/2)
  have hc0 : 0<c0 := lt_min (scalarFisherLowerConstant_pos Cs C2 hCs hC2) (by norm_num)
  refine ⟨c0,hc0,?_⟩
  intro β hβ0β lam hlam
  have hβ1 : 1≤β := hβ0.le.trans hβ0β
  have hβp : 0<β := zero_lt_one.trans_le hβ1
  have hlam1 : lam≤1 := hlam.2.trans hL1
  have hlamβ : lam/β≤1 := (div_le_one hβp).2 (by linarith)
  let μ:=FRSB.parisiMinimizer β 0
  let ν:=constrainedParisiMinimizer β (lam/β) hlamβ
  have hμ : FRSB.IsParisiMinimizer β 0 μ := FRSB.isParisiMinimizer_selected β 0
  have hνmem : ν∈scalarFloor (lam/β) := constrainedParisiMinimizer_mem β (lam/β) hlamβ
  have hνvalue : scalarEnergyValue β lam=scalarParisiFunctional β ν/β := by
    rw [scalarEnergyValue,constrainedParisiValue_eq_minimum β (lam/β) hlamβ]
  have hμvalue : scalarParisiFunctional β μ/β=scalarEnergyValue β 0 :=
    (scalarEnergyValue_zero_of_minimizer β μ hμ).symm
  by_cases hcost : scalarParisiFunctional β ν/β≤ scalarEnergyValue β 0+1/2
  · have hμcost : scalarParisiFunctional β μ/β≤ scalarEnergyValue β 0+1/2 := by rw [hμvalue];linarith
    let T:=lam/(2*Cs)
    have hTp : 0<T := div_pos hlam.1 (by positivity)
    have hTT : T≤Tstar/2 := by
      apply (div_le_iff₀ (by positivity : 0<2*Cs)).2
      have hh:=hlam.2.trans hLT
      nlinarith
    have hTquarter : T≤1/4 := by linarith [hT.2]
    have hfloor : lam≤β*parisiCDF ν 0 := by
      have hh:=scalarFloor_cdf_lower hνmem (q:=0) le_rfl
      have hr:=(div_le_iff₀ hβp).mp hh
      nlinarith
    have hband : Icc (lam/(8*Cs)) (3*lam/(8*Cs))=Icc (T/4) (3*T/4) := by
      dsimp only [T]
      congr 1 <;> field_simp <;> ring
    have hbandMem {q : ℝ} (hq : q∈Icc (lam/(8*Cs)) (3*lam/(8*Cs))) : q∈Icc (0:ℝ) (1/4) := by
      rw [hband] at hq
      constructor <;> linarith [hq.1,hq.2]
    have hprofile (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (q : ℝ) (hq : q≤1/2) :
        β*parisiCDF (parisiMix μ ν θ) q≤32 :=
      scalarEnergy_near_minimum_mix_cdf_le β hβ1 μ ν hμcost hcost θ
        ⟨hθ.1.le,hθ.2.le⟩ q hq
    have hMixCost (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
        scalarParisiFunctional β (parisiMix μ ν θ)/β≤2 := by
      have hc := (convexOn_parisiPDEFunctional_mix β 0 μ ν).2
        (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num)
        (show 0≤1-θ by linarith [hθ.2]) hθ.1.le (by ring : 1-θ+θ=1)
      simp only [smul_eq_mul,mul_zero,mul_one,zero_add,parisiMix_zero,parisiMix_one] at hc
      change scalarParisiFunctional β (parisiMix μ ν θ)≤
        (1-θ)*scalarParisiFunctional β μ+θ*scalarParisiFunctional β ν at hc
      have hd := div_le_div_of_nonneg_right hc hβp.le
      rw [add_div,mul_div_assoc,mul_div_assoc] at hd
      have hm := mul_le_mul_of_nonneg_left hμcost (by linarith [hθ.2] : 0≤1-θ)
      have hn := mul_le_mul_of_nonneg_left hcost hθ.1.le
      have hmix : scalarParisiFunctional β (parisiMix μ ν θ)/β≤ scalarEnergyValue β 0+1/2 := by
        nlinarith
      exact (scalarEnergy_near_minimum_cost_lt_two β hβ1 _ hmix).le
    have hSmooth (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (q : ℝ) (hq : q∈Icc (0:ℝ) (1/4)) :
        ∀x:ℝ,β*parisiHessian β (parisiMix μ ν θ) (q,x)≤C2 :=
      hsmooth β hβ0β _ (hMixCost θ hθ) q hq
    have hh:=scalar_energy_gap_fisher_lower β lam Cs C2 hβ1 hlam.1 hCs hC2
      (by exact hTquarter.trans (by norm_num)) μ ν hμ hfloor
      (fun q hq=>hroot β hβ0β q ⟨hq.1,hq.2.trans (by linarith)⟩)
      (fun θ hθ q hq=>hprofile θ hθ q ((hbandMem hq).2.trans (by norm_num)))
      (fun θ hθ q hq=>by
        have hqphysical:=hbandMem hq
        let qo : Paper.Overlap:=⟨q,hqphysical.1,hqphysical.2.trans (by norm_num)⟩
        have hmean:=responseMeanHessian_one_zero_time_le (parisiMix μ ν θ) β 0 C2 hβp qo
          (hSmooth θ hθ q hqphysical)
        simpa only [responseMeanHessianReal,show projIcc 0 1 zero_le_one q=qo from
          (projIcc_of_mem zero_le_one qo.property)] using hmean)
      (fun θ hθ q hq=>responseAveragedCurvature_one_zero_time_le (parisiMix μ ν θ) β 0 C2 hβp q
        (hSmooth θ hθ q (hbandMem hq)))
    rw [←hνvalue] at hh
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hlam.1.le _)).trans hh
  · have hlarge : 1/2<scalarEnergyValue β lam-scalarEnergyValue β 0 := by rw [hνvalue];linarith
    have hp : lam^5≤1 := pow_le_one₀ hlam.1.le hlam1
    have hc : c0≤1/2 := min_le_right _ _
    have hh:=mul_le_mul_of_nonneg_left hp hc0.le
    nlinarith

end QuantitativePaper
