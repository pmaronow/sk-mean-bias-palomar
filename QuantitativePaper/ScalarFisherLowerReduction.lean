module
public import QuantitativePaper.ScalarFisherBudget
public import QuantitativePaper.ScalarEnergyFunctionalIdentification
public import QuantitativePaper.ResponseMidpointProposition

@[expose] public section

/-! The actual scalar midpoint argument for the fifth-order lower floor
cost. Uniform scalar root and smoothing bounds are applied in the final
temperature-uniform theorem. -/
noncomputable section
open Set MeasureTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 1600000

def scalarFisherLowerConstant (Cs C2 : ℝ) : ℝ :=
  (responseCurvatureConstant 32)^4/(4096*Cs^3*(8*C2+32*C2^2))

theorem scalarFisherLowerConstant_pos (Cs C2 : ℝ) (hCs : 0<Cs) (hC2 : 0<C2) :
    0<scalarFisherLowerConstant Cs C2 := by
  unfold scalarFisherLowerConstant
  positivity [responseCurvatureConstant_pos 32]

theorem scalar_energy_gap_fisher_lower (β lam Cs C2 : ℝ) (hβ : 1≤β)
    (hlam : 0<lam) (hCs : 0<Cs) (hC2 : 0<C2)
    (hT : lam/(2*Cs)≤1)
    (μ ν : Paper.ParisiMeasure) (hmin : FRSB.IsParisiMinimizer β 0 μ)
    (hfloor : lam≤β*parisiCDF ν 0)
    (hroot : ∀q∈Icc (0:ℝ) (lam/(2*Cs)),β*parisiCDF μ q≤Cs*q)
    (hprofile : ∀θ∈Ioo (0:ℝ) 1,∀q∈Icc (lam/(8*Cs)) (3*lam/(8*Cs)),
      β*parisiCDF (parisiMix μ ν θ) q≤32)
    (hb : ∀θ∈Ioo (0:ℝ) 1,∀q∈Icc (lam/(8*Cs)) (3*lam/(8*Cs)),
      responseMeanHessianReal (n:=1) (parisiMix μ ν θ) β 0 0 (by norm_num) q≤C2)
    (hζ : ∀θ∈Ioo (0:ℝ) 1,∀q : Paper.Overlap,(q:ℝ)∈Icc (lam/(8*Cs)) (3*lam/(8*Cs))→
      responseAveragedCurvature (n:=1) (parisiMix μ ν θ) β 0 0 (by norm_num) q≤C2^2) :
    scalarFisherLowerConstant Cs C2*lam^5≤ scalarParisiFunctional β ν/β-scalarEnergyValue β 0 := by
  have hβp : 0<β := zero_lt_one.trans_le hβ
  let T:=lam/(2*Cs)
  have hTp : 0<T := div_pos hlam (by positivity)
  have hband : Icc (T/4) (3*T/4)=Icc (lam/(8*Cs)) (3*lam/(8*Cs)) := by
    dsimp only [T]
    congr 1 <;> field_simp <;> ring
  have hTmem : T∈Ioc (0:ℝ) 1 := ⟨hTp,hT⟩
  have hdir : ∀θ∈Ioo (0:ℝ) 1,∀q∈Icc (T/4) (3*T/4),
      lam/2≤β*(parisiCDF ν q-parisiCDF μ q) := by
    intro θ hθ q hq
    have hq0 : 0≤q := (by linarith : 0≤T/4).trans hq.1
    have hqT : q≤T := hq.2.trans (by linarith)
    have hc := hroot q ⟨hq0,hqT⟩
    have hv := hfloor.trans (mul_le_mul_of_nonneg_left (parisiCDF_monotone ν hq0) hβp.le)
    have hs := mul_le_mul_of_nonneg_left hqT hCs.le
    have he : Cs*T=lam/2 := by dsimp only [T];field_simp <;> ring
    rw [he] at hs
    nlinarith
  have hBudget : ∀θ∈Ioo (0:ℝ) 1,β*(∫q : Paper.Overlap in
      {q : Paper.Overlap | (q:ℝ)∈Icc (T/4) (3*T/4)},
      responseAveragedCurvature (n:=1) (parisiMix μ ν θ) β 0 0 (by norm_num) q
        ∂(parisiMix μ ν θ : Measure Paper.Overlap))≤32*C2^2 := by
    intro θ hθ
    have hh := response_curvature_band_budget (n:=1) (parisiMix μ ν θ) β 0 0
      (T/4) (3*T/4) (C2^2) 32 hβp.le (by norm_num) (sq_nonneg C2)
      (fun q hq => hζ θ hθ q (by rwa [hband] at hq))
      (hprofile θ hθ (3*T/4) (by rw [←hband];constructor <;> linarith))
    simpa only [mul_comm (C2^2) 32] using hh
  have hmid := (response_midpoint 1 (by norm_num) β 0 0 hβp (by norm_num)
    (by constructor <;> positivity) μ ν
    (mul_nonneg hβp.le (parisiCDF_nonneg μ 0))
    (mul_nonneg hβp.le (parisiCDF_nonneg ν 0))).2 hβ T (lam/2) 32 C2 (32*C2^2)
    hTmem (by positivity) (by norm_num) hC2 (by positivity) hdir
    (fun θ hθ q hq => hprofile θ hθ q (by rwa [hband] at hq))
    (fun θ hθ q hq => hb θ hθ q (by rwa [hband] at hq))
    (by simpa only [sub_zero,one_mul] using hBudget)
  simp only [sub_zero,one_pow,one_mul,mul_one] at hmid
  rw [responseEnergyFunctional_zero 1 (by norm_num) μ β 0 hβp.ne',
    responseEnergyFunctional_zero 1 (by norm_num) ν β 0 hβp.ne',
    responseEnergyFunctional_zero 1 (by norm_num) (parisiMix μ ν (1/2)) β 0 hβp.ne',
    ←scalarEnergyValue_zero_of_minimizer β μ hmin] at hmid
  have hminmid : scalarEnergyValue β 0≤ scalarParisiFunctional β (parisiMix μ ν (1/2))/β := by
    rw [scalarEnergyValue_zero_of_minimizer β μ hmin]
    exact div_le_div_of_nonneg_right (hmin (parisiMix μ ν (1/2))) hβp.le
  have hden : 0<128*(8*C2+T*(32*C2^2)) := by positivity
  have hdenUpper : 128*(8*C2+T*(32*C2^2))≤128*(8*C2+32*C2^2) := by
    nlinarith [sq_nonneg C2]
  have hnum : (responseCurvatureConstant 32)^4*(lam/2)^2*T^3=
      (responseCurvatureConstant 32)^4*lam^5/(32*Cs^3) := by
    dsimp only [T]
    field_simp
    ring
  have hconst : scalarFisherLowerConstant Cs C2*lam^5≤
      (responseCurvatureConstant 32)^4*(lam/2)^2*T^3/(128*(8*C2+T*(32*C2^2))) := by
    rw [hnum]
    apply le_trans ?_ (div_le_div_of_nonneg_left (by positivity) hden hdenUpper)
    unfold scalarFisherLowerConstant
    apply le_of_eq
    field_simp
    ring
  linarith

end QuantitativePaper
