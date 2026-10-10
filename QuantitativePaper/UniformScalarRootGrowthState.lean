module
public import QuantitativePaper.UniformScalarMild
public import FRSB.OptimalDiffusion

@[expose] public section

/-! Pathwise comparison of the actual energy-coordinate diffusion with its
Brownian driver under the true early CDF bound. -/
noncomputable section
open Set MeasureTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 700000

theorem scalarEnergyState_brownian_shift_bound (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (q : ℝ) (hq : q∈Icc (0:ℝ) 1)
    (hg : ∀s∈Icc (0:ℝ) q,β*parisiCDF μ s≤32) (ω : Paper.BrownianSample) :
    ‖FRSB.optimalStateReal β μ ω q/β-canonicalBrownian q.toNNReal ω‖≤32*q := by
  have he:=FRSB.optimalState_integral_equation β μ ω hq
  have hh:=intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=q) (C:=32*β)
    (f:=fun s=>β^2*FRSB.alpha μ s*FRSB.M β μ s ω) (by
      intro s hs
      rw [uIoc_of_le hq.1] at hs
      have hsI : s∈Icc (0:ℝ) q:=⟨hs.1.le,hs.2⟩
      have hm : ‖FRSB.M β μ s ω‖≤1:=by
        simpa only [FRSB.M,FRSB.jetProcess,FRSB.parisiSpatialJet_one] using
          norm_parisiGradient_le_one β μ (s,FRSB.optimalStateReal β μ ω s)
      have hgn : 0≤β*parisiCDF μ s:=mul_nonneg hβ.le (parisiCDF_nonneg μ s)
      have ha : ‖β^2*FRSB.alpha μ s‖≤32*β:=by
        change ‖β^2*parisiCDF μ s‖≤32*β
        rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg β) (parisiCDF_nonneg μ s))]
        have hg' :=mul_le_mul_of_nonneg_left (hg s hsI) hβ.le
        change β^2*parisiCDF μ s≤32*β
        nlinarith
      rw [norm_mul]
      simpa only [mul_one] using mul_le_mul ha hm (norm_nonneg _) (by positivity : (0:ℝ)≤32*β))
  rw [sub_zero,abs_of_nonneg hq.1] at hh
  have hid : FRSB.optimalStateReal β μ ω q/β-canonicalBrownian q.toNNReal ω=
      (∫s in (0:ℝ)..q,β^2*FRSB.alpha μ s*FRSB.M β μ s ω)/β := by
    rw [he]
    field_simp
    <;> ring
  rw [hid,norm_div,Real.norm_of_nonneg hβ.le]
  apply (div_le_iff₀ hβ).mpr
  nlinarith

theorem scalarEnergyState_on_brownian_window (β : ℝ) (hβ : 0<β)
    (μ : ParisiMeasure) (q : ℝ) (hq : q∈Ioc (0:ℝ) (1/4096))
    (hg : ∀s∈Icc (0:ℝ) q,β*parisiCDF μ s≤32) (ω : Paper.BrownianSample)
    (hω : canonicalBrownian q.toNNReal ω/Real.sqrt q∈Icc (1:ℝ) 2) :
    FRSB.optimalStateReal β μ ω q/β∈Icc (Real.sqrt q/2) (3*Real.sqrt q) := by
  have hs : 0<Real.sqrt q:=Real.sqrt_pos.2 hq.1
  have hsq : (Real.sqrt q)^2=q:=Real.sq_sqrt hq.1.le
  have hsmall : Real.sqrt q≤1/64:=by
    have h:=Real.sqrt_le_sqrt hq.2
    norm_num at h
    exact h
  have hshift:=scalarEnergyState_brownian_shift_bound β hβ μ q
    ⟨hq.1.le,hq.2.trans (by norm_num)⟩ hg ω
  rw [Real.norm_eq_abs,abs_le] at hshift
  have hlo:=(le_div_iff₀ hs).mp hω.1
  have hhi:=(div_le_iff₀ hs).mp hω.2
  constructor <;> nlinarith

end QuantitativePaper
