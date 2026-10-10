module
public import QuantitativeFollowup.SmallIntervalLocalizedDefect
public import QuantitativeFollowup.SmallIntervalNormalization

@[expose] public section

/-! Follow-up8.1 pointwise bounds for every actual minimizing profile.
The quantile localization is obtained from the literal actual trial gap. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper QuantitativePaper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def smallIntervalTrialGap (n : ℕ) (hn : 0<n) (β lam rho : ℝ)
    (hβ : 0<β) (hlam : lam∈Icc (0:ℝ) β) (hrho : 0 ≤ rho) : ℝ :=
  followupEnergyFunctional n β lam rho
    (scalarClippedTrialMeasure (lam/β)
      ⟨div_nonneg hlam.1 hβ.le,(div_le_one hβ).mpr hlam.2⟩ (parisiMinimizer β 0))-
      followupEnergyMinimum n hn β lam rho hβ hlam.2 hrho

def smallIntervalModelConstant (β K : ℝ) : ℝ :=
  smallIntervalClockConstant K*(1+(smallIntervalLogConstant β)^2)+movingCutoffDefectConstant

theorem smallIntervalModelConstant_pos (β K : ℝ) (hK : 0 ≤ K) :
    0<smallIntervalModelConstant β K := by
  unfold smallIntervalModelConstant
  exact add_pos (mul_pos (smallIntervalClockConstant_pos K hK) (by positivity)) movingCutoffDefectConstant_pos

theorem small_interval_profile_bounds (β : ℝ) (hβ : 1<β) :
    ∃C : ℝ,0<C ∧ ∀n : ℕ,∀hn : 2 ≤ n,∀μ : Paper.ParisiMeasure,∀lam rho eta : ℝ,
      ∀hlam : lam∈Ioc (0:ℝ) (min 1 (β/4)),∀hrho : rho∈Ioc (0:ℝ) 1,
      μ∈scalarFloor (lam/β)  → 
      (∀ν∈scalarFloor (lam/β),followupEnergyFunctional n β lam rho μ ≤ 
        followupEnergyFunctional n β lam rho ν)  →  0 ≤ eta  → 
      smallIntervalTrialGap n (by omega) β lam rho (zero_lt_one.trans hβ)
        ⟨hlam.1.le,by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩ hrho.1.le ≤ eta  → 
      (β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1]) ≤ 
        C*((Real.log (2+(n:ℝ)))^2/((n:ℝ)*rho*lam)+((n:ℝ)*rho)^(-(2/3:ℝ))+
          ((n:ℝ)*rho)^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*(smallIntervalOmega rho eta)^(2/3:ℝ))) ∧
      (β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-rho) (by linarith [hrho.1]) ≤ 
        C*((n:ℝ)*rho)^(-(1/2:ℝ))) := by
  have hβp : 0<β:=zero_lt_one.trans hβ
  obtain ⟨K,hK,hRoot⟩:=probability_root_quantile_localization β hβ
  let C:=smallIntervalModelConstant β K
  refine ⟨C,smallIntervalModelConstant_pos β K (zero_le_one.trans hK),?_⟩
  intro n hn μ lam rho eta hlam hrho hμ hminimal heta hBudget
  have hn0 : 0<n:=by omega
  have hN : (2:ℝ) ≤ n:=by exact_mod_cast hn
  have hlamβ : lam∈Icc (0:ℝ) β:=⟨hlam.1.le,by linarith [hlam.2.trans (min_le_right 1 (β/4))]⟩
  have hs : lam/β∈Ioo (0:ℝ) 1 := by
    constructor
    · positivity [hlam.1]
    · apply (div_lt_one hβp).mpr
      linarith [hlam.2.trans (min_le_right 1 (β/4))]
  have ht : 1-rho<1:=by linarith [hrho.1]
  have hmin : ∀ν∈scalarFloor (lam/β),vectorMeasureFunctional n μ β (1-rho) (lam/β) ≤ 
      vectorMeasureFunctional n ν β (1-rho) (lam/β) := by
    intro ν hν
    exact (div_le_div_iff_of_pos_right hβp).mp (hminimal ν hν)
  have hTrial : followupEnergyFunctional n β lam rho
      (scalarClippedTrialMeasure (lam/β)
        ⟨div_nonneg hlamβ.1 hβp.le,(div_le_one hβp).mpr hlamβ.2⟩ (parisiMinimizer β 0)) ≤ 
      followupEnergyMinimum n hn0 β lam rho hβp hlamβ.2 hrho.1.le+eta := by
    change smallIntervalTrialGap n hn0 β lam rho hβp hlamβ hrho.1.le ≤ eta at hBudget
    unfold smallIntervalTrialGap at hBudget
    linarith
  have hQ : ∀v∈Ioo (0:ℝ) (1-lam/β),(parisiFreeQuantile μ (lam/β) v:ℝ) ≤ 
      K*(lam/β+v+smallIntervalOmega rho eta) := by
    intro v hv
    exact hRoot n hn0 μ lam rho eta v hlamβ hrho hμ hminimal heta hv.1 hTrial
  have homega:=smallIntervalOmega_nonneg rho eta hrho.1.le heta
  have hb:=smallInterval_localized_defect hn0 μ (lam/β) β (1-rho) hβp.ne' ht hs hμ hmin
    K (smallIntervalOmega rho eta) (zero_le_one.trans hK) homega hQ
  dsimp only at hb
  let x:=(n:ℝ)*rho
  let M:=x*β^2
  let L:=1+logPlus M
  let W:=(smallIntervalOmega rho eta)^(2/3:ℝ)
  let X:=(Real.log (2+(n:ℝ)))^2/(x*lam)
  let Y:=x^(-(2/3:ℝ))
  let Z:=x^(-(2/3:ℝ))*lam^(-(1/3:ℝ))*W
  have hx : 0<x:=mul_pos (Nat.cast_pos.mpr hn0) hrho.1
  have hM : 0<M:=mul_pos hx (sq_pos_of_pos hβp)
  have hclock : (n:ℝ)*((1-(1-rho))*β^2)=M:=by dsimp only [M,x];ring
  rw [hclock] at hb
  have hMb : M ≤ β^2*(n:ℝ) := by
    dsimp only [M,x]
    nlinarith [mul_le_mul_of_nonneg_left hrho.2 (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg β))]
  have hLog:=smallInterval_log_bound (n:ℝ) β M hN hβ hM hMb
  have hL : 0 ≤ L:=by dsimp only [L];linarith [logPlus_nonneg M]
  have hSq : L^2 ≤ (smallIntervalLogConstant β)^2*(Real.log (2+(n:ℝ)))^2 := by
    have hh:=pow_le_pow_left₀ hL hLog 2
    simpa only [mul_pow] using hh
  have hFirst : β*(L^2/(M*(lam/β))) ≤ (smallIntervalLogConstant β)^2*X := by
    have he : β/(M*(lam/β))=1/(x*lam):=smallInterval_floor_normalization x β lam hx hβp hlam.1
    calc
      _=L^2*(β/(M*(lam/β))):=by ring
      _=L^2/(x*lam):=by rw [he];ring
      _ ≤ _:=by
        convert div_le_div_of_nonneg_right hSq (mul_nonneg hx.le hlam.1.le) using 1 <;> dsimp only [X] <;> ring
  have hSecond : β*(M^(-(2/3:ℝ))*(1+(lam/β)^(-(1/3:ℝ))*W)) ≤ Y+Z := by
    calc
      _=β*M^(-(2/3:ℝ))+(β*M^(-(2/3:ℝ))*(lam/β)^(-(1/3:ℝ)))*W:=by ring
      _ ≤ Y+(x^(-(2/3:ℝ))*lam^(-(1/3:ℝ)))*W:=
        add_le_add (smallInterval_twoThird_le x β hx hβ.le) (by
          rw [smallInterval_third_normalization x β lam hx hβp hlam.1])
      _=_:=rfl
  have hCC : 0 ≤ smallIntervalClockConstant K:=(smallIntervalClockConstant_pos K (zero_le_one.trans hK)).le
  have hEnergy:=mul_le_mul_of_nonneg_left hb hβp.le
  have hsum:=mul_le_mul_of_nonneg_left (add_le_add hFirst hSecond) hCC
  have hX : 0 ≤ X:=by dsimp only [X];positivity [hlam.1]
  have hY : 0 ≤ Y:=by dsimp only [Y];positivity
  have hZ : 0 ≤ Z:=by dsimp only [Z,W];positivity [hlam.1]
  have hfirst : β*vectorInterpolationDefect (n:=n) μ (lam/β) β (1-rho) ht.le ≤ C*(X+Y+Z) := by
    calc
      _ ≤ smallIntervalClockConstant K*(β*(L^2/(M*(lam/β)))+β*(M^(-(2/3:ℝ))*(1+(lam/β)^(-(1/3:ℝ))*W))):=by
        convert hEnergy using 1 <;> ring
      _ ≤ smallIntervalClockConstant K*((smallIntervalLogConstant β)^2*X+(Y+Z)):=hsum
      _ ≤ (smallIntervalClockConstant K*(1+(smallIntervalLogConstant β)^2))*(X+Y+Z):=by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hCC
        have hp:=mul_nonneg (sq_nonneg (smallIntervalLogConstant β)) (add_nonneg hY hZ)
        nlinarith only [hX,hp]
      _ ≤ C*(X+Y+Z):=mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right movingCutoffDefectConstant_pos.le) (by linarith)
  refine ⟨hfirst,?_⟩
  have hm:=smallInterval_profile_moving hn0 μ β lam rho hβp hrho hs hμ hmin
  exact hm.trans (mul_le_mul_of_nonneg_right
    (show movingCutoffDefectConstant ≤ C from le_add_of_nonneg_left
      (mul_nonneg hCC (by positivity))) (by positivity : 0 ≤ x^(-(1/2:ℝ))))

end QuantitativeFollowup
