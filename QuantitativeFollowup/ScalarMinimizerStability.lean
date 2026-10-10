module
public import QuantitativeFollowup.ScalarOperatorStability
public import QuantitativeFollowup.ScalarProfileStability

@[expose] public section

/-! Literal scalar stability at every actual finite-dimensional minimizing
profile, combining genuine localization, scalar-reference continuity, and
the completed response-operator domination. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def followupScalarCoefficient (n : ℕ) (β rho : ℝ) : ℝ := β^2*(1-(1-rho)/(n:ℝ))

theorem followupScalarCoefficient_window (n : ℕ) (hn : 2  ≤  n) (β rho : ℝ)
    (hrho : rho∈Ioc (0:ℝ) 1) :
    followupScalarCoefficient n β rho∈Icc (β^2/2) (β^2) ∧
      |followupScalarCoefficient n β rho-β^2|  ≤  β^2/(n:ℝ) := by
  have hN : (2:ℝ)  ≤  (n:ℝ) := by exact_mod_cast hn
  have hNp : 0<(n:ℝ) := by linarith
  have hz : 0  ≤  (1-rho)/(n:ℝ) := div_nonneg (by linarith [hrho.2]) hNp.le
  have hh : (1-rho)/(n:ℝ)  ≤  (1/2:ℝ) := by
    apply (div_le_iff₀ hNp).mpr
    linarith [hrho.1]
  have hfrac : (1-rho)/(n:ℝ)  ≤  1/(n:ℝ) := div_le_div_of_nonneg_right (by linarith [hrho.1]) hNp.le
  constructor
  · constructor
    · calc
        β^2/2=β^2*(1/2):=by ring
        _  ≤  β^2*(1-(1-rho)/(n:ℝ)):=mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg β)
    · exact mul_le_of_le_one_right (sq_nonneg β) (by linarith)
  · unfold followupScalarCoefficient
    rw [show β^2*(1-(1-rho)/(n:ℝ))-β^2=-(β^2*((1-rho)/(n:ℝ))) by ring,
      abs_neg,abs_of_nonneg (mul_nonneg (sq_nonneg β) hz)]
    exact (mul_le_mul_of_nonneg_left hfrac (sq_nonneg β)).trans_eq (by simp only [div_eq_mul_inv,one_mul])

/-- Literal Proposition 6.7; the λ range is strengthened to [0,β],
and the actual trial-budget and minimizing hypotheses are retained. -/
theorem scalar_minimizer_stability (β : ℝ) (hβ : 1<β) :
    ∃C : ℝ,1  ≤  C ∧
      ∀n : ℕ,∀hn : 2  ≤  n,∀μ : Paper.ParisiMeasure,∀lam rho eta : ℝ,
      ∀hlam : lam∈Icc (0:ℝ) β,∀hrho : rho∈Ioc (0:ℝ) 1,
      μ∈scalarFloor (lam/β)→
      (∀ν∈scalarFloor (lam/β),followupEnergyFunctional n β lam rho μ  ≤  followupEnergyFunctional n β lam rho ν)→
      0  ≤  eta→
      let hs : lam/β∈Icc (0:ℝ) 1 := ⟨div_nonneg hlam.1 (zero_lt_one.trans hβ).le,(div_le_one (zero_lt_one.trans hβ)).mpr hlam.2⟩
      let trial := scalarClippedTrialMeasure (lam/β) hs (parisiMinimizer β 0)
      followupEnergyFunctional n β lam rho trial  ≤  followupEnergyMinimum n (by omega) β lam rho (zero_lt_one.trans hβ) hlam.2 hrho.1.le+eta→
      Paper.parisiCDFDistance μ (parisiMinimizer β 0)  ≤  min 1 (C*(rho^((-3/4:ℝ))*eta^((1/4:ℝ))+lam^2)) ∧
      0  ≤  scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho) ∧
      scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho)  ≤  C*(rho^((-3/4:ℝ))*eta^((1/4:ℝ))+lam^2+(n:ℝ)⁻¹) ∧
      ∀hμ : μ∈scalarFloor (lam/β),∀f : endpointFixedL2 (parisiFreeMeasure μ (lam/β)),
        inner ℝ f (scalarResponseL2Operator (Real.sqrt (followupScalarCoefficient n β rho))
          (Real.sqrt_pos.mpr ((half_pos (sq_pos_of_ne_zero (zero_lt_one.trans hβ).ne')).trans_le (followupScalarCoefficient_window n hn β rho hrho).1.1)).ne' μ (lam/β) hs hμ f)  ≤ 
          (1+scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho))*‖f‖^2 := by
  have hb : 0 < β := zero_lt_one.trans hβ
  obtain ⟨Cp,hCp,hprof⟩:=scalar_profile_stability β hβ
  let K := scalarMultiplierContinuityConstant β
  have hK : 0  ≤  K := (scalarMultiplierContinuityConstant_pos β hb).le
  let C := max 1 (max Cp (K*(Cp+β^2)))
  have hC : 1  ≤  C := le_max_left _ _
  have hCpC : Cp  ≤  C := (le_max_left Cp _).trans (le_max_right _ _)
  have hKsum : K*(Cp+β^2)  ≤  C := (le_max_right Cp _).trans (le_max_right _ _)
  have hKCp : K*Cp  ≤  C := (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg β] : Cp  ≤  Cp+β^2) hK).trans hKsum
  have hKb : K*β^2  ≤  C := (mul_le_mul_of_nonneg_left (by linarith : β^2  ≤  Cp+β^2) hK).trans hKsum
  refine ⟨C,hC,?_⟩
  intro n hn μ lam rho eta hlam hrho hμ hmin heta
  dsimp only
  intro hbudget
  let B := rho^((-3/4:ℝ))*eta^((1/4:ℝ))+lam^2
  have hB : 0  ≤  B := by
    exact add_nonneg (mul_nonneg (Real.rpow_nonneg hrho.1.le _) (Real.rpow_nonneg heta _)) (sq_nonneg lam)
  have hi := hprof n (by omega) μ lam rho eta hlam hrho hμ hmin heta hbudget
  have hdist : Paper.parisiCDFDistance μ (parisiMinimizer β 0)  ≤  Cp*B := hi.trans (min_le_right _ _)
  have hd := followupScalarCoefficient_window n hn β rho hrho
  have hfinv : 0  ≤  (n:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have herr : scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho)  ≤  C*(B+(n:ℝ)⁻¹) := by
    have hmul := mul_le_mul_of_nonneg_left (add_le_add hdist hd.2) hK
    change scalarOperatorStabilityError β μ (followupScalarCoefficient n β rho)  ≤  K*(Cp*B+β^2/(n:ℝ)) at hmul
    calc
      _  ≤  K*(Cp*B+β^2/(n:ℝ)):=hmul
      _=(K*Cp)*B+(K*β^2)*(n:ℝ)⁻¹:=by rw [div_eq_mul_inv];ring
      _  ≤  C*B+C*(n:ℝ)⁻¹:=add_le_add (mul_le_mul_of_nonneg_right hKCp hB) (mul_le_mul_of_nonneg_right hKb hfinv)
      _=C*(B+(n:ℝ)⁻¹):=by ring
  refine ⟨le_min (FourPapersCommon.parisiCDFDistance_le_one _ _) (hdist.trans (mul_le_mul_of_nonneg_right hCpC hB)),
    scalarOperatorStabilityError_nonneg β hb μ _,herr,?_⟩
  intro hμ' f
  exact scalar_reference_operator_stability β hβ μ (followupScalarCoefficient n β rho) hd.1 (lam/β)
    ⟨div_nonneg hlam.1 hb.le,(div_le_one hb).mpr hlam.2⟩ hμ' f

end QuantitativeFollowup
