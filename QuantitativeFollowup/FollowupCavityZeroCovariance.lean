module
public import QuantitativeFollowup.FollowupCavityInterpolationZeroResponse
public import QuantitativeFollowup.FollowupCavityMarkedCovariance

@[expose] public section

/-! Actual quotient and retained-record covariance at zero incident variance. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency true
variable {n k : ℕ}

theorem hasDerivWithinAt_cavityInterpolationMarkedExpectation_zero
    (D:AnisotropicSpinModel n)(p:AnisotropicCouplingIndex n→Bool)(s:RSBScheme k)
    (a:ℝ)(i:Fin n){j:ℕ}(T:FiniteTerminalGenealogy j)(hj:j ≤ k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F:TerminalSpins (Configuration n) T→ℝ)(d alpha:ℝ)(halpha:0≤alpha)(hd:0<d-alpha):
    HasDerivWithinAt (fun q=>cavityInterpolationMarkedExpectation D p s a i T F q (d-alpha*q))
      ((∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha 0)/
        (∑σ,cavityInterpolationSpinWeight D p s a i T σ 0 d)-
      cavityInterpolationMarkedExpectation D p s a i T F 0 d*
        ((∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha 0)/
          (∑σ,cavityInterpolationSpinWeight D p s a i T σ 0 d))) (Ici (0:ℝ)) 0:=by
  have hd0:0<d:=by linarith
  have hnum : HasDerivWithinAt (fun q=>∑σ,F σ*cavityInterpolationSpinWeight D p s a i T σ q (d-alpha*q))
      (∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha 0) (Ici (0:ℝ)) 0:=by
    apply HasDerivWithinAt.fun_sum
    intro σ _
    exact (hasDerivWithinAt_cavityInterpolationSpinWeight_zero D p s a i T hj σ d alpha halpha hd).const_mul _
  have hden : HasDerivWithinAt (fun q=>∑σ,cavityInterpolationSpinWeight D p s a i T σ q (d-alpha*q))
      (∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha 0) (Ici (0:ℝ)) 0:=by
    apply HasDerivWithinAt.fun_sum
    intro σ _
    exact hasDerivWithinAt_cavityInterpolationSpinWeight_zero D p s a i T hj σ d alpha halpha hd
  have hn:(∑σ,cavityInterpolationSpinWeight D p s a i T σ 0 d)≠0:=
    (cavityInterpolationSpinWeight_sum_pos D p s a i T 0 d hd0).ne'
  have hx:=hnum.div hden (by simpa only [mul_zero,sub_zero] using hn)
  simp only [mul_zero,sub_zero] at hx
  have he : ((∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha 0)*
      (∑σ,cavityInterpolationSpinWeight D p s a i T σ 0 d)-
      (∑σ,F σ*cavityInterpolationSpinWeight D p s a i T σ 0 d)*
        (∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha 0))/
      (∑σ,cavityInterpolationSpinWeight D p s a i T σ 0 d)^2=
      (∑σ,F σ*cavityInterpolationSpinResponse D p s a i T σ d alpha 0)/
        (∑σ,cavityInterpolationSpinWeight D p s a i T σ 0 d)-
      cavityInterpolationMarkedExpectation D p s a i T F 0 d*
        ((∑σ,cavityInterpolationSpinResponse D p s a i T σ d alpha 0)/
          (∑σ,cavityInterpolationSpinWeight D p s a i T σ 0 d)):=by
    rw [cavityInterpolationMarkedExpectation_eq_normalized_weights D p s a i T F 0 d hd0]
    field_simp [hn]
  rw [he] at hx
  apply hx.congr_of_eventuallyEq_of_mem ?_ (by simp)
  have hq:∀ᶠq in 𝓝 (0:ℝ),0<d-alpha*q:=
    ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt).eventually
      (Ioi_mem_nhds (by change 0<d-alpha*(0:ℝ);simpa only [mul_zero,sub_zero] using hd0))
  filter_upwards [hq.filter_mono nhdsWithin_le_nhds] with q hq
  dsimp only [Pi.div_apply]
  exact cavityInterpolationMarkedExpectation_eq_normalized_weights D p s a i T F q (d-alpha*q) hq

theorem hasDerivWithinAt_cavityInterpolationMarkedExpectation_zero_recorded_covariance
    (D:AnisotropicSpinModel n)(p:AnisotropicCouplingIndex n→Bool)(s:RSBScheme k)
    (a:ℝ)(i:Fin n){j:ℕ}(T:FiniteTerminalGenealogy j)(hj:j ≤ k+2)
    [DecidableEq (AnisotropicCouplingIndex n ⊕ GaussianCoordinateIndex (Fin n) T)]
    (F:TerminalSpins (Configuration n) T→ℝ)(d alpha:ℝ)(halpha:0≤alpha)(hd:0<d-alpha):
    HasDerivWithinAt (fun q=>cavityInterpolationMarkedExpectation D p s a i T F q (d-alpha*q))
      ((∫r,F (finiteCascadeRecordTerminalSpins T r.2)*cavityInterpolationRecordScore D p s a i T alpha d r
          ∂cavityInterpolationRecordedLaw D p s a i T 0 d)-
        cavityInterpolationMarkedExpectation D p s a i T F 0 d*
          (∫r,cavityInterpolationRecordScore D p s a i T alpha d r
            ∂cavityInterpolationRecordedLaw D p s a i T 0 d)) (Ici (0:ℝ)) 0:=by
  have hb:0<d-alpha*(0:ℝ):=by simpa only [mul_zero,sub_zero] using (show 0<d by linarith)
  have h1:=integral_cavityInterpolationRecordedLaw_score_mul D p s a i T hj (fun _=>1) d alpha 0 hb
  have hF:=integral_cavityInterpolationRecordedLaw_score_mul D p s a i T hj F d alpha 0 hb
  simp only [one_mul,mul_zero,sub_zero] at h1 hF
  rw [hF,h1]
  exact hasDerivWithinAt_cavityInterpolationMarkedExpectation_zero D p s a i T hj F d alpha halpha hd

theorem hasDerivWithinAt_followupCavityPhysicalExpectation_zero_recorded_covariance
    (n:ℕ)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)(s:RSBScheme k)(a:ℝ)
    (T:FiniteTerminalGenealogy (k+2))
    (F:FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ):
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    HasDerivWithinAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F)
      ((∫r,followupCavityPhysicalRecordObservable n T F r*followupCavityPhysicalRecordScore n β ρ hβ hρ s a T 0 r
          ∂anisotropicTrimmedRecordedTreeLaw D s a T)-
        followupCavityPhysicalExpectation n β ρ hβ hρ s a T F 0*
          (∫r,followupCavityPhysicalRecordScore n β ρ hβ hρ s a T 0 r
            ∂anisotropicTrimmedRecordedTreeLaw D s a T)) (Ici (0:ℝ)) 0:=by
  classical
  dsimp only
  have hb:0<followupCavityD n β ρ-followupCavityAlpha n β ρ:=by
    simpa only [followupCavityB,mul_one] using (mul_pos (sq_pos_of_pos hβ) hρ.1).trans_le
      (followupCavityB_window n β ρ 1 hρ.2 ⟨zero_le_one,le_rfl⟩).1
  have h:=hasDerivWithinAt_cavityInterpolationMarkedExpectation_zero_recorded_covariance
    (followupCavitySpinModel n β ρ hβ hρ 1 ⟨zero_le_one,le_rfl⟩)
    (cavityIncidentRootMask n) s a (Fin.last n) (trimRoot T) (by omega)
    (fun σ=>F (trimmedSpinEquiv (S:=Configuration (n+1)) T
      (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot T) σ)))
    (followupCavityD n β ρ) (followupCavityAlpha n β ρ)
    (followupCavityAlpha_nonneg n β ρ hρ.2) hb
  change HasDerivWithinAt (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F) _ (Ici (0:ℝ)) 0 at h
  have hm:=followupCavity_interpolation_recordedLaw_eq_actual n β ρ hβ hρ s a T 0 ⟨le_rfl,zero_le_one⟩
  dsimp only [followupCavityB] at hm
  simp only [mul_zero,sub_zero] at hm
  rw [hm] at h
  convert! h using 1
  simp only [followupCavityPhysicalExpectation,followupCavityPhysicalRecordScore,followupCavityB,mul_zero,sub_zero]
  congr 1
  apply integral_congr_ae
  exact .of_forall fun r=>by
    dsimp only [followupCavityPhysicalRecordObservable,followupCavityPhysicalRecordScore,followupCavityB]
    rw [terminalSampleEquiv_recordSpins]

end QuantitativeFollowup
