module
public import QuantitativeFollowup.ScalarTransportNodeScheduledDerivative
public import QuantitativeFollowup.ScalarPartialCovarianceResponse

@[expose] public section

/-! The derivative of the actual moved-node potential is expressed under
its genuine refined scalar endpoint probability kernels. All response
coefficients, signs, and partial depths are derived from the actual schedule. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {k : ℕ}

theorem scalarTransportSchedule_partial_response (s : RSBScheme k) (β : ℝ) (hβ : 0 < β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ)
    (j J : ℕ) (hj : j < 3*J) (hJ : J ≤ k+2)
    (h : ℝ) (H : FiniteStateField (Fin 1)) (v : ℝ) (hv : 0 ≤ v) :
    finiteStateCascadeCovarianceResponse (scalarSpinPotential h) (coefficientScheduleMass s)
      (fun i=>finiteStateScheduleScale (scalarTransportScheduleUp s φ i) (signedAffineCellTime δ u) •
        scalarTransportScheduleDirection s β φ δ i) j (3*J-j) (replicaSingleSiteSpinCLM H)
        (scalarSpinDirection v)=
      v*(1+∑p∈Finset.range j,(coefficientScheduleMass s (p+1)-coefficientScheduleMass s p)*
        scalarSchemeFutureSquareKernel (scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu)
          β hβ h (p+1) (3*J) H) := by
  let r:=scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu
  have hm (i : ℕ) : coefficientScheduleMass s i=scalarSchemeMass r i :=
    (scalarTransportRefinedScheme_mass s φ L hφ h0 h1 δ u hδ hsmall hu i).symm
  have hA (i : ℕ) (hi : i < j+(3*J-j)) :
      finiteStateScheduleScale (scalarTransportScheduleUp s φ i) (signedAffineCellTime δ u) •
        scalarTransportScheduleDirection s β φ δ i=scalarSchemeSpinInput r β i :=
    (scalarTransportRefinedScheme_input s β φ L hφ h0 h1 δ u hδ hsmall hu i (by omega)).symm
  rw [finiteStateCascadeCovarianceResponse_congr_prefix (scalarSpinPotential h) _ _ _ _ j
    (3*J-j) (by omega) (fun i _=>hm i) hA,
    scalarGaussianCascade_partial_response r β hβ h j (3*J) hj (by omega) H v hv]
  simp_rw [hm]
  rfl

theorem scalarTransportSchedule_signed_active_variance (s : RSBScheme k) (β : ℝ)
    (φ : C(Paper.Overlap,ℝ)) (δ : ℝ) (i : ℕ) :
    (if scalarTransportScheduleUp s φ (3*i+2) then (1:ℝ) else -1)*
      (β^2*scalarTransportCellActive s φ δ (k+1-i))=
      2*δ*β^2*scalarTransportCellSlope s φ (k+1-i) := by
  simp only [scalarTransportScheduleUp,scalarTransportCellActive,
    show (3*i+2)%3=2 by omega,show (3*i+2)/3=i by omega,
    show ¬(2:ℕ)=0 by decide,show ¬(2:ℕ)=1 by decide,ite_false]
  by_cases hp : 0 ≤ scalarTransportCellSlope s φ (k+1-i)
  · simp only [hp,decide_true,ite_true,abs_of_nonneg hp]
    ring
  · simp only [hp,decide_false,Bool.false_eq_true,ite_false,abs_of_neg (lt_of_not_ge hp)]
    ring

theorem scalarTransportNodeScheduleDerivative_eq_refined_futures (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| < δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    scalarTransportNodeScheduleDerivative s β φ δ J u x=
      β^2/2*∑i∈Finset.range J,scalarTransportCellSlope s φ (k+1-i)*
        (1+∑p∈Finset.range (3*i+2),(coefficientScheduleMass s (p+1)-coefficientScheduleMass s p)*
          scalarSchemeFutureSquareKernel
            (scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu.le)
            β hβ 0 (p+1) (3*J) (EuclideanSpace.single (0:Fin 1) x)) := by
  rw [scalarTransportNodeScheduleDerivative_eq_signed_responses s β φ δ u x hδ hu J]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hj := Finset.mem_range.mp hi
  have hv : 0 ≤ β^2*scalarTransportCellActive s φ δ (k+1-i) := by
    unfold scalarTransportCellActive
    positivity
  have hdir : scalarTransportScheduleDirection s β φ δ (3*i+2)=
      scalarSpinDirection (β^2*scalarTransportCellActive s φ δ (k+1-i)) := by
    simp [scalarTransportScheduleDirection,Nat.mul_comm,Nat.add_div,Nat.add_mod]
  rw [hdir,scalarTransportSchedule_partial_response s β hβ φ L hφ h0 h1 δ u
    hδ hsmall hu.le (3*i+2) J (by omega) hJ 0 (EuclideanSpace.single (0:Fin 1) x) _ hv]
  rw [←mul_assoc (if scalarTransportScheduleUp s φ (3*i+2) then (1:ℝ) else -1),
    scalarTransportSchedule_signed_active_variance]
  field_simp
  ring

end QuantitativeFollowup
