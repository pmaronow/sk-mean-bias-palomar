module
public import QuantitativeFollowup.FollowupCavityMixtureHeatZero
public import FourPapersCommon.ExponentialLinearChange

@[expose] public section

/-! Exponential jet bounds of actual retained-field functions supply the
Gaussian row-heat inputs, including after the genuine incident-row CLM. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativeFollowup
open FourPapersCommon
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1200000

theorem cavityRowHeatData_of_exponentialSmooth
    (F : QuantitativePaper.Field n→ℝ) (hF : ExponentialSmoothOn F univ) :
    Nonempty (CavityRowHeatData F) := by
  obtain ⟨B,K,hB,hK,hjet⟩:=hF.common_bound 2
  have hs : ContDiff ℝ ∞ F:=contDiff_iff_contDiffAt.2 (fun x=>hF.smooth x (mem_univ _))
  refine ⟨⟨hs.of_le (by simp),B,K,by linarith,hK,?_,?_,?_⟩⟩
  · intro y
    simpa only [norm_iteratedFDeriv_zero] using hjet 0 (by omega) y (mem_univ _)
  · intro y
    simpa only [norm_iteratedFDeriv_one] using hjet 1 (by omega) y (mem_univ _)
  · intro y
    rw [←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact hjet 2 (by omega) y (mem_univ _)

theorem cavityRowHeatData_of_exponentialSmooth_compCLM
    (F : E→ℝ) (hF : ExponentialSmoothOn F univ)
    (M : QuantitativePaper.Field n→L[ℝ]E) :
    Nonempty (CavityRowHeatData (fun theta=>F (M theta))) :=
  cavityRowHeatData_of_exponentialSmooth _
    (hF.precompCLM M (fun _ _=>mem_univ _))

end QuantitativeFollowup
