module
public import QuantitativePaper.GaussianShiftColeHopfLipschitz

@[expose] public section

/-! Gaussian Cole--Hopf smoothing preserves Lipschitz estimates along
commuting noise translations on an invariant open parameter domain. The
ambient function need not be Lipschitz in its deterministic parameters. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ContDiff
namespace QuantitativeFollowup
open QuantitativePaper
set_option maxHeartbeats 1000000
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n m : ℕ}

theorem lipschitzWith_gaussian_noise_slice (f : E→ℝ) (U : Set E)
    (A : Field n→L[ℝ]E) (hA : ∀x∈U,∀z,x+A z∈U)
    (H : ℝ≥0) (hLip : ∀x∈U,∀z,|f (x+A z)-f x|≤H*‖z‖)
    (x : E) (hx : x∈U) : LipschitzWith H (fun z=>f (x+A z)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq,dist_eq_norm]
  have hh:=hLip (x+A w) (hA x hx w) (z-w)
  have he : x+A w+A (z-w)=x+A z := by rw [map_sub];abel
  rw [he] at hh
  exact hh

theorem gaussianShiftColeHopf_directional_lipschitz (f : E→ℝ) (U : Set E)
    (A : Field n→L[ℝ]E) (B : Field m→L[ℝ]E)
    (hA : ∀x∈U,∀z,x+A z∈U) (hB : ∀x∈U,∀z,x+B z∈U)
    (H K : ℝ≥0)
    (hLipA : ∀x∈U,∀z,|f (x+A z)-f x|≤H*‖z‖)
    (hLipB : ∀x∈U,∀z,|f (x+B z)-f x|≤K*‖z‖)
    (mass : ℝ) (hmass : 0 ≤ mass) (x : E) (hx : x∈U) (v : Field m) :
    |gaussianShiftColeHopf A mass f (x+B v)-gaussianShiftColeHopf A mass f x|≤K*‖v‖ := by
  rw [gaussianShiftColeHopf_eq_unitVectorStep,gaussianShiftColeHopf_eq_unitVectorStep]
  apply abs_vectorColeHopfStep_sub_le _ _ H
    (lipschitzWith_gaussian_noise_slice f U A hA H hLipA _ (hB x hx v))
    (lipschitzWith_gaussian_noise_slice f U A hA H hLipA x hx)
    1 mass ((K:ℝ)*‖v‖) hmass _ 0
  intro z
  have hh:=hLipB (x+A z) (hA x hx z) v
  have he : x+B v+A z=x+A z+B v := by abel
  rw [he]
  exact hh

end QuantitativeFollowup
