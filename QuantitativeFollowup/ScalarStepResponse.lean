module
public import QuantitativeFollowup.ScalarTransportGammaSmooth
public import QuantitativeFollowup.ScalarTransportSevenTermDerivative
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-! Literal step-profile response theorem: genuine C∞ on an open parameter
neighborhood and the exact seven-term derivative at every observed overlap. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativeFollowup
open Paper QuantitativePaper FourPapersCommon SpinGlass.Targets FRSB
set_option maxHeartbeats 1600000
variable {k : ℕ}

def scalarSmoothTransportTest (f : ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f (Icc (0:ℝ) 1)) :
    C(Paper.Overlap,ℝ) :=
  ⟨fun q => f q,hf.continuousOn.comp_continuous continuous_subtype_val (fun q => q.property)⟩

theorem scalar_step_response_identity (s : RSBScheme k) (β : ℝ) (hβ : 0<β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (hμ : parisiSchemeMeasure s ∈ scalarFloor a) (p : Paper.Overlap) :
    ContDiffOn ℝ ∞ (fun u => Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u p)) (Ioo (-δ) δ) ∧
    HasDerivAt (fun u => Gamma β (scalarTransportMeasure (parisiSchemeMeasure s) φ u)
      (scalarLevelTransport φ u p))
      (scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a φ p) 0 := by
  refine ⟨fun u hu => ?_,hasDerivAt_scalarTransportGamma_seven_terms s β hβ φ L hφ h0 h1 δ hδ hsmall a ha hμ p⟩
  have hh := mul_le_mul_of_nonneg_right (abs_lt.mpr hu).le L.coe_nonneg
  exact (contDiffAt_scalarTransportGamma s β hβ.ne' φ L hφ h0 h1 p u (hh.trans_lt hsmall)).contDiffWithinAt

/-- The paper's smooth-test statement, with the Lipschitz constant and the
actual increasing-transport neighborhood constructed from its assumptions. -/
theorem scalar_step_response_smooth_test (s : RSBScheme k) (β : ℝ) (hβ : 0<β)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ ∞ f (Icc (0:ℝ) 1)) (h0 : f 0=0) (h1 : f 1=0)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (hμ : parisiSchemeMeasure s ∈ scalarFloor a) :
    ∃ δ : ℝ, 0<δ ∧ ∀ p : Paper.Overlap,
      ContDiffOn ℝ ∞ (fun u => Gamma β
        (scalarTransportMeasure (parisiSchemeMeasure s) (scalarSmoothTransportTest f hf) u)
        (scalarLevelTransport (scalarSmoothTransportTest f hf) u p)) (Ioo (-δ) δ) ∧
      HasDerivAt (fun u => Gamma β
        (scalarTransportMeasure (parisiSchemeMeasure s) (scalarSmoothTransportTest f hf) u)
        (scalarLevelTransport (scalarSmoothTransportTest f hf) u p))
        (scalarResponseOperator β hβ.ne' (parisiSchemeMeasure s) a (scalarSmoothTransportTest f hf) p) 0 := by
  obtain ⟨L,hL⟩ := hf.exists_lipschitzOnWith (by simp : (∞ : ℕ∞ω)≠0) (convex_Icc 0 1) isCompact_Icc
  have hφ : LipschitzWith L (scalarSmoothTransportTest f hf) := by
    apply LipschitzWith.of_dist_le_mul
    intro q r
    exact hL.dist_le_mul q q.property r r.property
  let δ := (1:ℝ)/(2*((L:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  have hsmall : δ*(L:ℝ)<1 := by
    dsimp [δ]
    apply (div_mul_eq_mul_div _ _ _).trans_lt ?_
    apply (div_lt_one (by positivity)).mpr
    linarith [L.coe_nonneg]
  refine ⟨δ,hδ,fun p => ?_⟩
  exact scalar_step_response_identity s β hβ (scalarSmoothTransportTest f hf) L hφ h0 h1
    δ hδ hsmall a ha hμ p

end QuantitativeFollowup
