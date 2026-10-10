module
public import QuantitativePaper.VectorMeasureConvexity
public import QuantitativePaper.VectorMeasureFunctional
public import FourPapersCommon.LogMomentConvexity
public import Paper.ParisiMixConvexity

@[expose] public section

/-! Actual convexity of the interpolating arbitrary-probability functional
at every nonnegative outer tilt, including its removable expectation branch. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem normalizedCGF_vectorMeasurePotential_mix_le (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (a : ℝ) (ha : 0 ≤ a)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    normalizedCGF (completionLaw n)
        (fun p => vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0) a ≤
      (1-lam)*normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential μ β t p 0) a +
        lam*normalizedCGF (completionLaw n) (fun p => vectorMeasurePotential ν β t p 0) a := by
  by_cases ha0 : a = 0
  · subst a
    have h0 (ρ : Paper.ParisiMeasure) : (0 : ℝ) ∈ interior
        (integrableExpSet (fun p : Couplings n × ℝ => vectorMeasurePotential ρ β t p 0) (completionLaw n)) := by
      have he : integrableExpSet (fun p : Couplings n × ℝ => vectorMeasurePotential ρ β t p 0)
          (completionLaw n) = univ := Set.eq_univ_iff_forall.mpr
        (fun m => integrable_exp_vectorMeasurePotential (n := n) ρ β t ht m 0)
      rw [he,interior_univ]; trivial
    rw [normalizedCGF_zero _ _ (h0 _),normalizedCGF_zero _ _ (h0 μ),normalizedCGF_zero _ _ (h0 ν)]
    have hh := integral_mono (integrable_vectorMeasurePotential (n := n) _ β t ht 0)
      (((integrable_vectorMeasurePotential (n := n) μ β t ht 0).const_mul (1-lam)).add
        ((integrable_vectorMeasurePotential (n := n) ν β t ht 0).const_mul lam))
      (fun p => vectorMeasurePotential_mix_le μ ν β t ht lam hlam p)
    simp only [Pi.add_apply] at hh
    rw [integral_add ((integrable_vectorMeasurePotential (n := n) μ β t ht 0).const_mul (1-lam))
        ((integrable_vectorMeasurePotential (n := n) ν β t ht 0).const_mul lam),
      integral_const_mul,integral_const_mul] at hh
    exact hh
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [normalizedCGF_of_ne _ _ ha0,normalizedCGF_of_ne _ _ ha0,normalizedCGF_of_ne _ _ ha0]
    have hh := log_integral_exp_mixture_le (completionLaw n)
      (fun p => a*vectorMeasurePotential μ β t p 0)
      (fun p => a*vectorMeasurePotential ν β t p 0)
      (fun p => a*vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0)
      (integrable_exp_vectorMeasurePotential (n := n) μ β t ht a 0)
      (integrable_exp_vectorMeasurePotential (n := n) ν β t ht a 0)
      (integrable_exp_vectorMeasurePotential (n := n) _ β t ht a 0) lam hlam (fun p => by
        have hp := mul_le_mul_of_nonneg_left (vectorMeasurePotential_mix_le μ ν β t ht lam hlam p) ha
        nlinarith [hp])
    change cgf (fun p => vectorMeasurePotential (Paper.parisiMix μ ν lam) β t p 0) (completionLaw n) a ≤
      (1-lam)*cgf (fun p => vectorMeasurePotential μ β t p 0) (completionLaw n) a +
        lam*cgf (fun p => vectorMeasurePotential ν β t p 0) (completionLaw n) a at hh
    have hd := div_le_div_of_nonneg_right hh ha
    convert hd using 1 <;> ring

theorem vectorMeasureFunctional_mix_le (n : ℕ) (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (a : ℝ) (ha : 0 ≤ a)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    vectorMeasureFunctional n (Paper.parisiMix μ ν lam) β t a ≤
      (1-lam)*vectorMeasureFunctional n μ β t a + lam*vectorMeasureFunctional n ν β t a := by
  have hh := div_le_div_of_nonneg_right
    (normalizedCGF_vectorMeasurePotential_mix_le (n := n) μ ν β t ht a ha lam hlam) (Nat.cast_nonneg n)
  unfold vectorMeasureFunctional
  rw [Paper.parisiCorrection_integral_mix μ ν lam hlam]
  ring_nf at hh ⊢
  linarith

theorem convexOn_vectorMeasureFunctional_mix (n : ℕ) (μ ν : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    ConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun lam => vectorMeasureFunctional n (Paper.parisiMix μ ν lam) β t a) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy u v hu hv huv
  have hv1 : v ∈ Icc (0 : ℝ) 1 := ⟨hv,by linarith⟩
  have hu1 : 1-v = u := by linarith
  have hh := vectorMeasureFunctional_mix_le n (Paper.parisiMix μ ν x) (Paper.parisiMix μ ν y)
    β t ht a ha v hv1
  rw [Paper.parisiMix_parisiMix μ ν x y v hx hy hv1,hu1] at hh
  simpa only [smul_eq_mul] using hh

end QuantitativePaper
