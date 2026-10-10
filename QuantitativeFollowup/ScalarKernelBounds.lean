module
public import QuantitativeFollowup.ScalarMarkedSpin

@[expose] public section

/-! Literal scalar kernel estimates, including the genuinely sampled
terminal spin and the genuine fresh-restart transition kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem scalarMarkedSpinLaw_memLp_lift (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (f : Paper.BrownianSample → ℝ) (hf : MemLp f 2 canonicalBrownianMeasure) :
    MemLp (fun z : Paper.BrownianSample×Bool => f z.1) 2 (scalarMarkedSpinLaw β hβ μ) := by
  have hmap : MemLp f 2 ((scalarMarkedSpinLaw β hβ μ).map Prod.fst) := by
    change MemLp f 2 (scalarMarkedSpinLaw β hβ μ).fst
    rw [scalarMarkedSpinLaw_fst β hβ μ]
    exact hf
  exact hmap.comp_of_map measurable_fst.aemeasurable

theorem scalar_marked_centered_spin_pairing (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (p r : Paper.Overlap) :
    |∫ z,scalarCenteredSquare β μ p z.1*Paper.spinSign z.2*M β μ r z.1
      ∂scalarMarkedSpinLaw β hβ μ| ≤ Real.sqrt (Gamma β μ p*Gamma β μ r) := by
  let f : Paper.BrownianSample×Bool → ℝ := fun z => scalarCenteredSquare β μ p z.1
  let g : Paper.BrownianSample×Bool → ℝ := fun z => Paper.spinSign z.2*M β μ r z.1
  have hf := scalarMarkedSpinLaw_memLp_lift β hβ μ _
    (scalarCenteredSquare_memLp_two β μ p p.property)
  have hgm : Measurable g := ((measurable_of_finite Paper.spinSign).comp measurable_snd).mul
    ((measurable_M β μ r r.property).comp measurable_fst)
  have hg : MemLp g 2 (scalarMarkedSpinLaw β hβ μ) := by
    apply MemLp.of_bound hgm.aestronglyMeasurable 1
    exact .of_forall fun z => by
      dsimp only [g]
      rw [norm_mul]
      have hs : ‖Paper.spinSign z.2‖=1 := by cases z.2 <;> norm_num [Paper.spinSign]
      rw [hs,one_mul]
      exact scalar_M_norm_le_one β μ r z.1
  have hfm : Measurable (scalarCenteredSquare β μ p) :=
    ((measurable_M β μ p p.property).pow_const 2).sub measurable_const
  have hfmoment : (∫ z,f z^2 ∂scalarMarkedSpinLaw β hβ μ) ≤ Gamma β μ p := by
    rw [show (∫ z,f z^2 ∂scalarMarkedSpinLaw β hβ μ)=
      ∫ ω,scalarCenteredSquare β μ p ω^2 ∂canonicalBrownianMeasure from
        integral_scalarMarkedSpinLaw_sample β hβ μ _ (hfm.pow_const 2)]
    exact scalarCenteredSquare_secondMoment_le β μ p p.property
  have hgmoment : (∫ z,g z^2 ∂scalarMarkedSpinLaw β hβ μ)=Gamma β μ r := by
    calc
      _ = ∫ z,M β μ r z.1^2 ∂scalarMarkedSpinLaw β hβ μ := by
        apply integral_congr_ae
        exact .of_forall fun z => by
          dsimp only [g]
          cases z.2 <;> simp [Paper.spinSign]
      _ = _ := integral_scalarMarkedSpinLaw_sample β hβ μ _
        ((measurable_M β μ r r.property).pow_const 2)
  have he := integral_mul_abs_le_sqrt_moment_bounds f g hf hg _ _ hfmoment hgmoment.le
  simpa only [f,g,mul_assoc] using he

/-- All clauses of the scalar-kernel lemma, on the actual scalar law. -/
theorem scalar_kernel_bounds (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) :
    MonotoneOn (Gamma β μ) (Icc (0 : ℝ) 1) ∧
    ∀ p r ell : Paper.Overlap,
      (0 ≤ Gamma β μ p ∧ Gamma β μ p ≤ min 1 (β^2*(p : ℝ))) ∧
      |∫ ω,M β μ p ω*C β μ p ω*M β μ r ω ∂canonicalBrownianMeasure| ≤
        Real.sqrt (Gamma β μ p*Gamma β μ r) ∧
      |∫ z,scalarCenteredSquare β μ p z.1*Paper.spinSign z.2*M β μ r z.1
        ∂scalarMarkedSpinLaw β hβ μ| ≤ Real.sqrt (Gamma β μ p*Gamma β μ r) ∧
      |∫ ω,scalarCenteredSquare β μ p ω*M β μ r ω*M β μ ell ω ∂canonicalBrownianMeasure| ≤
        Real.sqrt (Gamma β μ p*Gamma β μ (min (r : ℝ) ell)) ∧
      |∫ ω,scalarCenteredSquare β μ p ω*M β μ p ω*M β μ r ω ∂canonicalBrownianMeasure| ≤
        Real.sqrt (Gamma β μ p*Gamma β μ (min (p : ℝ) r)) ∧
      (0 ≤ variance (fun ω => M β μ p ω^2) canonicalBrownianMeasure ∧
        variance (fun ω => M β μ p ω^2) canonicalBrownianMeasure ≤ Gamma β μ p) ∧
      (0 ≤ (∫ ω,M β μ p ω^2*C β μ p ω ∂canonicalBrownianMeasure) ∧
        (∫ ω,M β μ p ω^2*C β μ p ω ∂canonicalBrownianMeasure) ≤ Gamma β μ p) ∧
      ∀ hpell : (p : ℝ) ≤ ell,
        |covariance (fun ω => M β μ p ω^2) (scalarFutureSquareProcess β μ p ell hpell)
          canonicalBrownianMeasure| ≤ Real.sqrt (Gamma β μ p*Gamma β μ ell) := by
  refine ⟨scalarGamma_monotoneOn β hβ μ,?_⟩
  intro p r ell
  exact ⟨scalarGamma_bound β hβ μ p p.property,
    scalar_M_C_M_pairing β hβ μ p r p.property r.property,
    scalar_marked_centered_spin_pairing β hβ μ p r,
    scalar_centered_square_M_M_pairing β μ p r ell p.property r.property ell.property,
    scalar_centered_square_M_M_pairing β μ p p r p.property p.property r.property,
    scalar_square_variance_bound β μ p p.property,
    scalar_M_sq_C_bound β hβ μ p p.property,
    fun hpell => scalar_square_future_covariance_bound β hβ μ p ell hpell⟩

end QuantitativeFollowup
