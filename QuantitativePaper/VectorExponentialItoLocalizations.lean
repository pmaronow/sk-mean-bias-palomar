module
public import QuantitativePaper.VectorCompactSmoothItoTest
public import FourPapersCommon.ParameterSliceCutoff

@[expose] public section

/-! Actual compact tests approximating a globally smooth observable, with
time fixed on the physical interval and the disorder/field cutoff expanding. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorExponentialTimeCutoff : ℝ→ℝ :=
  (exists_cellTimeCutoff (-1) 0 1 2 (by norm_num) (by norm_num) (by norm_num)).choose

theorem vectorExponentialTimeCutoff_properties :
    ContDiff ℝ ∞ vectorExponentialTimeCutoff ∧ HasCompactSupport vectorExponentialTimeCutoff ∧
      tsupport vectorExponentialTimeCutoff⊆Ioo (-1) 2 ∧
      (∀q,vectorExponentialTimeCutoff q∈Icc (0:ℝ) 1) ∧
      (∀q∈Icc (0:ℝ) 1,vectorExponentialTimeCutoff=ᶠ[𝓝 q] (fun _=>1)) :=
  (exists_cellTimeCutoff (-1) 0 1 2 (by norm_num) (by norm_num) (by norm_num)).choose_spec

def vectorExponentialLocalized (j : ℕ) (f : VectorCompactTestParameter n→ℝ) :
    VectorCompactTestParameter n→ℝ := cellLocalizedFunction vectorExponentialTimeCutoff j f

theorem contDiff_vectorExponentialLocalized (j : ℕ) (f : VectorCompactTestParameter n→ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (vectorExponentialLocalized j f) :=
  contDiff_cellLocalizedFunction _ j f univ isOpen_univ
    vectorExponentialTimeCutoff_properties.1 (subset_univ _) hf.contDiffOn

theorem hasCompactSupport_vectorExponentialLocalized (j : ℕ) (f : VectorCompactTestParameter n→ℝ) :
    HasCompactSupport (vectorExponentialLocalized j f) :=
  hasCompactSupport_cellLocalizedFunction _ j f vectorExponentialTimeCutoff_properties.2.1

theorem vectorExponentialLocalized_eventually_eq (f : VectorCompactTestParameter n→ℝ)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    ∀ᶠj : ℕ in atTop,vectorExponentialLocalized j f=ᶠ[𝓝 (q,(p,x))]f :=
  cellLocalizedFunction_eventually_eq _ f q (p,x)
    (vectorExponentialTimeCutoff_properties.2.2.2.2 q hq)

theorem norm_iteratedFDeriv_vectorExponentialLocalized_slice_le
    (j r : ℕ) (f : VectorCompactTestParameter n→ℝ) (hf : ContDiff ℝ ∞ f)
    (q : ℝ) (p : Couplings n×ℝ) (x : Field n) (B : ℝ)
    (hb : ∀i : ℕ,i≤r→‖iteratedFDeriv ℝ i (fun y=>f (q,(p,y))) x‖≤B) :
    ‖iteratedFDeriv ℝ r (fun y=>vectorExponentialLocalized j f (q,(p,y))) x‖≤
      localizedJetCoefficient (E:=(Couplings n×ℝ)×Field n) r*B := by
  apply norm_iteratedFDeriv_cellLocalized_slice_le _ j r f q p x
    (hf.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))) _ B hb
  exact abs_le.mpr ⟨by linarith [vectorExponentialTimeCutoff_properties.2.2.2.1 q |>.1],
    vectorExponentialTimeCutoff_properties.2.2.2.1 q |>.2⟩

theorem vectorCompactSmoothTimeField_vectorExponentialLocalized
    (j : ℕ) (f : VectorCompactTestParameter n→ℝ) (hf : ContDiff ℝ ∞ f)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    vectorCompactSmoothTimeField (vectorExponentialLocalized j f) (q,(p,x))=
      expandingSmoothCutoff j (p,x)*vectorCompactSmoothTimeField f (q,(p,x)) := by
  exact (hasDerivAt_vectorCompactSmooth_time (contDiff_vectorExponentialLocalized j f hf) q p x).unique
    (hasDerivAt_cellLocalizedFunction_time _ j f q (p,x) _
      (vectorExponentialTimeCutoff_properties.2.2.2.2 q hq)
      (hasDerivAt_vectorCompactSmooth_time hf q p x))

theorem norm_vectorCompactSmoothTimeField_vectorExponentialLocalized_le
    (j : ℕ) (f : VectorCompactTestParameter n→ℝ) (hf : ContDiff ℝ ∞ f)
    (q : ℝ) (hq : q∈Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    ‖vectorCompactSmoothTimeField (vectorExponentialLocalized j f) (q,(p,x))‖≤
      ‖vectorCompactSmoothTimeField f (q,(p,x))‖ := by
  rw [vectorCompactSmoothTimeField_vectorExponentialLocalized j f hf q hq p x,norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact abs_le.mpr ⟨by linarith [expandingSmoothCutoff_mem_Icc j (p,x) |>.1],
    expandingSmoothCutoff_mem_Icc j (p,x) |>.2⟩

end QuantitativePaper
