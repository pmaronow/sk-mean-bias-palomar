module
public import QuantitativePaper.VectorMeasureSpatialSmooth
public import QuantitativePaper.VectorMeasureGradientStability
public import FourPapersCommon.JointDerivativeContinuity

@[expose] public section

/-! Genuine joint overlap/disorder/field continuity of all actual spatial
jets. Parameters remain merely continuous; uniform directional difference
quotients discharge the joint derivative continuity. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem continuous_vectorMeasureTailPotential_jet (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (r : ℕ) :
    Continuous (fun z : Paper.Overlap×VectorParameter n =>
      iteratedFDeriv ℝ r (vectorMeasureTailPotential μ β t z.1 z.2.1) z.2.2) := by
  let U : (Paper.Overlap×(Couplings n × ℝ))×Field n → ℝ := fun z =>
    vectorMeasureTailPotential μ β t z.1.1 z.1.2 z.2
  let reorder : (Paper.Overlap×(Couplings n × ℝ))×Field n → Paper.Overlap×VectorParameter n :=
    fun z => (z.1.1,(z.1.2,z.2))
  have hcr : Continuous reorder := by
    exact (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hsrc : Continuous (fun z : Paper.Overlap×VectorParameter n =>
      vectorMeasureTailPotential μ β t z.1 z.2.1 z.2.2) :=
    continuous_vectorMeasureTailPotential (n := n) μ β t ht
  have hcU : Continuous U := by
    simpa only [U,reorder,Function.comp_def] using hsrc.comp hcr
  have hsU (a : Paper.Overlap×(Couplings n × ℝ)) : ContDiff ℝ ∞ (fun x => U (a,x)) :=
    contDiff_vectorMeasureTailPotential μ β t ht a.1 a.2
  have hj := continuous_iteratedFDeriv_family_of_uniform_jet_bounds U hcU hsU
    (vectorSpatialJetBound n) (vectorSpatialJetBound_nonneg n)
    (fun j hj a x => norm_vectorMeasureTailPotential_jet_le_uniform μ β t ht
      a.1 a.2 j (by omega) x) r
  let back : Paper.Overlap×VectorParameter n → (Paper.Overlap×(Couplings n×ℝ))×Field n :=
    fun z=>((z.1,z.2.1),z.2.2)
  have hcb : Continuous back := (Homeomorph.prodAssoc Paper.Overlap (Couplings n×ℝ) (Field n)).symm.continuous
  simpa only [U,back,Function.comp_def] using hj.comp hcb

theorem continuous_vectorMeasureHessian (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) :
    Continuous (fun z : Paper.Overlap×VectorParameter n =>
      vectorMeasureHessian μ β t z.1 z.2.1 z.2.2) := by
  let G : (Paper.Overlap×(Couplings n × ℝ))×Field n → Field n := fun z =>
    vectorMeasureGradient μ β t z.1.1 z.1.2 z.2
  let reorder : (Paper.Overlap×(Couplings n × ℝ))×Field n → Paper.Overlap×VectorParameter n :=
    fun z => (z.1.1,(z.1.2,z.2))
  have hcr : Continuous reorder := by
    exact (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hsrc : Continuous (fun z : Paper.Overlap×VectorParameter n =>
      vectorMeasureGradient μ β t z.1 z.2.1 z.2.2) :=
    continuous_vectorMeasureGradient (n := n) μ β t ht
  have hcG : Continuous G := by
    simpa only [G,reorder,Function.comp_def] using hsrc.comp hcr
  have hsG (a : Paper.Overlap×(Couplings n × ℝ)) : ContDiff ℝ ∞ (fun x => G (a,x)) :=
    contDiff_vectorMeasureGradient μ β t ht a.1 a.2
  have hbG (a : Paper.Overlap×(Couplings n × ℝ)) (x : Field n) :
      ‖iteratedFDeriv ℝ 2 (fun y => G (a,y)) x‖ ≤ vectorSpatialJetBound n 3 := by
    have he := funext (vectorMeasureGradient_eq_gradient μ β t ht a.1 a.2)
    change ‖iteratedFDeriv ℝ 2 (vectorMeasureGradient μ β t a.1 a.2) x‖ ≤ _
    rw [he,norm_iteratedFDeriv_gradient]
    exact norm_vectorMeasureTailPotential_jet_le_uniform μ β t ht a.1 a.2 3 (by omega) x
  have hcD := continuous_fderiv_family_of_uniform_secondJet G hcG hsG
    (vectorSpatialJetBound n 3) (vectorSpatialJetBound_nonneg n _) hbG
  let back : Paper.Overlap×VectorParameter n → (Paper.Overlap×(Couplings n×ℝ))×Field n :=
    fun z=>((z.1,z.2.1),z.2.2)
  have hcb : Continuous back := (Homeomorph.prodAssoc Paper.Overlap (Couplings n×ℝ) (Field n)).symm.continuous
  have hh := hcD.comp hcb
  convert hh using 1
  funext z
  exact (hasFDerivAt_vectorMeasureGradient μ β t ht z.1 z.2.1 z.2.2).fderiv.symm

end QuantitativePaper
