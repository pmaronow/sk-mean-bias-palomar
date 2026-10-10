module
public import QuantitativePaper.VectorMeasureSpatialSmooth
public import FourPapersCommon.UniformDerivativeFamily

@[expose] public section

/-! Actual simultaneous uniform convergence of all finite spatial jets over
the entire overlap interval, disorder space, and field space. This permits
moving overlap nodes and true posterior limits. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ContDiff Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem tendstoUniformly_vectorDyadicTailPotential_jets (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (r : ℕ) :
    TendstoUniformly (fun j (z : Paper.Overlap×VectorParameter n) =>
      iteratedFDeriv ℝ r (vectorDyadicTailPotential μ β t z.1 j z.2.1) z.2.2)
      (fun z => iteratedFDeriv ℝ r (vectorMeasureTailPotential μ β t z.1 z.2.1) z.2.2) atTop := by
  let A := Paper.Overlap×(Couplings n × ℝ)
  let f := fun j (a : A) => vectorDyadicTailPotential μ β t a.1 j a.2
  let g := fun a : A => vectorMeasureTailPotential μ β t a.1 a.2
  have hu (r : ℕ) : TendstoUniformly (fun j (z : A×Field n) => iteratedFDeriv ℝ r (f j z.1) z.2)
      (fun z => iteratedFDeriv ℝ r (g z.1) z.2) atTop := by
    induction r with
    | zero =>
      have h0 := (tendstoUniformly_vectorDyadicTailPotential μ β t ht).comp
        (fun z : A×Field n => (z.1.1,(z.1.2,z.2)))
      simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def] using
        (continuousMultilinearCurryFin0 ℝ (Field n) ℝ).symm.isometry.uniformContinuous.comp_tendstoUniformly h0
    | succ r ih =>
      let F := fun j (a : A) => iteratedFDeriv ℝ r (f j a)
      have hs (j : ℕ) (a : A) : ContDiff ℝ ∞ (F j a) :=
        (contDiff_vectorDyadicTailPotential μ β t a.1 j a.2).iteratedFDeriv_right (by simp)
      have hL (j : ℕ) (a : A) : LipschitzWith (vectorSpatialJetBound n (r+2)).toNNReal
          (fderiv ℝ (F j a)) :=
        lipschitz_fderiv_of_secondJet_bound _ (hs j a) _ (vectorSpatialJetBound_nonneg n _)
          (fun x => by
            rw [norm_secondJet_iteratedFDeriv _ (contDiff_vectorDyadicTailPotential μ β t a.1 j a.2)]
            exact norm_vectorDyadicTailPotential_jet_le_uniform μ β t a.1 j a.2 (r+2) (by omega) x)
      have hp (z : A×Field n) : Tendsto (fun j => fderiv ℝ (F j z.1) z.2) atTop
          (𝓝 (fderiv ℝ (iteratedFDeriv ℝ r (g z.1)) z.2)) := by
        have hh := (tendstoUniformly_vectorDyadicTailPotential_jet μ β t ht z.1.1 z.1.2 (r+1)).tendsto_at z.2
        simpa only [F,f,g,fderiv_iteratedFDeriv,Function.comp_def] using
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1) => Field n) ℝ).continuous.tendsto _ |>.comp hh
      have hd := tendstoUniformly_fderiv_family F
        (fun z : A×Field n => fderiv ℝ (iteratedFDeriv ℝ r (g z.1)) z.2)
        (fun j a => (hs j a).differentiable (by simp))
        (vectorSpatialJetBound n (r+2)).toNNReal hL
        (tendstoUniformlyOn_univ.mpr ih).uniformCauchySeqOn hp
      have hh := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (r+1) => Field n) ℝ).symm.isometry.uniformContinuous.comp_tendstoUniformly hd
      simpa only [F,iteratedFDeriv_succ_eq_comp_left,Function.comp_def] using hh
  exact (hu r).comp (fun z : Paper.Overlap×VectorParameter n => ((z.1,z.2.1),z.2.2))

end QuantitativePaper
