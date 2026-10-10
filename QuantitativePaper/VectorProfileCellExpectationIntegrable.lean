module
public import QuantitativePaper.VectorProfileActualSourceDynkin
public import QuantitativePaper.VectorFiniteExponentialLocalization

@[expose] public section

/-! Genuine endpoint integrability for actual exponential-growth profile
observables. This justifies splitting their expected differences. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2300000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem integrable_vectorProfile_cell_observable
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (l u A B : ℝ) (hl : 0≤l) (hu : u≤1) (hA : 0<A) (hB : B<1)
    (hθ : θ∈Ioo A B) (F : VectorProfileCellParameter n×Field n→ℝ)
    (hf : ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (r : ℝ≥0) (hr : (r:ℝ)∈Ioo l u) :
    let hθ01 : θ∈Icc (0:ℝ) 1:=⟨(hA.trans hθ.1).le,(hθ.2.trans hB).le⟩
    let s:=vectorProfileScheme s₀ s₁ θ hθ01
    Integrable (fun sample : VectorDisorderBrownianSample n=>
      F ((r,θ,sample.1),vectorFiniteState s β t ht r sample))
      (vectorFiniteDisorderTilt s β t outer) := by
  let hθ01 : θ∈Icc (0:ℝ) 1:=⟨(hA.trans hθ.1).le,(hθ.2.trans hB).le⟩
  let s:=vectorProfileScheme s₀ s₁ θ hθ01
  let X:=vectorFiniteState (n:=n) s β t ht
  have hr1 : r≤1:=by exact_mod_cast hr.2.le.trans hu
  obtain ⟨_,C,R,hC,hR,hjets,_⟩:=vectorProfileTestRestriction_exponential_bounds
    F l u A B θ hf hl hu hA hB hθ
  have hSection : Continuous (fun z : (Couplings n×ℝ)×Field n=>F ((r,θ,z.1),z.2)):=by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((hf.smooth _ ⟨hr,hθ⟩).comp z
      ((contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_fst)).prodMk contDiffAt_snd)).continuousAt
  have hmeas : Measurable (fun sample : VectorDisorderBrownianSample n=>
      F ((r,θ,sample.1),X r sample)):=hSection.measurable.comp
    (measurable_fst.prodMk (measurable_uncurry_vectorFiniteState s β t ht).of_uncurry_left)
  apply ((integrable_exp_vectorFiniteState_and_disorder s β t outer R ht r hr1).const_mul C).mono'
    hmeas.aestronglyMeasurable
  exact .of_forall fun sample=>by
    simpa only [norm_iteratedFDeriv_zero,vectorProfileTestRestriction,Function.comp_def] using
      hjets r hr sample.1 (X r sample) 0 (by norm_num)

end QuantitativePaper
