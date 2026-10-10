module
public import QuantitativePaper.VectorProfileFiniteCellGenerator

@[expose] public section

/-! Genuine actual finite diffusion Dynkin identities for original-field
profile observables with proved exponential envelopes on cropped cells. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfile_cell_dynkin_of_exponentialSmooth
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t<1)
    (i : ℕ) (hi : i ≤ k+1) (l u A B : ℝ)
    (hl : s₀.q i≤l) (hu : u<s₀.q (i+1)) (hA : 0<A) (hB : B<1)
    (hθ : θ∈Ioo A B) (F : VectorProfileCellParameter n×Field n→ℝ)
    (hf : ExponentialSmoothOn F (vectorProfileJointCylinder l u A B))
    (a b : ℝ≥0) (hab : a≤b) (hb : b≤1) (hla : l<(a:ℝ)) (hbu : (b:ℝ)<u) :
    let hθ01 : θ∈Icc (0:ℝ) 1:=⟨(hA.trans hθ.1).le,(hθ.2.trans hB).le⟩
    let s:=vectorProfileScheme s₀ s₁ θ hθ01
    let X:=vectorFiniteState (n:=n) s β t ht.le
    let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t outer
    let G : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
      vectorProfileCellFieldGenerator s₀ s₁ β t i F (r,θ,sample.1) (X r sample)
    Integrable (Function.uncurry G) ((nonnegativeLebesgueMeasure.restrict (Ioc a b)).prod P) ∧
      (∫sample,F ((b,θ,sample.1),X b sample)-F ((a,θ,sample.1),X a sample) ∂P)=
        ∫sample,(∫r in Ioc a b,G r sample ∂nonnegativeLebesgueMeasure) ∂P := by
  let hθ01 : θ∈Icc (0:ℝ) 1:=⟨(hA.trans hθ.1).le,(hθ.2.trans hB).le⟩
  let s:=vectorProfileScheme s₀ s₁ θ hθ01
  let X:=vectorFiniteState (n:=n) s β t ht.le
  let P:=vectorFiniteDisorderTilt (n:=n) s β t outer
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t outer
  let d:=vectorAdditiveDrift (vectorFiniteDriftData (n:=n) s β t ht.le)
    (Real.sqrt ((1-t)*β^2)) 0 1
  let f:=vectorProfileTestRestriction θ F
  let G : ℝ≥0→VectorDisorderBrownianSample n→ℝ:=fun r sample=>
    vectorProfileCellFieldGenerator s₀ s₁ β t i F (r,θ,sample.1) (X r sample)
  have hl0 : 0≤l:=(s₀.q_nonneg (by omega)).trans hl
  have hu1 : u≤1:=hu.le.trans (s₀.q_le_one (by omega))
  obtain ⟨hfc,K,R,hK,hR,hjets,htime⟩:=vectorProfileTestRestriction_exponential_bounds
    F l u A B θ hf hl0 hu1 hA hB hθ
  obtain ⟨hInt,hId⟩:=vector_finiteTilt_cell_exponential_dynkin s β t outer ht.le f l u
    hfc K R hK hjets htime a b hab hb hla hbu
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc a b)
  have hEq (r : ℝ≥0) (hr : r∈Ioc a b) (sample : VectorDisorderBrownianSample n) :
      vectorExponentialGenerator f X d (Real.sqrt ((1-t)*β^2)) r sample=G r sample:=by
    have hrq : (r:ℝ)∈Ioo l u:=⟨hla.trans hr.1,hbu.trans_le' hr.2⟩
    have hCell : (r:ℝ)∈Ioo (s₀.q i) (s₀.q (i+1)):=⟨hl.trans_lt hrq.1,hrq.2.trans hu⟩
    exact vectorProfileFiniteCellGenerator_eq s₀ s₁ β t θ ht hθ01 i hi F r hCell sample
      (hf.smooth _ ⟨hrq,hθ⟩)
  have hMem : ∀ᵐz ∂ν.prod P,z.1∈Ioc a b:=by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact .of_forall fun _=>hr
  have hIntG : Integrable (Function.uncurry G) (ν.prod P):=hInt.congr (by
    filter_upwards [hMem] with z hz
    exact hEq z.1 hz z.2)
  have he : (∫sample,(∫r in Ioc a b,vectorExponentialGenerator f X d
      (Real.sqrt ((1-t)*β^2)) r sample ∂nonnegativeLebesgueMeasure) ∂P)=
      ∫sample,(∫r in Ioc a b,G r sample ∂nonnegativeLebesgueMeasure) ∂P:=by
    apply integral_congr_ae
    exact .of_forall fun sample=>setIntegral_congr_fun measurableSet_Ioc
      (fun r hr=>hEq r hr sample)
  exact ⟨hIntG,hId.trans he⟩

end QuantitativePaper
