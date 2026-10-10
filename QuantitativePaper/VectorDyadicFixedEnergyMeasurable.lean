module
public import QuantitativePaper.VectorDyadicFixedHessianEnergy

@[expose] public section

/-! Measurability of the literal finite Hessian energy follows from genuine
directional difference quotients of the finite gradient. All expected
energies use the actual normalized arbitrary-profile disorder tilt. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem measurable_vectorFiniteTailHessian_entry (s : RSBScheme k) (β t : ℝ) (j l : Fin n) :
    Measurable (fun z : Paper.Overlap×VectorParameter n=>
      vectorFiniteTailHessian s β t z.1 z.2.1 z.2.2 (EuclideanSpace.single j 1) l) := by
  let h:=fun a : ℕ=>(1 : ℝ)/((a : ℝ)+1)
  have hpos (a : ℕ) : 0<h a:=by dsimp [h];positivity
  have hlim : Tendsto h atTop (𝓝[>] (0 : ℝ)):=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,.of_forall hpos⟩
  let Q:=fun a : ℕ=>fun z : Paper.Overlap×VectorParameter n=>
    (h a)⁻¹*(vectorFiniteTailGradient s β t z.1 z.2.1 (z.2.2+h a • EuclideanSpace.single j 1) l-
      vectorFiniteTailGradient s β t z.1 z.2.1 z.2.2 l)
  have hQ (a : ℕ) : Measurable (Q a):=by
    have hshift:Measurable (fun z : Paper.Overlap×VectorParameter n=>
      (z.1,(z.2.1,z.2.2+h a • EuclideanSpace.single j 1))):=by fun_prop
    have h1:=((EuclideanSpace.proj l).continuous.measurable.comp
      (measurable_vectorFiniteTailGradient s β t)).comp hshift
    have h0:=(EuclideanSpace.proj l).continuous.measurable.comp
      (measurable_vectorFiniteTailGradient s β t)
    exact measurable_const.mul (h1.sub h0)
  apply measurable_of_tendsto_metrizable hQ
  apply tendsto_pi_nhds.mpr
  intro z
  let f:=vectorTailRecursion s β t z.1 z.2.1 (k+2)
  let g:=fun x : Field n=>gradient f x l
  have hfs:ContDiff ℝ ∞ f:=contDiff_vectorTailRecursion_field s β t z.1 z.2.1
  have hgs:ContDiff ℝ 2 g:=by
    change ContDiff ℝ 2 ((EuclideanSpace.proj l) ∘ ((InnerProductSpace.toDual ℝ (Field n)).symm ∘ fderiv ℝ f))
    exact (EuclideanSpace.proj l).contDiff.comp
      ((InnerProductSpace.toDual ℝ (Field n)).symm.contDiff.comp
        (hfs.fderiv_right (m:=2) (by simp)))
  have hd:=hasDerivAt_on_affine_line g hgs z.2.2 (EuclideanSpace.single j 1) 0
  have hh:=hd.tendsto_slope_zero_right.comp hlim
  change Tendsto (fun a=>Q a z) atTop
    (𝓝 (hessianOperator f z.2.2 (EuclideanSpace.single j 1) l))
  rw [←fderiv_gradient_component_eq_hessian f (hfs.of_le (by simp))]
  simpa only [Q,g,f,vectorFiniteTailGradient,zero_add,zero_smul,add_zero,smul_eq_mul,
    Function.comp_def] using hh

theorem measurable_uncurry_vectorDyadicFixedHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (j : ℕ) :
    Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      vectorDyadicFixedHessianEnergy μ β t ht z.1 j z.2) := by
  let insert : Paper.Overlap×VectorDisorderBrownianSample n→Paper.Overlap×VectorParameter n:=fun z=>
    (z.1,(z.2.1,vectorMeasureState μ β t ht (z.1 : ℝ).toNNReal z.2))
  let clock : Paper.Overlap×VectorDisorderBrownianSample n→ℝ≥0×VectorDisorderBrownianSample n:=
    fun z=>((z.1 : ℝ).toNNReal,z.2)
  have hclock : Measurable clock:=
    (((continuous_real_toNNReal.comp continuous_subtype_val).measurable.comp measurable_fst).prodMk measurable_snd)
  have hX:Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>
      vectorMeasureState μ β t ht (z.1 : ℝ).toNNReal z.2):=by
    have hh:=(measurable_uncurry_vectorMeasureState (n:=n) μ β t ht).comp hclock
    simpa only [Function.comp_def,Function.uncurry,clock] using hh
  have hIns:Measurable insert:=measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hX)
  unfold vectorDyadicFixedHessianEnergy vectorHessianHilbertSquare
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.measurable_sum
  intro r _
  apply Finset.measurable_sum
  intro l _
  exact ((measurable_vectorFiniteTailHessian_entry
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t r l).comp hIns).pow_const 2

theorem measurable_vectorDyadicFixedHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) :
    Measurable (vectorDyadicFixedHessianEnergy (n:=n) μ β t ht q j) := by
  have hmap:Measurable (fun sample : VectorDisorderBrownianSample n=>(q,sample)):=
    measurable_const.prodMk measurable_id
  have hh:=(measurable_uncurry_vectorDyadicFixedHessianEnergy (n:=n) μ β t ht j).comp hmap
  change Measurable (fun sample : VectorDisorderBrownianSample n=>
    vectorDyadicFixedHessianEnergy μ β t ht q j sample)
  simpa only [Function.comp_def] using hh

theorem integrable_vectorDyadicFixedHessianEnergy (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) :
    Integrable (vectorDyadicFixedHessianEnergy (n:=n) μ β t ht q j)
      (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply Integrable.of_bound (measurable_vectorDyadicFixedHessianEnergy μ β t ht q j).aestronglyMeasurable ((n : ℝ)^3)
  filter_upwards with sample
  rw [Real.norm_eq_abs,abs_of_nonneg (vectorDyadicFixedHessianEnergy_nonneg_le μ β t ht q j sample).1]
  exact (vectorDyadicFixedHessianEnergy_nonneg_le μ β t ht q j sample).2

def vectorDyadicFixedEnergyExpectation (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) : ℝ :=
  ∫sample : VectorDisorderBrownianSample n,vectorDyadicFixedHessianEnergy μ β t ht q j sample
    ∂vectorMeasureDisorderTilt μ β t a

theorem measurable_vectorDyadicFixedEnergyExpectation (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (j : ℕ) : Measurable (fun q=>vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht q j) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  exact ((measurable_uncurry_vectorDyadicFixedHessianEnergy μ β t ht j).stronglyMeasurable.integral_prod_right').measurable

theorem vectorDyadicFixedEnergyExpectation_nonneg_le (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) :
    0≤vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht q j ∧
      vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht q j≤(n : ℝ)^3 := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  refine ⟨integral_nonneg fun sample=>(vectorDyadicFixedHessianEnergy_nonneg_le μ β t ht q j sample).1,?_⟩
  have he:=integral_mono (integrable_vectorDyadicFixedHessianEnergy μ β t a ht q j)
    (integrable_const ((n : ℝ)^3)) (fun sample=>(vectorDyadicFixedHessianEnergy_nonneg_le μ β t ht q j sample).2)
  simpa only [vectorDyadicFixedEnergyExpectation,integral_const,probReal_univ,one_smul] using he

end QuantitativePaper
