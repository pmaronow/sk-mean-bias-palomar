module
public import HexagonPaper.PathHeatDerivativeLimit
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! Integration and normalization for a path-heat limit. These are assembly
lemmas: the actual Gaussian envelope, signed-measure contractions and finite
Price theorem must supply their hypotheses. No derivative of the limiting
normalized expectation is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def pathHeatNormalizer (μ : Measure Ω) (W : Ω→ℝ) : ℝ := ∫ω,W ω ∂μ

def pathHeatExpectation (μ : Measure Ω) (W F : Ω→ℝ) : ℝ :=
  (∫ω,W ω*F ω ∂μ)/pathHeatNormalizer μ W

def pathHeatResponse (μ : Measure Ω) (W F H J : Ω→ℝ) : ℝ :=
  (∫ω,W ω*(J ω+(F ω-pathHeatExpectation μ W F)*H ω) ∂μ)/pathHeatNormalizer μ W

structure PathHeatDominatedData (μ : Measure Ω) (W F H J e : Ω→ℝ) (B C D : ℝ) : Prop where
  integrable_envelope : Integrable e μ
  nonneg_B : 0≤B
  nonneg_C : 0≤C
  nonneg_D : 0≤D
  weight_measurable : AEStronglyMeasurable W μ
  observable_measurable : AEStronglyMeasurable F μ
  density_generator_measurable : AEStronglyMeasurable H μ
  observable_generator_measurable : AEStronglyMeasurable J μ
  weight_positive : ∀ᵐω ∂μ,0<W ω
  weight_bound : ∀ᵐω ∂μ,W ω≤e ω
  observable_bound : ∀ᵐω ∂μ,|F ω|≤B
  density_generator_bound : ∀ᵐω ∂μ,|H ω|≤C
  observable_generator_bound : ∀ᵐω ∂μ,|J ω|≤D

theorem pathHeat_integrable_weight {W F H J e : Ω→ℝ} {B C D : ℝ}
    (h : PathHeatDominatedData μ W F H J e B C D) : Integrable W μ := by
  apply h.integrable_envelope.mono' h.weight_measurable
  filter_upwards [h.weight_positive,h.weight_bound] with ω hp hb
  simpa only [Real.norm_eq_abs,abs_of_pos hp] using hb

theorem pathHeat_integrable_weighted {W e G : Ω→ℝ} {A : ℝ}
    (he : Integrable e μ) (hA : 0≤A)
    (hW : AEStronglyMeasurable W μ) (hG : AEStronglyMeasurable G μ)
    (hp : ∀ᵐω ∂μ,0<W ω) (hb : ∀ᵐω ∂μ,W ω≤e ω)
    (hg : ∀ᵐω ∂μ,|G ω|≤A) : Integrable (fun ω=>W ω*G ω) μ := by
  apply (he.mul_const A).mono' (hW.mul hG)
  filter_upwards [hp,hb,hg] with ω hwp hwb hgb
  simp only [Real.norm_eq_abs,Pi.mul_apply,abs_mul,abs_of_pos hwp]
  exact mul_le_mul hwb hgb (abs_nonneg _) (hwp.le.trans hwb)

theorem pathHeat_normalizer_positive [IsProbabilityMeasure μ]
    {W F H J e : Ω→ℝ} {B C D : ℝ}
    (h : PathHeatDominatedData μ W F H J e B C D) : 0<pathHeatNormalizer μ W := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (h.weight_positive.mono (fun _ hp=>hp.le)) (pathHeat_integrable_weight h)).mpr
  have hset : Function.support W =ᵐ[μ] (univ : Set Ω) := by
    filter_upwards [h.weight_positive] with ω hp
    apply propext
    simpa only [mem_univ,Function.mem_support,iff_true] using hp.ne'
  rw [measure_congr hset]
  simp

theorem pathHeat_response_eq_raw {W F H J e : Ω→ℝ} {B C D : ℝ}
    (h : PathHeatDominatedData μ W F H J e B C D) :
    pathHeatResponse μ W F H J =
      (∫ω,W ω*J ω ∂μ)/pathHeatNormalizer μ W+
      (∫ω,W ω*(F ω*H ω) ∂μ)/pathHeatNormalizer μ W-
      pathHeatExpectation μ W F*((∫ω,W ω*H ω ∂μ)/pathHeatNormalizer μ W) := by
  have hiJ := pathHeat_integrable_weighted h.integrable_envelope h.nonneg_D
    h.weight_measurable h.observable_generator_measurable h.weight_positive h.weight_bound
    h.observable_generator_bound
  have hiH := pathHeat_integrable_weighted h.integrable_envelope h.nonneg_C
    h.weight_measurable h.density_generator_measurable h.weight_positive h.weight_bound
    h.density_generator_bound
  have hbFH : ∀ᵐω ∂μ,|F ω*H ω|≤B*C := by
    filter_upwards [h.observable_bound,h.density_generator_bound] with ω hf hh
    rw [abs_mul]
    exact mul_le_mul hf hh (abs_nonneg _) h.nonneg_B
  have hiFH := pathHeat_integrable_weighted h.integrable_envelope
    (mul_nonneg h.nonneg_B h.nonneg_C) h.weight_measurable
    (h.observable_measurable.mul h.density_generator_measurable) h.weight_positive h.weight_bound hbFH
  change Integrable (fun ω=>W ω*(F ω*H ω)) μ at hiFH
  have hiSum : Integrable (fun ω=>W ω*J ω+W ω*(F ω*H ω)) μ := hiJ.add hiFH
  unfold pathHeatResponse
  have heq : (fun ω=>W ω*(J ω+(F ω-pathHeatExpectation μ W F)*H ω))=
      fun ω=>W ω*J ω+W ω*(F ω*H ω)-pathHeatExpectation μ W F*(W ω*H ω) := by
    funext ω
    ring
  rw [heq,integral_sub hiSum (hiH.const_mul _),integral_add hiJ hiFH,integral_const_mul]
  ring

theorem pathHeat_tendsto_weighted_integral
    {Wn Gn : ℕ→Ω→ℝ} {W G e : Ω→ℝ} {A : ℝ}
    (he : Integrable e μ) (hA : 0≤A)
    (hW : ∀n,AEStronglyMeasurable (Wn n) μ) (hG : ∀n,AEStronglyMeasurable (Gn n) μ)
    (hp : ∀n,∀ᵐω ∂μ,0<Wn n ω) (hb : ∀n,∀ᵐω ∂μ,Wn n ω≤e ω)
    (hg : ∀n,∀ᵐω ∂μ,|Gn n ω|≤A)
    (hlimW : ∀ᵐω ∂μ,Tendsto (fun n=>Wn n ω) atTop (𝓝 (W ω)))
    (hlimG : ∀ᵐω ∂μ,Tendsto (fun n=>Gn n ω) atTop (𝓝 (G ω))) :
    Tendsto (fun n=>∫ω,Wn n ω*Gn n ω ∂μ) atTop (𝓝 (∫ω,W ω*G ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun ω=>e ω*A)
    (fun n=>(hW n).mul (hG n)) (he.mul_const A)
  · intro n
    filter_upwards [hp n,hb n,hg n] with ω hwp hwb hgb
    simp only [Real.norm_eq_abs,Pi.mul_apply,abs_mul,abs_of_pos hwp]
    exact mul_le_mul hwb hgb (abs_nonneg _) (hwp.le.trans hwb)
  · filter_upwards [hlimW,hlimG] with ω hw hg
    exact hw.mul hg

theorem pathHeat_normalized_limits [IsProbabilityMeasure μ]
    {Wn Fn Hn Jn : ℕ→Ω→ℝ} {W F H J e : Ω→ℝ} {B C D : ℝ}
    (hn : ∀n,PathHeatDominatedData μ (Wn n) (Fn n) (Hn n) (Jn n) e B C D)
    (h : PathHeatDominatedData μ W F H J e B C D)
    (hlimW : ∀ᵐω ∂μ,Tendsto (fun n=>Wn n ω) atTop (𝓝 (W ω)))
    (hlimF : ∀ᵐω ∂μ,Tendsto (fun n=>Fn n ω) atTop (𝓝 (F ω)))
    (hlimH : ∀ᵐω ∂μ,Tendsto (fun n=>Hn n ω) atTop (𝓝 (H ω)))
    (hlimJ : ∀ᵐω ∂μ,Tendsto (fun n=>Jn n ω) atTop (𝓝 (J ω))) :
    (0<pathHeatNormalizer μ W) ∧
    Tendsto (fun n=>pathHeatNormalizer μ (Wn n)) atTop (𝓝 (pathHeatNormalizer μ W)) ∧
    Tendsto (fun n=>pathHeatExpectation μ (Wn n) (Fn n)) atTop (𝓝 (pathHeatExpectation μ W F)) ∧
    Tendsto (fun n=>pathHeatResponse μ (Wn n) (Fn n) (Hn n) (Jn n)) atTop
      (𝓝 (pathHeatResponse μ W F H J)) := by
  have hp := pathHeat_normalizer_positive h
  have hZ : Tendsto (fun n=>pathHeatNormalizer μ (Wn n)) atTop (𝓝 (pathHeatNormalizer μ W)) := by
    apply tendsto_integral_of_dominated_convergence e (fun n=>(hn n).weight_measurable)
      h.integrable_envelope _ hlimW
    intro n
    filter_upwards [(hn n).weight_positive,(hn n).weight_bound] with ω hwp hwb
    simpa only [Real.norm_eq_abs,abs_of_pos hwp] using hwb
  have hIF := pathHeat_tendsto_weighted_integral h.integrable_envelope h.nonneg_B
    (fun n=>(hn n).weight_measurable) (fun n=>(hn n).observable_measurable)
    (fun n=>(hn n).weight_positive) (fun n=>(hn n).weight_bound)
    (fun n=>(hn n).observable_bound) hlimW hlimF
  have hIH := pathHeat_tendsto_weighted_integral h.integrable_envelope h.nonneg_C
    (fun n=>(hn n).weight_measurable) (fun n=>(hn n).density_generator_measurable)
    (fun n=>(hn n).weight_positive) (fun n=>(hn n).weight_bound)
    (fun n=>(hn n).density_generator_bound) hlimW hlimH
  have hIJ := pathHeat_tendsto_weighted_integral h.integrable_envelope h.nonneg_D
    (fun n=>(hn n).weight_measurable) (fun n=>(hn n).observable_generator_measurable)
    (fun n=>(hn n).weight_positive) (fun n=>(hn n).weight_bound)
    (fun n=>(hn n).observable_generator_bound) hlimW hlimJ
  have hbFH : ∀n,∀ᵐω ∂μ,|Fn n ω*Hn n ω|≤B*C := by
    intro n
    filter_upwards [(hn n).observable_bound,(hn n).density_generator_bound] with ω hf hh
    rw [abs_mul]
    exact mul_le_mul hf hh (abs_nonneg _) h.nonneg_B
  have hlimFH : ∀ᵐω ∂μ,Tendsto (fun n=>Fn n ω*Hn n ω) atTop (𝓝 (F ω*H ω)) := by
    filter_upwards [hlimF,hlimH] with ω hf hh
    exact hf.mul hh
  have hIFH := pathHeat_tendsto_weighted_integral h.integrable_envelope
    (mul_nonneg h.nonneg_B h.nonneg_C) (fun n=>(hn n).weight_measurable)
    (fun n=>(hn n).observable_measurable.mul (hn n).density_generator_measurable)
    (fun n=>(hn n).weight_positive) (fun n=>(hn n).weight_bound) hbFH hlimW hlimFH
  have hE : Tendsto (fun n=>pathHeatExpectation μ (Wn n) (Fn n)) atTop (𝓝 (pathHeatExpectation μ W F)) :=
    hIF.div hZ hp.ne'
  refine ⟨hp,hZ,hE,?_⟩
  simp_rw [pathHeat_response_eq_raw (hn _),pathHeat_response_eq_raw h]
  exact ((hIJ.div hZ hp.ne').add (hIFH.div hZ hp.ne')).sub (hE.mul (hIH.div hZ hp.ne'))

theorem hasDerivAt_pathHeat_normalized_limit [IsProbabilityMeasure μ]
    (Wn Fn Hn Jn : ℕ→ℝ→Ω→ℝ) (W F H J : ℝ→Ω→ℝ)
    (e : Ω→ℝ) (B C D a b x : ℝ) (hx : x∈Ioo a b)
    (hn : ∀n z,z∈Icc a b→PathHeatDominatedData μ (Wn n z) (Fn n z) (Hn n z) (Jn n z) e B C D)
    (h : ∀z,z∈Icc a b→PathHeatDominatedData μ (W z) (F z) (H z) (J z) e B C D)
    (hlim : ∀z : ℕ→ℝ,∀y : ℝ,(∀n,z n∈Icc a b)→y∈Icc a b→Tendsto z atTop (𝓝 y)→
      (∀ᵐω ∂μ,Tendsto (fun n=>Wn n (z n) ω) atTop (𝓝 (W y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Fn n (z n) ω) atTop (𝓝 (F y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Hn n (z n) ω) atTop (𝓝 (H y ω))) ∧
      (∀ᵐω ∂μ,Tendsto (fun n=>Jn n (z n) ω) atTop (𝓝 (J y ω))))
    (hfinite : ∀n z,z∈Ioo a b→
      HasDerivAt (fun u=>pathHeatExpectation μ (Wn n u) (Fn n u))
        (pathHeatResponse μ (Wn n z) (Fn n z) (Hn n z) (Jn n z)) z) :
    HasDerivAt (fun u=>pathHeatExpectation μ (W u) (F u))
      (pathHeatResponse μ (W x) (F x) (H x) (J x)) x := by
  have hab : a≤b := hx.1.le.trans hx.2.le
  let clamp : ℝ→ℝ := fun u=>(projIcc a b hab u:ℝ)
  have hc : Continuous clamp := continuous_subtype_val.comp continuous_projIcc
  have hclamp (u : ℝ) : clamp u∈Icc a b := (projIcc a b hab u).property
  have heq (u : ℝ) (hu : u∈Icc a b) : clamp u=u := by
    simp only [clamp,projIcc_of_mem hab hu]
  apply hasDerivAt_pathHeat_limit
    (fun n u=>pathHeatExpectation μ (Wn n u) (Fn n u))
    (fun n u=>pathHeatResponse μ (Wn n (clamp u)) (Fn n (clamp u))
      (Hn n (clamp u)) (Jn n (clamp u)))
    (fun u=>pathHeatExpectation μ (W u) (F u))
    (fun u=>pathHeatResponse μ (W u) (F u) (H u) (J u)) a b x hx
  · intro n z hz
    rw [heq z ⟨hz.1.le,hz.2.le⟩]
    exact hfinite n z hz
  · intro z hz
    have hz' : z∈Icc a b := ⟨hz.1.le,hz.2.le⟩
    obtain ⟨hw,hf,hh,hj⟩ := hlim (fun _=>z) z (fun _=>hz') hz' tendsto_const_nhds
    exact (pathHeat_normalized_limits (fun n=>hn n z hz') (h z hz') hw hf hh hj).2.2.1
  · intro z hz
    have hx' : x∈Icc a b := ⟨hx.1.le,hx.2.le⟩
    have hcz : Tendsto (fun n=>clamp (z n)) atTop (𝓝 x) := by
      simpa only [Function.comp_def,heq x hx'] using (hc.tendsto x).comp hz
    obtain ⟨hw,hf,hh,hj⟩ := hlim (fun n=>clamp (z n)) x (fun n=>hclamp (z n)) hx' hcz
    exact (pathHeat_normalized_limits (fun n=>hn n _ (hclamp (z n))) (h x hx') hw hf hh hj).2.2.2

end HexagonPaper
