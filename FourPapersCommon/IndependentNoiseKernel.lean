module
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-! Genuine kernels obtained by applying a measurable state map to fresh
independent noise; exact joint and two-branch pushforward laws. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

def independentNoiseKernel (Q : Measure C) [IsProbabilityMeasure Q]
    (f : A×C→B) : Kernel A B :=
  (Kernel.id ×ₖ Kernel.const A Q).map f

theorem isMarkovKernel_independentNoiseKernel (Q : Measure C) [IsProbabilityMeasure Q]
    (f : A×C→B) (hf : Measurable f) : IsMarkovKernel (independentNoiseKernel Q f) :=
  Kernel.IsMarkovKernel.map _ hf

theorem independentNoiseKernel_apply (Q : Measure C) [IsProbabilityMeasure Q]
    (f : A×C→B) (hf : Measurable f) (x : A) :
    independentNoiseKernel Q f x=Q.map (fun w=>f (x,w)) := by
  rw [independentNoiseKernel,Kernel.map_apply _ hf,Kernel.prod_apply,
    Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

theorem independentNoiseKernel_joint_law (ν : Measure A) [IsProbabilityMeasure ν]
    (Q : Measure C) [IsProbabilityMeasure Q] (f : A×C→B) (hf : Measurable f) :
    (ν.prod Q).map (fun z=>(z.1,f z))=ν ⊗ₘ independentNoiseKernel Q f := by
  letI:=isMarkovKernel_independentNoiseKernel Q f hf
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (measurable_fst.prodMk hf) (hs.prod ht),
    Measure.prod_apply ((measurable_fst.prodMk hf) (hs.prod ht)),
    Measure.compProd_apply_prod hs ht]
  rw [←lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x∈s
  · simp only [Set.indicator_of_mem hx]
    have hfx : Measurable (fun w : C=>f (x,w)) := hf.comp measurable_prodMk_left
    rw [independentNoiseKernel_apply Q f hf,
      Measure.map_apply hfx ht]
    congr 1
    ext w
    simp only [mem_preimage,mem_prod,hx,true_and]
  · simp only [Set.indicator_of_notMem hx]
    have he : (Prod.mk x) ⁻¹' ((fun z=>(z.1,f z)) ⁻¹' (s ×ˢ t))=∅ := by
      ext w
      simp only [mem_preimage,mem_prod,hx,false_and,mem_empty_iff_false]
    rw [he,measure_empty]

theorem independentNoiseKernel_two_branch_law (ν : Measure A) [IsProbabilityMeasure ν]
    (Q : Measure C) [IsProbabilityMeasure Q] (f : A×C→B) (hf : Measurable f) :
    (ν.prod (Q.prod Q)).map (fun z=>(f (z.1,z.2.1),f (z.1,z.2.2)))=
      (independentNoiseKernel Q f ×ₖ independentNoiseKernel Q f) ∘ₘ ν := by
  letI:=isMarkovKernel_independentNoiseKernel Q f hf
  have hpair : Measurable (fun z : A×(C×C)=>(f (z.1,z.2.1),f (z.1,z.2.2))) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (hf.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hpair hs,Measure.prod_apply (hpair hs),
    Measure.bind_apply hs (Kernel.prod _ _).aemeasurable]
  apply lintegral_congr
  intro x
  have hx : Measurable (fun w : C=>f (x,w)) := hf.comp measurable_prodMk_left
  rw [Kernel.prod_apply,independentNoiseKernel_apply Q f hf,
    Measure.map_prod_map _ _ hx hx,Measure.map_apply (hx.prodMap hx) hs]
  rfl

end FourPapersCommon
