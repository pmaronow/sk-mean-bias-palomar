module
public import FourPapersCommon.ConditionalKernelExpectation
public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-! Conditional averaging against an honestly independent fresh-noise law,
retaining every event of the chosen raw past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
set_option maxHeartbeats 600000
variable {Ω A Z:Type*} [MeasurableSpace A] [MeasurableSpace Z]

theorem restricted_independent_joint_law (m:MeasurableSpace Ω) [mΩ:MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] (hm:m≤mΩ) (X:Ω→A) (hX:Measurable[m] X)
    (W:Ω→Z) (hW:Measurable W) (Q:Measure Z) [IsProbabilityMeasure Q] (hQ:HasLaw W Q P)
    (hI:Indep (MeasurableSpace.comap W inferInstance) m P)
    (E:Set Ω) (hE:MeasurableSet[m] E):
      (P.restrict E).map (fun ω=>(X ω,W ω))=((P.restrict E).map X).prod Q:=by
  letI:MeasurableSpace Ω:=mΩ
  have hXa:=hX.mono hm le_rfl
  have hEa:=hm E hE
  apply Measure.ext_prod
  intro S T hS hT
  have hU:MeasurableSet[m] (X⁻¹' S∩E):=(hX hS).inter hE
  have hV:MeasurableSet[MeasurableSpace.comap W inferInstance] (W⁻¹' T):=⟨T,hT,rfl⟩
  have he: P ((X⁻¹' S∩E)∩W⁻¹' T)=P (X⁻¹' S∩E)*Q T:=by
    rw [(hI.symm.indepSet_of_measurableSet hU hV).measure_inter_eq_mul,
      ←hQ.map_eq,Measure.map_apply hW hT]
  rw [Measure.map_apply (hXa.prodMk hW) (hS.prod hT),Measure.restrict_apply ((hXa.prodMk hW) (hS.prod hT)),
    Measure.prod_prod,Measure.map_apply hXa hS,Measure.restrict_apply (hXa hS)]
  convert he using 1
  congr 1
  ext ω
  simp only [mem_inter_iff,mem_preimage,mem_prod]
  tauto

theorem condExp_independent_noise (m:MeasurableSpace Ω) [mΩ:MeasurableSpace Ω]
    (P:Measure Ω) [IsProbabilityMeasure P] (hm:m≤mΩ) (X:Ω→A) (hX:Measurable[m] X)
    (W:Ω→Z) (hW:Measurable W) (Q:Measure Z) [IsProbabilityMeasure Q] (hQ:HasLaw W Q P)
    (hI:Indep (MeasurableSpace.comap W inferInstance) m P)
    (f:A×Z→ℝ) (hf:Measurable f) (C:ℝ) (hC:∀z,‖f z‖≤C):
    P[(fun ω=>f (X ω,W ω))|m]=ᵐ[P]fun ω=>∫z,f (X ω,z)∂Q:=by
  letI:MeasurableSpace Ω:=mΩ
  have hXa:=hX.mono hm le_rfl
  have hg:StronglyMeasurable (fun x=>∫z,f (x,z)∂Q):=hf.stronglyMeasurable.integral_prod_right'
  have hknown:StronglyMeasurable[m] (fun ω=>∫z,f (X ω,z)∂Q):=hg.comp_measurable hX
  have hfi:Integrable (fun ω=>f (X ω,W ω)) P:=
    (integrable_const C).mono' (hf.comp (hXa.prodMk hW)).aestronglyMeasurable (.of_forall fun ω=>hC _)
  have hgi:Integrable (fun ω=>∫z,f (X ω,z)∂Q) P:=
    (integrable_const C).mono' (hknown.mono hm).aestronglyMeasurable
      (.of_forall fun ω=>by
        simpa using norm_integral_le_of_norm_le_const (μ:=Q) (.of_forall fun z=>hC (X ω,z)))
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hfi
  · intro E hE hfin
    exact hgi.integrableOn
  · intro E hE hfin
    have hEa:=hm E hE
    have he:=restricted_independent_joint_law m P hm X hX W hW Q hQ hI E hE
    have hip:Integrable f (((P.restrict E).map X).prod Q):=
      (integrable_const C).mono' hf.aestronglyMeasurable (.of_forall hC)
    have heint:=congrArg (fun R:Measure (A×Z)=>∫z,f z∂R) he
    rw [integral_map (hXa.prodMk hW).aemeasurable hf.aestronglyMeasurable,
      integral_prod _ hip,integral_map hXa.aemeasurable hg.aestronglyMeasurable] at heint
    exact heint.symm
  · exact hknown.aestronglyMeasurable

end QuantitativePaper
