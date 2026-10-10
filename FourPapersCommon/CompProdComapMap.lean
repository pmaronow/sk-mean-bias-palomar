module
public import FourPapersCommon.FiniteJointLaw

@[expose] public section

/-! Exact transport of a sampled terminal mark with its complete retained
history. The mark kernel depends measurably on that actual history. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]

theorem compProd_comap_map_history (P : Measure Ω) [IsFiniteMeasure P]
    (H : Ω→A) (hH : Measurable H) (κ : Kernel A B) [IsMarkovKernel κ] :
    (P ⊗ₘ (κ.comap H hH)).map (fun p=>(H p.1,p.2))=(P.map H) ⊗ₘ κ := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (show Measurable (fun p : Ω×B=>(H p.1,p.2)) from by fun_prop) (hs.prod ht)]
  have hp : (fun p : Ω×B=>(H p.1,p.2)) ⁻¹' (s ×ˢ t)=(H ⁻¹' s) ×ˢ t := by
    ext p
    rfl
  rw [hp,Measure.compProd_apply_prod (hH hs) ht,Measure.compProd_apply_prod hs ht,
    Measure.restrict_map hH hs]
  exact (lintegral_map (κ.measurable_coe ht) hH).symm

end FourPapersCommon
