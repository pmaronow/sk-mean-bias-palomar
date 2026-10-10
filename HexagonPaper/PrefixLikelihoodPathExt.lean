module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Probability.Process.FiniteDimensionalLaws

@[expose] public section

/-! Full continuous-path law equality from every finite observation law.
This generic lemma upgrades likelihoods of refined finite histories to an
equality on the actual path Borel sigma-algebra. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace HexagonPaper
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem continuousPathMeasure_ext {X E : Type*}
    [TopologicalSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [TopologicalSpace E] [SecondCountableTopology E] [RegularSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P Q : Measure C(X,E)) [IsFiniteMeasure P]
    (h : ∀S : Finset X,P.map (fun p : C(X,E)=>S.restrict p)=
      Q.map (fun p : C(X,E)=>S.restrict p)) : P=Q := by
  let coePath : C(X,E)→(X→E) := fun p=>p
  have hm : Measurable coePath := Measurable.of_eval
    (fun x=>ContinuousMap.measurable_eval x)
  have he : P.map coePath=Q.map coePath := by
    have hp := isProjectiveLimit_map (P:=P) (X:=fun x p=>p x) hm.aemeasurable
    have hq := isProjectiveLimit_map (P:=Q) (X:=fun x p=>p x) hm.aemeasurable
    simp_rw [←h] at hq
    exact hp.unique hq
  have hspace : (inferInstance : MeasurableSpace C(X,E))=
      MeasurableSpace.pi.comap coePath := by
    calc
      _ = ⨆x : X,(inferInstance : MeasurableSpace E).comap
        (fun p : C(X,E)=>p x) :=
          ContinuousMap.measurableSpace_eq_iSup_comap_eval
      _ = _ := by simp only [MeasurableSpace.pi,MeasurableSpace.comap_iSup,
          MeasurableSpace.comap_comp,Function.comp_def,coePath]
  apply Measure.ext
  intro A hA
  change @MeasurableSet C(X,E) (inferInstance : MeasurableSpace C(X,E)) A at hA
  rw [hspace] at hA
  obtain ⟨B,hB,rfl⟩ := hA
  rw [←Measure.map_apply hm hB,←Measure.map_apply hm hB,he]

end HexagonPaper
