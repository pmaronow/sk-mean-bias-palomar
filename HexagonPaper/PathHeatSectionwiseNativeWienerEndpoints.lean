module
public import HexagonPaper.PathHeatSectionwiseNativeWiener
public import HexagonPaper.PathHeatSectionwiseNativeWienerTransfer
public import HexagonPaper.PathHeatSectionwiseWienerMoments

@[expose] public section

/-! C1 and the genuine endpoint formulas for the original compact index
and the manuscript's actual finite counting measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped Topology BigOperators unitInterval NNReal ENNReal BoundedContinuousFunction
namespace HexagonPaper
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X E K : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Fintype K] [Nonempty K] [TopologicalSpace K] [DiscreteTopology K]
  [MeasurableSpace K] [BorelSpace K] [MeasurableSingletonClass K]
variable {L : ℕ} {a b : ℝ}

theorem pathHeatSectionwiseNativeWiener_continuity
    (μ : Measure E) [IsGaussian μ] (hab : a≤b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab d C)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdcc : ∀l,Continuous (fun z=>dc z l)) :
    Continuous (fun u=>pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W (projIcc a b hab u)) ∧
    Continuous (fun u=>pathHeatSectionwiseNativeWienerResponse μ d ι c dc δ W (projIcc a b hab u)) ∧
    Continuous (fun u=>Real.log (pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W (projIcc a b hab u))) ∧
    Continuous (fun u=>pathHeatSectionwiseNativeWienerLogNormalizerResponse μ d ι c dc δ W (projIcc a b hab u)) := by
  letI : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  let df := pathHeatSectionwiseNativeSourceExtension ι d
  have hs := pathHeatSectionwiseNativeSourceExtension_analytic hab ι d C hsource
  have hm := pathHeatSectionwiseWiener_continuous_moments μ df c dc δ W hab C hs hc hdcc
  have hp := hm.1
  have hE := hm.2.2.1.comp (continuous_projIcc (a:=a) (b:=b) (h:=hab))
  have hR := hm.2.2.2.1.comp (continuous_projIcc (a:=a) (b:=b) (h:=hab))
  have hLog := (hm.2.1.log (fun z=>(hp z).ne')).comp (continuous_projIcc (a:=a) (b:=b) (h:=hab))
  have hEH := hm.2.2.2.2.comp (continuous_projIcc (a:=a) (b:=b) (h:=hab))
  have hcard : (Fintype.card K:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have hlog : (fun u=>Real.log (pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W (projIcc a b hab u)))=
      fun u=>Real.log (Fintype.card K:ℝ)+
        Real.log (pathHeatSectionwiseWienerNormalizer μ df c δ W (projIcc a b hab u)) := by
    funext u
    rw [pathHeatSectionwiseNativeWienerNormalizer_eq_card_flat,Real.log_mul hcard (hp _).ne']
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [pathHeatSectionwiseNativeWienerExpectation_eq_flat,Function.comp_def,df] using hE
  · simpa only [pathHeatSectionwiseNativeWienerResponse_eq_flat,Function.comp_def,df] using hR
  · rw [hlog]
    exact continuous_const.add hLog
  · simpa only [pathHeatSectionwiseNativeWienerLogNormalizerResponse_eq_flat,Function.comp_def,df] using hEH

theorem pathHeatSectionwiseNativeWiener_C1_and_endpoints
    (μ : Measure E) [IsGaussian μ] (hab : a<b)
    (d : PathHeatSectionwiseSignedSource (Icc a b) E K X)
    (C : ℝ≥0) (hsource : PathHeatSectionwiseAnalyticSource a b hab.le d C)
    (ι : C(X,Fin L×I)) (c : Icc a b→Fin L→C(I,I)) (dc : Icc a b→Fin L→C(I,ℝ))
    (δ : Fin L→ℝ) (W : Fin L→Fin L→ℝ)
    (hc : ∀l,Continuous (fun z=>c z l)) (hdcc : ∀l,Continuous (fun z=>dc z l))
    (hstrict : ∀z : Icc a b,z.val∈Ioo a b→∀l,StrictMono (c z l))
    (hroot : ∀z l,c z l 0=0)
    (hdc : ∀z∈Ioo a b,∀l t,
      HasDerivAt (fun u=>(c (projIcc a b hab.le u) l t:ℝ))
        (dc (projIcc a b hab.le z) l t) z) :
    let f := fun u=>pathHeatSectionwiseNativeWienerExpectation μ d ι c δ W (projIcc a b hab.le u)
    let r := fun u=>pathHeatSectionwiseNativeWienerResponse μ d ι c dc δ W (projIcc a b hab.le u)
    let g := fun u=>Real.log (pathHeatSectionwiseNativeWienerNormalizer μ d ι c δ W (projIcc a b hab.le u))
    let s := fun u=>pathHeatSectionwiseNativeWienerLogNormalizerResponse μ d ι c dc δ W (projIcc a b hab.le u)
    ContDiffOn ℝ 1 f (Ioo a b) ∧ ContDiffOn ℝ 1 g (Ioo a b) ∧
    HasDerivWithinAt f (r a) (Ici a) a ∧ HasDerivWithinAt f (r b) (Iic b) b ∧
    HasDerivWithinAt g (s a) (Ici a) a ∧ HasDerivWithinAt g (s b) (Iic b) b := by
  dsimp only
  have hm := pathHeatSectionwiseNativeWiener_continuity μ hab.le d C hsource ι c dc δ W hc hdcc
  have hderiv (x : ℝ) (hx : x∈Ioo a b) :=
    pathHeatSectionwiseNativeWiener_differentiation μ hab.le d C hsource ι c dc δ W hc hdcc hstrict hroot hdc x hx
  have hf := fun x hx=>(hderiv x hx).2.1
  have hg := fun x hx=>(hderiv x hx).2.2
  have he := pathHeat_endpoint_derivatives _ _ a b hab hm.1.continuousOn hm.2.1.continuousOn hf
  have hl := pathHeat_endpoint_derivatives _ _ a b hab hm.2.2.1.continuousOn hm.2.2.2.continuousOn hg
  exact ⟨contDiffOn_one_of_hasDerivAt_of_continuous _ _ a b hm.2.1 hf,
    contDiffOn_one_of_hasDerivAt_of_continuous _ _ a b hm.2.2.2 hg,he.1,he.2,hl.1,hl.2⟩

end HexagonPaper
