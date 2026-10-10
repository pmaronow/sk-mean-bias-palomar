module
public import QuantitativeFollowup.FollowupCavityNativeComparison
public import QuantitativeFollowup.AnisotropicRecordedBinaryFreshLaw
public import QuantitativeFollowup.FourDescendantNativeLaw
public import QuantitativeFollowup.FollowupCavityThreeNativeComparison

@[expose] public section

/-! The native four-descendant law is the actual four-sibling
observation genealogy, preserving every terminal spin. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityFourObservationTree : FiniteTerminalGenealogy 2 :=
  .advance (.fork (.fork (.advance .leaf) (.advance .leaf)) (.fork (.advance .leaf) (.advance .leaf)))

theorem cavityFourObservationTree_spin_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    (anisotropicRecordedProfileTreeKernel D μ (anisotropicBinaryObservationSchedule p)
      cavityFourObservationTree).map (finiteCascadeRecordTerminalSpins cavityFourObservationTree)=
      (((anisotropicObservationTerminalSpinKernel D μ p) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ p)) ×ₖ
        ((anisotropicObservationTerminalSpinKernel D μ p) ×ₖ
          (anisotropicObservationTerminalSpinKernel D μ p))) ∘ₖ anisotropicObservationTransition D μ 0 p := by
  let K:=((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
    (measurable_anisotropicObservationParameter D))
  let A:=(Kernel.id ×ₖ K) ∘ₖ anisotropicObservationTransition D μ p 1
  change ((Kernel.id ×ₖ ((A ×ₖ A) ×ₖ (A ×ₖ A))) ∘ₖ anisotropicObservationTransition D μ 0 p).map
    ((Prod.map (Prod.map Prod.snd Prod.snd) (Prod.map Prod.snd Prod.snd)) ∘ Prod.snd)=_
  rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd
      ((measurable_snd.prodMap measurable_snd).prodMap (measurable_snd.prodMap measurable_snd)),
    ←Kernel.snd_eq,Kernel.snd_prod,←Kernel.map_prod_map _ _
      (measurable_snd.prodMap measurable_snd) (measurable_snd.prodMap measurable_snd),
    ←Kernel.map_prod_map _ _ measurable_snd measurable_snd]
  have hA : A.map Prod.snd=anisotropicObservationTerminalSpinKernel D μ p := by
    rw [←Kernel.snd_eq]
    change ((Kernel.id ×ₖ K) ∘ₖ anisotropicObservationTransition D μ p 1).snd=_
    rw [Kernel.snd_comp,Kernel.snd_prod]
    rfl
  simp only [hA]

theorem cavityFourDescendantLaw_snd_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (cavityFourDescendantLaw D μ a q).snd=
      (((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) ×ₖ
        ((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
          (anisotropicObservationTerminalSpinKernel D μ q))) ∘ₘ
        ((anisotropicMeasureSampleLaw D μ a).map (anisotropicNativeObservation D μ q)) := by
  have he : cavityFourDescendantLaw D μ a q=
      (anisotropicMeasureSpinPathLaw D μ a) ⊗ₘ
        ((((anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst)) ×ₖ
        ((anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst))) ×ₖ
        (((anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst)) ×ₖ
        ((anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst)))) := by
    apply Measure.compProd_congr
    filter_upwards [anisotropicFreshTerminalSpinKernel_eq_native_continuation D μ a q] with p hp
    simp only [Kernel.prod_apply,Kernel.comap_apply]
    rw [hp]
  rw [he,Measure.snd_compProd]
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map ((Kernel.prod (Kernel.prod _ _) (Kernel.prod _ _)).measurable_coe hA)
      (measurable_anisotropicNativeObservation D μ q)]
  have hh:=congrArg (fun P : Measure (AnisotropicDisorderBrownianSample n)=>
      ∫⁻p,(((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) ×ₖ
        ((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
          (anisotropicObservationTerminalSpinKernel D μ q))) (anisotropicNativeObservation D μ q p) A∂P)
    (anisotropicMeasureSpinPathLaw_fst D μ a)
  rw [Measure.fst] at hh
  have hm : Measurable (fun p : AnisotropicDisorderBrownianSample n=>
      (((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) ×ₖ
        ((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
          (anisotropicObservationTerminalSpinKernel D μ q))) (anisotropicNativeObservation D μ q p) A) :=
    ((Kernel.prod (Kernel.prod _ _) (Kernel.prod _ _)).measurable_coe hA).comp (measurable_anisotropicNativeObservation D μ q)
  rw [lintegral_map hm measurable_fst] at hh
  convert hh using 1
  simp only [Kernel.prod_apply,Kernel.comap_apply]

theorem cavityFourObservationTree_spin_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    (anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p)
      cavityFourObservationTree).map (finiteCascadeRecordTerminalSpins cavityFourObservationTree ∘ Prod.snd)=
      (cavityFourDescendantLaw D μ a p).snd := by
  rw [anisotropicRecordedProfileTreeLaw,Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ ((measurable_finiteCascadeRecordTerminalSpins cavityFourObservationTree).comp measurable_snd),
    Kernel.map_comp_right _ measurable_snd (measurable_finiteCascadeRecordTerminalSpins cavityFourObservationTree),
    ←Kernel.snd_eq,Kernel.snd_prod,cavityFourObservationTree_spin_kernel,
    ←Measure.comp_assoc,←anisotropicNativeObservation_law,cavityFourDescendantLaw_snd_native]
  rfl

theorem cavityFourObservation_energy_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) (F : CavityFourTerminalSpins n→ℝ) :
    (∫z : CavityPathRecordSpace cavityFourObservationTree n,
      F (finiteCascadeRecordTerminalSpins cavityFourObservationTree z.2)
      ∂(anisotropicRecordedEnergyProbability D μ a (anisotropicBinaryObservationSchedule p)
        cavityFourObservationTree:Measure (CavityPathRecordSpace cavityFourObservationTree n)))=
      ∫z,F z.2 ∂cavityFourDescendantLaw D μ a p := by
  let Ft : TerminalSpins (Configuration n) cavityFourObservationTree→ℝ:=F
  have hF:Measurable Ft:=measurable_of_finite Ft
  change (∫z : CavityPathRecordSpace cavityFourObservationTree n,
    Ft (finiteCascadeRecordTerminalSpins cavityFourObservationTree z.2)
      ∂(anisotropicRecordedEnergyProbability D μ a (anisotropicBinaryObservationSchedule p)
        cavityFourObservationTree:Measure (CavityPathRecordSpace cavityFourObservationTree n)))=
    ∫z,Ft z.2 ∂cavityFourDescendantLaw D μ a p
  rw [anisotropicRecordedEnergyProbability_measure,integral_map
    (f:=fun z : CavityPathRecordSpace cavityFourObservationTree n=>
      Ft (finiteCascadeRecordTerminalSpins cavityFourObservationTree z.2))
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) cavityFourObservationTree)).aemeasurable
    (hF.comp ((measurable_finiteCascadeRecordTerminalSpins cavityFourObservationTree).comp measurable_snd)).aestronglyMeasurable]
  change (∫z,Ft (finiteCascadeRecordTerminalSpins cavityFourObservationTree z.2)
    ∂anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p)
      cavityFourObservationTree)=_
  have hh:=integral_map (μ:=anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p) cavityFourObservationTree)
    ((measurable_finiteCascadeRecordTerminalSpins cavityFourObservationTree).comp measurable_snd).aemeasurable hF.aestronglyMeasurable
  rw [cavityFourObservationTree_spin_law] at hh
  exact hh.symm.trans (integral_map (μ:=cavityFourDescendantLaw D μ a p)
    measurable_snd.aemeasurable (measurable_of_finite F).aestronglyMeasurable)

end QuantitativeFollowup
