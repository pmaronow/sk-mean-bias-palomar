module
public import QuantitativeFollowup.FollowupCavityNativeComparison
public import QuantitativeFollowup.AnisotropicRecordedBinaryFreshLaw
public import QuantitativeFollowup.ThreeDescendantNativeLaw

@[expose] public section

/-! The native three-descendant law is the actual three-sibling
observation genealogy. Positive moment comparison preserves all marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityThreeObservationTree : FiniteTerminalGenealogy 2 :=
  .advance (.fork (.fork (.advance .leaf) (.advance .leaf)) (.advance .leaf))

theorem anisotropicBinaryObservationSchedule_antitone (q : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule q) := by
  apply antitone_nat_of_succ_le
  intro j
  cases j with
  | zero => exact q.property.2
  | succ j => cases j with
    | zero => exact q.property.1
    | succ j => exact le_refl _

theorem cavityThreeObservationTree_spin_kernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    (anisotropicRecordedProfileTreeKernel D μ (anisotropicBinaryObservationSchedule p)
      cavityThreeObservationTree).map (finiteCascadeRecordTerminalSpins cavityThreeObservationTree)=
      (((anisotropicObservationTerminalSpinKernel D μ p) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ p)) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ p)) ∘ₖ anisotropicObservationTransition D μ 0 p := by
  let K:=((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
    (measurable_anisotropicObservationParameter D))
  let A:=(Kernel.id ×ₖ K) ∘ₖ anisotropicObservationTransition D μ p 1
  change ((Kernel.id ×ₖ ((A ×ₖ A) ×ₖ A)) ∘ₖ anisotropicObservationTransition D μ 0 p).map
    ((Prod.map (Prod.map Prod.snd Prod.snd) Prod.snd) ∘ Prod.snd)=_
  rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd
      ((measurable_snd.prodMap measurable_snd).prodMap measurable_snd),
    ←Kernel.snd_eq,Kernel.snd_prod,←Kernel.map_prod_map _ _
      (measurable_snd.prodMap measurable_snd) measurable_snd,
    ←Kernel.map_prod_map _ _ measurable_snd measurable_snd]
  have hA : A.map Prod.snd=anisotropicObservationTerminalSpinKernel D μ p := by
    rw [←Kernel.snd_eq]
    change ((Kernel.id ×ₖ K) ∘ₖ anisotropicObservationTransition D μ p 1).snd=_
    rw [Kernel.snd_comp,Kernel.snd_prod]
    rfl
  rw [hA]

theorem cavityThreeDescendantLaw_snd_native (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (cavityThreeDescendantLaw D μ a q).snd=
      (((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) ∘ₘ
        ((anisotropicMeasureSampleLaw D μ a).map (anisotropicNativeObservation D μ q)) := by
  have he : cavityThreeDescendantLaw D μ a q=
      (anisotropicMeasureSpinPathLaw D μ a) ⊗ₘ
        ((((anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst)) ×ₖ
        ((anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst))) ×ₖ
        ((anisotropicObservationTerminalSpinKernel D μ q).comap
          (fun p=>anisotropicNativeObservation D μ q p.1)
          ((measurable_anisotropicNativeObservation D μ q).comp measurable_fst))) := by
    apply Measure.compProd_congr
    filter_upwards [anisotropicFreshTerminalSpinKernel_eq_native_continuation D μ a q] with p hp
    simp only [Kernel.prod_apply,Kernel.comap_apply]
    rw [hp]
  rw [he,Measure.snd_compProd]
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map ((Kernel.prod (Kernel.prod _ _) _).measurable_coe hA)
      (measurable_anisotropicNativeObservation D μ q)]
  have hh:=congrArg (fun P : Measure (AnisotropicDisorderBrownianSample n)=>
      ∫⁻p,(((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) (anisotropicNativeObservation D μ q p) A∂P)
    (anisotropicMeasureSpinPathLaw_fst D μ a)
  rw [Measure.fst] at hh
  have hm : Measurable (fun p : AnisotropicDisorderBrownianSample n=>
      (((anisotropicObservationTerminalSpinKernel D μ q) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ q)) (anisotropicNativeObservation D μ q p) A) :=
    ((Kernel.prod (Kernel.prod _ _) _).measurable_coe hA).comp (measurable_anisotropicNativeObservation D μ q)
  rw [lintegral_map hm measurable_fst] at hh
  convert hh using 1
  simp only [Kernel.prod_apply,Kernel.comap_apply]

theorem cavityThreeObservationTree_spin_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    (anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p)
      cavityThreeObservationTree).map (finiteCascadeRecordTerminalSpins cavityThreeObservationTree ∘ Prod.snd)=
      (cavityThreeDescendantLaw D μ a p).snd := by
  rw [anisotropicRecordedProfileTreeLaw,Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ ((measurable_finiteCascadeRecordTerminalSpins cavityThreeObservationTree).comp measurable_snd),
    Kernel.map_comp_right _ measurable_snd (measurable_finiteCascadeRecordTerminalSpins cavityThreeObservationTree),
    ←Kernel.snd_eq,Kernel.snd_prod,cavityThreeObservationTree_spin_kernel,
    ←Measure.comp_assoc,←anisotropicNativeObservation_law,cavityThreeDescendantLaw_snd_native]
  rfl

theorem cavityThreeObservation_energy_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) (F : CavityThreeTerminalSpins n→ℝ) :
    (∫z : CavityPathRecordSpace cavityThreeObservationTree n,
      F (finiteCascadeRecordTerminalSpins cavityThreeObservationTree z.2)
      ∂(anisotropicRecordedEnergyProbability D μ a (anisotropicBinaryObservationSchedule p)
        cavityThreeObservationTree:Measure (CavityPathRecordSpace cavityThreeObservationTree n)))=
      ∫z,F z.2 ∂cavityThreeDescendantLaw D μ a p := by
  let Ft : TerminalSpins (Configuration n) cavityThreeObservationTree→ℝ:=F
  have hF:Measurable Ft:=measurable_of_finite Ft
  change (∫z : CavityPathRecordSpace cavityThreeObservationTree n,
    Ft (finiteCascadeRecordTerminalSpins cavityThreeObservationTree z.2)
      ∂(anisotropicRecordedEnergyProbability D μ a (anisotropicBinaryObservationSchedule p)
        cavityThreeObservationTree:Measure (CavityPathRecordSpace cavityThreeObservationTree n)))=
    ∫z,Ft z.2 ∂cavityThreeDescendantLaw D μ a p
  rw [anisotropicRecordedEnergyProbability_measure,integral_map
    (f:=fun z : CavityPathRecordSpace cavityThreeObservationTree n=>
      Ft (finiteCascadeRecordTerminalSpins cavityThreeObservationTree z.2))
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) cavityThreeObservationTree)).aemeasurable
    (hF.comp ((measurable_finiteCascadeRecordTerminalSpins cavityThreeObservationTree).comp measurable_snd)).aestronglyMeasurable]
  change (∫z,Ft (finiteCascadeRecordTerminalSpins cavityThreeObservationTree z.2)
    ∂anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p)
      cavityThreeObservationTree)=_
  have hh:=integral_map (μ:=anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p) cavityThreeObservationTree)
    ((measurable_finiteCascadeRecordTerminalSpins cavityThreeObservationTree).comp measurable_snd).aemeasurable hF.aestronglyMeasurable
  rw [cavityThreeObservationTree_spin_law] at hh
  exact hh.symm.trans (integral_map (μ:=cavityThreeDescendantLaw D μ a p)
    measurable_snd.aemeasurable (measurable_of_finite F).aestronglyMeasurable)

theorem cavityThreeDescendant_positive_comparison
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (μ:Paper.ParisiMeasure)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(hfloor:a≤Paper.parisiCDF μ 0)
    (p:Paper.Overlap)(F:CavityThreeTerminalSpins (n+1)→ℝ)(hF0:∀σ,0≤F σ)
    (u v:ℝ)(hu:u∈Icc (0:ℝ) 1)(hv:v∈Icc (0:ℝ) 1):
    (∫z,F z.2 ∂cavityThreeDescendantLaw (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p) ≤
      Real.exp (43*β^2)*(∫z,F z.2 ∂cavityThreeDescendantLaw (followupCavitySpinModel n β ρ hβ hρ v hv) μ a p) := by
  have hh:=cavityNative_positive_spin_comparison hn β ρ hβ hρ μ a ha hfloor
    (anisotropicBinaryObservationSchedule p) (anisotropicBinaryObservationSchedule_antitone p)
    2 (by norm_num) rfl rfl cavityThreeObservationTree F hF0 u v hu hv
  rw [cavityThreeObservation_energy_integral,cavityThreeObservation_energy_integral] at hh
  convert hh using 1 <;> norm_num [cavityThreeObservationTree,asGenealogy,FiniteCascadeGenealogy.leafCount] <;> ring <;> simp

end QuantitativeFollowup
