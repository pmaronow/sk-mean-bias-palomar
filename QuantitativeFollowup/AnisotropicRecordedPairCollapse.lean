module
public import QuantitativeFollowup.AnisotropicObservationSemigroup
public import QuantitativeFollowup.AnisotropicRecordedProfilePruning
public import QuantitativeFollowup.AnisotropicRecordedBinaryFreshLaw

@[expose] public section

/-! Every pair of distinct descendants has the actual two-fresh law at its
common ancestral level. Intermediate observations are removed by the
proved native restart semigroup, for each incoming disorder and field. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem clock_antitone {q : ℕ→Paper.Overlap} {j : ℕ}
    (hq : ∀i,i<j→q (i+1)≤q i) {a b : ℕ} (hab : a≤b) (hb : b≤j) : q b≤q a := by
  induction hab with
  | refl => exact le_rfl
  | @step b hab ih => exact (hq b (by omega)).trans (ih (by omega))

theorem anisotropicObservationTerminalSpinKernel_before (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q r : Paper.Overlap) (hqr : q≤r) :
    (anisotropicObservationTerminalSpinKernel D μ r) ∘ₖ
      anisotropicObservationTransition D μ q r =
      anisotropicObservationTerminalSpinKernel D μ q := by
  change (((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
    (measurable_anisotropicObservationParameter D)) ∘ₖ anisotropicObservationTransition D μ r 1) ∘ₖ _ = _
  rw [Kernel.comp_assoc,anisotropicObservationTransition_semigroup D μ q r 1 hqr r.property.2]
  rfl

theorem anisotropicRecordedLinearSpinKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (hzero : q 0=1) (j : ℕ)
    (hq : ∀i,i<j→q (i+1)≤q i) :
    (anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree j)).map
      (observationLinearSpin j)=anisotropicObservationTerminalSpinKernel D μ (q j) := by
  induction j with
  | zero =>
      change ((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
        (measurable_anisotropicObservationParameter D)).map id = _
      rw [Kernel.map_id]
      change _=(_ ∘ₖ anisotropicObservationTransition D μ (q 0) 1)
      rw [hzero,anisotropicObservationTransition_same_time,Kernel.comp_id]
  | succ j ih =>
      change (((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q (observationLinearTree j)) ∘ₖ
        anisotropicObservationTransition D μ (q (j+1)) (q j)).map
        ((observationLinearSpin j) ∘ Prod.snd)) = _
      rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd (measurable_observationLinearSpin j),
        ←Kernel.snd_eq,Kernel.snd_prod,ih (fun i hi=>hq i (by omega)),
        anisotropicObservationTerminalSpinKernel_before D μ (q (j+1)) (q j) (hq j (by omega))]

theorem anisotropicRecordedPairSpinKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ→Paper.Overlap) (hzero : q 0=1)
    {j : ℕ} (P : ObservationPairTree j) (hq : ∀i,i<j→q (i+1)≤q i) :
    (anisotropicRecordedProfileTreeKernel D μ q P.tree).map P.spins =
      ((anisotropicObservationTerminalSpinKernel D μ (q P.splitLevel)) ×ₖ
        (anisotropicObservationTerminalSpinKernel D μ (q P.splitLevel))) ∘ₖ
          anisotropicObservationTransition D μ (q j) (q P.splitLevel) := by
  induction P with
  | split j reverse =>
      have hlin:=anisotropicRecordedLinearSpinKernel D μ q hzero j hq
      cases reverse with
      | false =>
          change (_ ×ₖ _).map (Prod.map (observationLinearSpin j) (observationLinearSpin j))=_
          rw [←Kernel.map_prod_map _ _ (measurable_observationLinearSpin j)
            (measurable_observationLinearSpin j),hlin,
            anisotropicObservationTransition_same_time,Kernel.comp_id]
      | true =>
          change (_ ×ₖ _).map (Prod.swap ∘ Prod.map (observationLinearSpin j) (observationLinearSpin j))=_
          rw [Kernel.map_comp_right _ ((measurable_observationLinearSpin j).prodMap
            (measurable_observationLinearSpin j)) measurable_swap,
            ←Kernel.map_prod_map _ _ (measurable_observationLinearSpin j)
              (measurable_observationLinearSpin j),hlin,Kernel.map_prod_swap,
            anisotropicObservationTransition_same_time,Kernel.comp_id]
  | @advance j P ih =>
      change (((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q P.tree) ∘ₖ
        anisotropicObservationTransition D μ (q (j+1)) (q j)).map (P.spins ∘ Prod.snd))=_
      rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd P.measurable_spins,
        ←Kernel.snd_eq,Kernel.snd_prod,ih (fun i hi=>hq i (by omega)),Kernel.comp_assoc,
        anisotropicObservationTransition_semigroup D μ (q (j+1)) (q j) (q P.splitLevel)
          (hq j (by omega)) (clock_antitone (fun i hi=>hq i (by omega)) P.splitLevel_le le_rfl)]

theorem anisotropicRecordedPairSpinLaw (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hzero : q 0=1)
    {j : ℕ} (P : ObservationPairTree j) (hroot : q j=0)
    (hq : ∀i,i<j→q (i+1)≤q i) :
    (anisotropicRecordedProfileTreeLaw D μ a q P.tree).map (P.spins ∘ Prod.snd)=
      (anisotropicBinarySpinProbability D μ a (q P.splitLevel) : Measure _) := by
  rw [anisotropicRecordedProfileTreeLaw,Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ (P.measurable_spins.comp measurable_snd),
    Kernel.map_comp_right _ measurable_snd P.measurable_spins,
    ←Kernel.snd_eq,Kernel.snd_prod,anisotropicRecordedPairSpinKernel D μ q hzero P hq,
    hroot,←Measure.comp_assoc,←anisotropicNativeObservation_law,
    ←anisotropicFreshTerminalPairLaw_pair_marginal,
    anisotropicBinarySpinProbability_eq_fresh_pair]

theorem anisotropicRecordedProfile_leafPair_law (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ→Paper.Overlap) (hzero : q 0=1)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (hroot : q j=0)
    (hq : ∀l,l<j→q (l+1)≤q l) (i k : ObservationLeaf T) (hik : i≠k) :
    (anisotropicRecordedProfileTreeLaw D μ a q T).map
      (fun z=>(observationLeafSpin T i z.2,observationLeafSpin T k z.2))=
      (anisotropicBinarySpinProbability D μ a (q (observationCommonLevel T i k)) : Measure _) := by
  obtain ⟨P,R,hlevel,hspin⟩:=exists_observationPairPruning
    (E:=AnisotropicObservationState n) (S:=Configuration n) T i k hik
  have he : (fun z : AnisotropicObservationState n×
      Records (AnisotropicObservationState n) (Configuration n) T=>
      (observationLeafSpin T i z.2,observationLeafSpin T k z.2))=
      (P.spins ∘ Prod.snd) ∘ Prod.map id (FiniteObservationPruning.project R) := by
    funext z
    exact (congrFun hspin z.2).symm
  rw [he,←Measure.map_map (P.measurable_spins.comp measurable_snd)
    (measurable_id.prodMap (FiniteObservationPruning.measurable_project R)),
    anisotropicRecordedProfileTreeLaw_pruning D μ a q R,
    anisotropicRecordedPairSpinLaw D μ a q hzero P hroot hq,hlevel]

end QuantitativeFollowup
