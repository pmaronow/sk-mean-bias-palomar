module
public import FourPapersCommon.FiniteCascadeTreeRecords
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-! Transport of complete finite observation genealogies through a measurable
field map. Every retained observation is transported, and product forks
remain conditionally independent. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable {E F S : Type} [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace S]

@[reducible] def observationTreeMap (φ : E→F) : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    Records E S T→Records F S T
  | _, .leaf => id
  | _, .advance T => Prod.map φ (observationTreeMap φ T)
  | _, .fork T U => Prod.map (observationTreeMap φ T) (observationTreeMap φ U)

theorem measurable_observationTreeMap (φ : E→F) (hφ : Measurable φ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) : Measurable (observationTreeMap φ (S:=S) T) := by
  induction T with
  | leaf => exact measurable_id
  | advance T ih => exact hφ.prodMap ih
  | fork T U ihT ihU => exact ihT.prodMap ihU

@[reducible] def observationTreeKernel (κ : ℕ→Kernel E E) (θ : Kernel E S) :
    {j : ℕ}→(T : FiniteTerminalGenealogy j)→Kernel E (Records E S T)
  | _, .leaf => θ
  | _, @FiniteTerminalGenealogy.advance j T => (Kernel.id ×ₖ observationTreeKernel κ θ T) ∘ₖ κ j
  | _, .fork T U => observationTreeKernel κ θ T ×ₖ observationTreeKernel κ θ U

theorem observationTreeKernel_markov (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (θ : Kernel E S) [IsMarkovKernel θ] {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsMarkovKernel (observationTreeKernel κ θ T) := by
  induction T with
  | leaf => exact inferInstance
  | @advance j T ih =>
      haveI:=ih
      haveI:=hκ j
      change IsMarkovKernel ((_ ×ₖ _) ∘ₖ _)
      infer_instance
  | fork T U ihT ihU =>
      haveI:=ihT
      haveI:=ihU
      change IsMarkovKernel (_ ×ₖ _)
      infer_instance

private theorem comp_comap_observation {A B C D : Type} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (κ : Kernel A B) (η : Kernel B C) (f : D→A) (hf : Measurable f) :
    (η ∘ₖ κ).comap f hf=η ∘ₖ (κ.comap f hf) := by
  rw [←Kernel.comp_deterministic_eq_comap,←Kernel.comp_deterministic_eq_comap,Kernel.comp_assoc]

theorem observationTreeKernel_map (κ : ℕ→Kernel E E) (hκ : ∀j,IsMarkovKernel (κ j))
    (η : ℕ→Kernel F F) (hη : ∀j,IsMarkovKernel (η j))
    (θ : Kernel E S) [IsMarkovKernel θ] (ζ : Kernel F S) [IsMarkovKernel ζ]
    (φ : E→F) (hφ : Measurable φ) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hedge : ∀j,j<J→(κ j).map φ=(η j).comap φ hφ)
    (hleaf : θ=ζ.comap φ hφ) :
    (observationTreeKernel κ θ T).map (observationTreeMap φ T)=
      (observationTreeKernel η ζ T).comap φ hφ := by
  induction T with
  | leaf => simpa only [observationTreeKernel,observationTreeMap,Kernel.map_id] using hleaf
  | @advance j T ih =>
      haveI:=observationTreeKernel_markov κ hκ θ T
      haveI:=observationTreeKernel_markov η hη ζ T
      haveI:=hκ j
      haveI:=hη j
      have hi:=ih (fun l hl=>hedge l (by omega))
      simp only [observationTreeKernel,observationTreeMap]
      rw [Kernel.map_comp,←Kernel.map_prod_map _ _ hφ (measurable_observationTreeMap φ hφ T),
        hi,Kernel.id_map hφ,←Kernel.id_comap hφ,←Kernel.comap_prod,
        ←Kernel.comp_map _ _ hφ,hedge j (by omega),←comp_comap_observation]
  | fork T U ihT ihU =>
      haveI:=observationTreeKernel_markov κ hκ θ T
      haveI:=observationTreeKernel_markov κ hκ θ U
      haveI:=observationTreeKernel_markov η hη ζ T
      haveI:=observationTreeKernel_markov η hη ζ U
      simp only [observationTreeKernel,observationTreeMap]
      rw [←Kernel.map_prod_map _ _ (measurable_observationTreeMap φ hφ T)
        (measurable_observationTreeMap φ hφ U),ihT hedge,ihU hedge,←Kernel.comap_prod]

theorem observationJointLaw_map {J : ℕ} (T : FiniteTerminalGenealogy J)
    (P : Measure E) [IsProbabilityMeasure P]
    (κ : Kernel E (Records E S T)) [IsMarkovKernel κ]
    (η : Kernel F (Records F S T)) [IsMarkovKernel η] (φ : E→F) (hφ : Measurable φ)
    (hmap : κ.map (observationTreeMap φ T)=η.comap φ hφ) :
    (P ⊗ₘ κ).map (Prod.map φ (observationTreeMap φ T))=(P.map φ) ⊗ₘ η := by
  rw [Measure.compProd_eq_comp_prod,Measure.map_comp _ _
    (hφ.prodMap (measurable_observationTreeMap φ hφ T)),
    ←Kernel.map_prod_map _ _ hφ (measurable_observationTreeMap φ hφ T),hmap,
    Kernel.id_map hφ,←Kernel.id_comap hφ,←Kernel.comap_prod,
    ←Kernel.comp_deterministic_eq_comap,←Measure.comp_assoc,
    Measure.deterministic_comp_eq_map hφ,←Measure.compProd_eq_comp_prod]

end FourPapersCommon
