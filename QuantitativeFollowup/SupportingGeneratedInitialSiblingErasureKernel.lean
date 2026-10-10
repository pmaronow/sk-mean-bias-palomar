module
public import QuantitativeFollowup.SupportingGeneratedInitialSiblingErasureGeometry

@[expose] public section

/-! The true native transition semigroup removes unary observations from
an initial tree whose forks all occur at one physical level. The proof
retains the complete terminal test, rather than only pair marginals. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

@[reducible] def printedGeneratedInitialSiblingConditionalKernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    {J : ℕ} → (T : FiniteTerminalGenealogy J) →
      Kernel (AnisotropicObservationState n) (TerminalSpins (Configuration n) T)
  | _, .leaf => anisotropicObservationTerminalSpinKernel D μ p
  | _, .advance T => printedGeneratedInitialSiblingConditionalKernel D μ p T
  | _, .fork T U => printedGeneratedInitialSiblingConditionalKernel D μ p T ×ₖ
      printedGeneratedInitialSiblingConditionalKernel D μ p U

instance printedGeneratedInitialSiblingConditionalKernel_markov
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (p : Paper.Overlap)
    {J : ℕ} (T : FiniteTerminalGenealogy J) :
    IsMarkovKernel (printedGeneratedInitialSiblingConditionalKernel D μ p T) := by
  induction T with
  | leaf =>
      change IsMarkovKernel (anisotropicObservationTerminalSpinKernel D μ p)
      infer_instance
  | advance T ih => exact ih
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      exact inferInstanceAs (IsMarkovKernel
        (printedGeneratedInitialSiblingConditionalKernel D μ p T ×ₖ
          printedGeneratedInitialSiblingConditionalKernel D μ p U))

def printedGeneratedInitialTerminalKernel (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    Kernel (AnisotropicObservationState n) (TerminalSpins (Configuration n) T) :=
  (anisotropicRecordedProfileTreeKernel D μ q T).map (finiteCascadeRecordTerminalSpins T)

private theorem terminalKernel_advance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    printedGeneratedInitialTerminalKernel D μ q (.advance T) =
      printedGeneratedInitialTerminalKernel D μ q T ∘ₖ
        anisotropicObservationTransition D μ (q (J+1)) (q J) := by
  change (((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
    anisotropicObservationTransition D μ (q (J+1)) (q J)).map
      ((finiteCascadeRecordTerminalSpins T) ∘ Prod.snd)) = _
  rw [Kernel.map_comp,Kernel.map_comp_right _ measurable_snd
    (measurable_finiteCascadeRecordTerminalSpins T),←Kernel.snd_eq,Kernel.snd_prod]
  rfl

private theorem terminalKernel_fork (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) {J : ℕ}
    (T U : FiniteTerminalGenealogy J) :
    printedGeneratedInitialTerminalKernel D μ q (.fork T U) =
      printedGeneratedInitialTerminalKernel D μ q T ×ₖ
        printedGeneratedInitialTerminalKernel D μ q U := by
  change (anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
    anisotropicRecordedProfileTreeKernel D μ q U).map
      (Prod.map (finiteCascadeRecordTerminalSpins T) (finiteCascadeRecordTerminalSpins U)) = _
  rw [←Kernel.map_prod_map _ _ (measurable_finiteCascadeRecordTerminalSpins T)
    (measurable_finiteCascadeRecordTerminalSpins U)]
  rfl

private theorem siblingConditional_before (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hno : printedGeneratedInitialSiblingErasure T = .single)
    (q r : Paper.Overlap) (hqr : q ≤ r) :
    printedGeneratedInitialSiblingConditionalKernel D μ r T ∘ₖ
      anisotropicObservationTransition D μ q r =
        printedGeneratedInitialSiblingConditionalKernel D μ q T := by
  induction T with
  | leaf => exact anisotropicObservationTerminalSpinKernel_before D μ q r hqr
  | advance T ih => exact ih hno
  | fork T U ihT ihU => cases hno

private theorem terminalKernel_without_forks (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) (hq : Antitone q)
    (hzero : q 0 = 1) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hno : printedGeneratedInitialSiblingErasure T = .single) :
    printedGeneratedInitialTerminalKernel D μ q T =
      printedGeneratedInitialSiblingConditionalKernel D μ (q J) T := by
  induction T with
  | leaf =>
      change ((anisotropicTerminalSpinKernel D).comap (anisotropicObservationParameter D)
        (measurable_anisotropicObservationParameter D)).map id = _
      rw [Kernel.map_id]
      change _ = _ ∘ₖ anisotropicObservationTransition D μ (q 0) 1
      rw [hzero,anisotropicObservationTransition_same_time,Kernel.comp_id]
  | @advance j T ih =>
      rw [terminalKernel_advance,ih hno]
      exact siblingConditional_before D μ T hno _ _ (hq (Nat.le_succ j))
  | fork T U ihT ihU => cases hno

theorem printedGeneratedInitialTerminalKernel_before_sibling
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (p : Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hfork : printedGeneratedInitialForksAt q p T) (htop : q J ≤ p) :
    printedGeneratedInitialTerminalKernel D μ q T =
      printedGeneratedInitialSiblingConditionalKernel D μ p T ∘ₖ
        anisotropicObservationTransition D μ (q J) p := by
  induction T with
  | leaf =>
      have hno : printedGeneratedInitialSiblingErasure (.leaf : FiniteTerminalGenealogy 0) = .single := rfl
      rw [terminalKernel_without_forks D μ q hq hzero .leaf hno]
      exact (siblingConditional_before D μ .leaf hno _ _ htop).symm
  | @advance j T ih =>
      by_cases hs : printedGeneratedInitialSiblingErasure T = .single
      · rw [terminalKernel_without_forks D μ q hq hzero (.advance T) hs]
        exact (siblingConditional_before D μ (.advance T) hs _ _ htop).symm
      · obtain ⟨d,hd,hp⟩ := printedGeneratedInitialSiblingErasure_has_fork T q p hfork hs
        have hchild : q j ≤ p := (hq hd).trans_eq hp
        rw [terminalKernel_advance,ih hfork hchild,Kernel.comp_assoc,
          anisotropicObservationTransition_semigroup D μ (q (j+1)) (q j) p
            (hq (Nat.le_succ j)) hchild]
  | @fork j T U ihT ihU =>
      have hself : q j ≤ p := le_of_eq hfork.1
      have ht := ihT hfork.2.1 hself
      have hu := ihU hfork.2.2 hself
      have htrans : anisotropicObservationTransition D μ (q j) p = Kernel.id := by
        rw [hfork.1,anisotropicObservationTransition_same_time]
      have ht' : printedGeneratedInitialTerminalKernel D μ q T =
          printedGeneratedInitialSiblingConditionalKernel D μ p T := by
        exact ht.trans (by rw [htrans,Kernel.comp_id])
      have hu' : printedGeneratedInitialTerminalKernel D μ q U =
          printedGeneratedInitialSiblingConditionalKernel D μ p U := by
        exact hu.trans (by rw [htrans,Kernel.comp_id])
      calc
        _ = printedGeneratedInitialTerminalKernel D μ q T ×ₖ
            printedGeneratedInitialTerminalKernel D μ q U := terminalKernel_fork D μ q T U
        _ = printedGeneratedInitialSiblingConditionalKernel D μ p T ×ₖ
            printedGeneratedInitialSiblingConditionalKernel D μ p U :=
          congrArg₂ (fun KT KU => KT ×ₖ KU) ht' hu'
        _ = _ := by
          change (_ ×ₖ _) = (_ ×ₖ _) ∘ₖ anisotropicObservationTransition D μ (q j) p
          rw [htrans,Kernel.comp_id]

theorem printedGeneratedInitialSiblingConditionalKernel_terminal_equiv
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (p : Paper.Overlap)
    {J : ℕ} (T : FiniteTerminalGenealogy J) :
    (printedGeneratedInitialSiblingConditionalKernel D μ p T).map
      (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T) =
        printedGeneratedInitialSiblingConditionalKernel D μ p
          (printedGeneratedInitialSiblingErasure T).tree := by
  induction T with
  | leaf => exact Kernel.map_id _
  | advance T ih => exact ih
  | fork T U ihT ihU =>
      change (_ ×ₖ _).map (Prod.map (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T)
        (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) U)) = _ ×ₖ _
      rw [←Kernel.map_prod_map _ _ (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T).measurable
        (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) U).measurable,ihT,ihU]

private theorem siblingTree_forks (p : Paper.Overlap) (S : CavityGeneratedSiblingShape) :
    printedGeneratedInitialForksAt (anisotropicBinaryObservationSchedule p) p (.advance S.tree) := by
  induction S with
  | single => trivial
  | fork S T ihS ihT => exact ⟨rfl,ihS,ihT⟩

theorem printedGeneratedInitialSiblingErasure_terminal_kernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hzero : q 0 = 1)
    (p : Paper.Overlap) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (hfork : printedGeneratedInitialForksAt q p T) (htop : q J = 0) :
    (anisotropicRecordedProfileTreeKernel D μ q T).map
      ((printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T) ∘ finiteCascadeRecordTerminalSpins T) =
    printedGeneratedInitialTerminalKernel D μ (anisotropicBinaryObservationSchedule p)
      (.advance (printedGeneratedInitialSiblingErasure T).tree) := by
  have hstep : q J ≤ p := by rw [htop]; exact p.property.1
  rw [Kernel.map_comp_right _ (measurable_finiteCascadeRecordTerminalSpins T)
    (printedGeneratedInitialSiblingTerminalEquiv (A:=Configuration n) T).measurable]
  change (printedGeneratedInitialTerminalKernel D μ q T).map _ = _
  rw [printedGeneratedInitialTerminalKernel_before_sibling D μ q hq hzero p T hfork hstep,
    Kernel.map_comp,printedGeneratedInitialSiblingConditionalKernel_terminal_equiv,htop]
  have hQ : Antitone (anisotropicBinaryObservationSchedule p) := by
    intro i j hij
    cases i with
    | zero => exact (anisotropicBinaryObservationSchedule p j).property.2
    | succ i => cases j with
      | zero => omega
      | succ j => cases i with
        | zero => cases j with
          | zero => exact le_rfl
          | succ j => exact p.property.1
        | succ i => cases j with
          | zero => omega
          | succ j => exact le_rfl
  rw [printedGeneratedInitialTerminalKernel_before_sibling D μ _ hQ rfl p
    (.advance (printedGeneratedInitialSiblingErasure T).tree)
    (siblingTree_forks p _) p.property.1]
  rfl

end QuantitativeFollowup
