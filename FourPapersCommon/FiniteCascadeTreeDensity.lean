module
public import FourPapersCommon.FiniteCascadeTreeRecords
public import FourPapersCommon.FiniteStateCascadePosteriorDensity
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section

/-! Exact density of an actual finite Gaussian genealogy relative to the
raw Gaussian continuations and counting measure on terminal spins. Zero
masses and singular Gaussian increments remain part of the construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

@[reducible] def finiteCascadeTreeReferenceKernel
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      Kernel (FiniteStateField S) (Records (FiniteStateField S) S T)
  | _, .leaf => Kernel.const _ Measure.count
  | _, @FiniteTerminalGenealogy.advance j T =>
      (Kernel.id ×ₖ finiteCascadeTreeReferenceKernel L T) ∘ₖ finiteStateGaussianRawKernel (L j)
  | _, .fork T U => finiteCascadeTreeReferenceKernel L T ×ₖ finiteCascadeTreeReferenceKernel L U

theorem isFiniteKernel_finiteCascadeTreeReferenceKernel
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    IsFiniteKernel (finiteCascadeTreeReferenceKernel L T) := by
  induction T with
  | leaf => change IsFiniteKernel (Kernel.const _ (Measure.count : Measure S)); infer_instance
  | @advance j T ih =>
      haveI := ih
      change IsFiniteKernel ((_ ×ₖ _) ∘ₖ _)
      infer_instance
  | fork T U ihT ihU =>
      haveI := ihT
      haveI := ihU
      change IsFiniteKernel (_ ×ₖ _)
      infer_instance

attribute [local instance] isFiniteKernel_finiteCascadeTreeReferenceKernel

@[reducible] def finiteCascadeTreeLogDensity (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) → FiniteStateField S →
      Records (FiniteStateField S) S T → ℝ
  | _, .leaf => fun H σ => H σ + V σ - gtStateLogPartition V H
  | _, @FiniteTerminalGenealogy.advance j T => fun H z =>
      a j * (finiteStateGaussianTerminalCascade V a L j z.1 -
        finiteStateGaussianTerminalCascade V a L (j+1) H) +
          finiteCascadeTreeLogDensity V a L T z.1 z.2
  | _, .fork T U => fun H z =>
      finiteCascadeTreeLogDensity V a L T H z.1 + finiteCascadeTreeLogDensity V a L U H z.2

theorem measurable_finiteCascadeTreeLogDensity (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Measurable (Function.uncurry (finiteCascadeTreeLogDensity V a L T)) := by
  induction T with
  | leaf =>
      apply measurable_from_prod_countable_left
      intro σ
      change Measurable (fun H : FiniteStateField S => (EuclideanSpace.proj σ) H + V σ - gtStateLogPartition V H)
      exact ((EuclideanSpace.proj σ).measurable.add_const (V σ)).sub
        (contDiff_gtStateLogPartition V).continuous.measurable
  | @advance j T ih =>
      have hj := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable
      have hj1 := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L (j+1)).continuous.measurable
      exact (((hj.comp (measurable_fst.comp measurable_snd)).sub
        (hj1.comp measurable_fst)).const_mul _).add (ih.comp measurable_snd)
  | fork T U ihT ihU =>
      exact (ihT.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).add
        (ihU.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))

theorem finiteStateGaussianCascadeKernel_exp_density (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j =
      (finiteStateGaussianRawKernel (L j)).withDensity (fun H Q => ENNReal.ofReal
        (Real.exp (a j * (finiteStateGaussianTerminalCascade V a L j Q -
          finiteStateGaussianTerminalCascade V a L (j+1) H)))) := by
  unfold finiteStateGaussianCascadeKernel finiteStateGaussianStepKernel
  congr 1
  funext H Q
  change ENNReal.ofReal (Real.exp (a j * finiteStateGaussianTerminalCascade V a L j Q) /
    finiteStateGaussianNormalizer (a j) (L j) (finiteStateGaussianTerminalCascade V a L j) H) = _
  rw [finiteStateGaussianNormalizer_terminal_eq_exp V a ha L j H]
  congr 1
  rw [mul_sub, Real.exp_sub]

private theorem prodMkLeft_withDensity {X Y Z : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (κ : Kernel Y Z)
    [IsSFiniteKernel κ] (w : Y → Z → ℝ≥0∞) (hw : Measurable (Function.uncurry w)) :
    Kernel.prodMkLeft X (κ.withDensity w) =
      (Kernel.prodMkLeft X κ).withDensity (fun p z => w p.2 z) := by
  have hw' : Measurable (Function.uncurry (fun p : X × Y => fun z => w p.2 z)) :=
    hw.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  ext p : 1
  rw [Kernel.prodMkLeft_apply, Kernel.withDensity_apply _ hw,
    Kernel.withDensity_apply _ hw', Kernel.prodMkLeft_apply]

private theorem kernel_exp_density_prod {X Y Z : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (κ : Kernel X Y) (η : Kernel X Z)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (f : X → Y → ℝ) (g : X → Z → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) ×ₖ
      (η.withDensity (fun x z => ENNReal.ofReal (Real.exp (g x z)))) =
      (κ ×ₖ η).withDensity (fun x yz => ENNReal.ofReal (Real.exp (f x yz.1 + g x yz.2))) := by
  haveI : IsSFiniteKernel (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) :=
    Kernel.IsSFiniteKernel.withDensity κ (fun x y => ENNReal.ofReal_ne_top)
  haveI : IsSFiniteKernel (η.withDensity (fun x z => ENNReal.ofReal (Real.exp (g x z)))) :=
    Kernel.IsSFiniteKernel.withDensity η (fun x z => ENNReal.ofReal_ne_top)
  ext x : 1
  rw [Kernel.prod_apply, Kernel.withDensity_apply _ hf.exp.ennreal_ofReal,
    Kernel.withDensity_apply _ hg.exp.ennreal_ofReal,
    MeasureTheory.prod_withDensity (by fun_prop) (by fun_prop),
    Kernel.withDensity_apply _ (by fun_prop), Kernel.prod_apply]
  congr 1
  funext yz
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

private theorem kernel_exp_density_compProd {X Y Z : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (κ : Kernel X Y) (η : Kernel (X × Y) Z)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (f : X → Y → ℝ) (g : X × Y → Z → ℝ)
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) ⊗ₖ
      (η.withDensity (fun xy z => ENNReal.ofReal (Real.exp (g xy z)))) =
      (κ ⊗ₖ η).withDensity (fun x yz => ENNReal.ofReal (Real.exp (f x yz.1 + g (x,yz.1) yz.2))) := by
  haveI : IsSFiniteKernel (κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y)))) :=
    Kernel.IsSFiniteKernel.withDensity κ (fun x y => ENNReal.ofReal_ne_top)
  haveI : IsSFiniteKernel (η.withDensity (fun xy z => ENNReal.ofReal (Real.exp (g xy z)))) :=
    Kernel.IsSFiniteKernel.withDensity η (fun xy z => ENNReal.ofReal_ne_top)
  haveI : IsSFiniteKernel ((κ ⊗ₖ η).withDensity (fun x yz => ENNReal.ofReal (Real.exp (f x yz.1)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun x yz => ENNReal.ofReal_ne_top)
  simp only [Kernel.compProd_withDensity (κ:=κ.withDensity (fun x y => ENNReal.ofReal (Real.exp (f x y))))
      (η:=η) (g:=fun xy z => ENNReal.ofReal (Real.exp (g xy z))) hg.exp.ennreal_ofReal,
    Kernel.withDensity_compProd (κ:=κ) (η:=η)
      (g:=fun x y => ENNReal.ofReal (Real.exp (f x y))) hf.exp.ennreal_ofReal]
  ext x : 1
  rw [Kernel.withDensity_apply _ (by fun_prop), Kernel.withDensity_apply _ (by fun_prop),
    Kernel.withDensity_apply _ (by fun_prop), ←MeasureTheory.withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext yz
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rfl

 theorem finiteCascadeTreeRecordKernel_exp_density (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    finiteCascadeTreeRecordKernel V a L T =
      (finiteCascadeTreeReferenceKernel L T).withDensity (fun H z =>
        ENNReal.ofReal (Real.exp (finiteCascadeTreeLogDensity V a L T H z))) := by
  induction T with
  | leaf =>
      change finiteStateGibbsKernel V = (Kernel.const _ (Measure.count : Measure S)).withDensity _
      ext H : 1
      rw [Kernel.withDensity_apply _
        (measurable_finiteCascadeTreeLogDensity V a ha L .leaf).exp.ennreal_ofReal,
        Kernel.const_apply]
      rw [finiteStateGibbsKernel_apply]
      congr 1
      funext σ
      congr 1
      simp only [finiteCascadeTreeLogDensity, gtStateGibbs, gtStateLogPartition]
      rw [Real.exp_sub, Real.exp_log (gtStatePartition_pos V H)]
  | @advance j T ih =>
      haveI := isFiniteKernel_finiteCascadeTreeReferenceKernel L T
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L j
      change (_ ×ₖ _) ∘ₖ _ = ((_ ×ₖ _) ∘ₖ _).withDensity _
      haveI : IsSFiniteKernel ((finiteCascadeTreeReferenceKernel L T).withDensity
          (fun H z => ENNReal.ofReal (Real.exp (finiteCascadeTreeLogDensity V a L T H z)))) :=
        Kernel.IsSFiniteKernel.withDensity _ (fun H z => ENNReal.ofReal_ne_top)
      haveI : IsSFiniteKernel ((finiteStateGaussianRawKernel (L j)).withDensity
          (fun H Q => ENNReal.ofReal (Real.exp (a j *
            (finiteStateGaussianTerminalCascade V a L j Q -
              finiteStateGaussianTerminalCascade V a L (j+1) H))))) :=
        Kernel.IsSFiniteKernel.withDensity _ (fun H Q => ENNReal.ofReal_ne_top)
      simp only [ih, finiteStateGaussianCascadeKernel_exp_density V a ha L j]
      simp only [←Kernel.compProd_prodMkLeft_eq_comp,
        prodMkLeft_withDensity (finiteCascadeTreeReferenceKernel L T)
          (fun H z => ENNReal.ofReal (Real.exp (finiteCascadeTreeLogDensity V a L T H z)))
          (measurable_finiteCascadeTreeLogDensity V a ha L T).exp.ennreal_ofReal,
        finiteStateGaussianCascadeKernel_exp_density V a ha L j]
      exact kernel_exp_density_compProd (finiteStateGaussianRawKernel (L j))
        (Kernel.prodMkLeft (FiniteStateField S) (finiteCascadeTreeReferenceKernel L T))
        (fun H Q => a j * (finiteStateGaussianTerminalCascade V a L j Q -
          finiteStateGaussianTerminalCascade V a L (j+1) H))
        (fun p z => finiteCascadeTreeLogDensity V a L T p.2 z) (by
        exact (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.comp
          measurable_snd).sub ((contDiff_one_finiteStateGaussianTerminalCascade V a ha L (j+1)).continuous.measurable.comp
            measurable_fst)).const_mul _) (by
        exact (measurable_finiteCascadeTreeLogDensity V a ha L T).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  | fork T U ihT ihU =>
      haveI := isFiniteKernel_finiteCascadeTreeReferenceKernel L T
      haveI := isFiniteKernel_finiteCascadeTreeReferenceKernel L U
      change _ ×ₖ _ = (_ ×ₖ _).withDensity _
      rw [ihT, ihU]
      exact kernel_exp_density_prod _ _ _ _
        (measurable_finiteCascadeTreeLogDensity V a ha L T)
        (measurable_finiteCascadeTreeLogDensity V a ha L U)

end FourPapersCommon
