module
public import FourPapersCommon.FiniteCascadeTreeReferenceFlatGaussian
public import FourPapersCommon.FiniteCascadeTreeGaussianDensity

@[expose] public section

/-! The reference law including its Gaussian root is the literal pushforward
of one independent Euclidean Gaussian and terminal counting spins. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
attribute [local instance] isProbabilityMeasure_gaussianCoordinateLaw
  isFiniteMeasure_terminalSpinCountingLaw isFiniteKernel_finiteCascadeTreeReferenceKernel
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteCascadeTreeReferenceKernel_joint_flat_law
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (ρ : Measure (FiniteStateField S)) [SFinite ρ] :
    (ρ.prod ((stdGaussian (FiniteStateGaussianInput (GaussianCoordinateIndex I T))).prod
      (terminalSpinCountingLaw S T))).map
      (fun p => (p.1,finiteCascadeTreeReferenceFlatRecord L T p.1 p.2)) =
      ρ ⊗ₘ finiteCascadeTreeReferenceKernel L T := by
  have hm : Measurable (fun p : FiniteStateField S ×
      (FiniteStateGaussianInput (GaussianCoordinateIndex I T) × TerminalSpins S T) =>
      (p.1,finiteCascadeTreeReferenceFlatRecord L T p.1 p.2)) :=
    measurable_fst.prodMk (measurable_finiteCascadeTreeReferenceFlatRecord L T)
  ext s hs
  rw [Measure.map_apply hm hs,Measure.prod_apply (hm hs),Measure.compProd_apply hs]
  apply lintegral_congr
  intro H
  rw [←finiteCascadeTreeReferenceKernel_eq_flat_gaussian L T H,
    Measure.map_apply
      (show Measurable (finiteCascadeTreeReferenceFlatRecord L T H) from
        (measurable_finiteCascadeTreeReferenceFlatRecord L T).comp measurable_prodMk_left)
      (measurable_prodMk_left hs)]
  rfl

def finiteCascadeTreeReferenceRootFlatRecord
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S)
    (p : FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T) × TerminalSpins S T) :
    FiniteStateField S × Records (FiniteStateField S) S T :=
  let Q := H + R (finiteGaussianLeft p.1)
  (Q, finiteCascadeTreeReferenceFlatRecord L T Q (finiteGaussianRight p.1,p.2))

theorem measurable_finiteCascadeTreeReferenceRootFlatRecord
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    Measurable (finiteCascadeTreeReferenceRootFlatRecord L T R H) := by
  have hQ : Measurable (fun p : FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T) ×
      TerminalSpins S T => H + R (finiteGaussianLeft p.1)) := by fun_prop
  have hr : Measurable (finiteGaussianRight (I:=J) (J:=GaussianCoordinateIndex I T)) :=
    finiteGaussianRight.continuous.measurable
  exact hQ.prodMk ((measurable_finiteCascadeTreeReferenceFlatRecord L T).comp
    (hQ.prodMk ((hr.comp measurable_fst).prodMk measurable_snd)))

theorem finiteCascadeTreeGaussianReferenceLaw_eq_flat_gaussian
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H : FiniteStateField S) :
    ((stdGaussian (FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T))).prod
      (terminalSpinCountingLaw S T)).map (finiteCascadeTreeReferenceRootFlatRecord L T R H) =
      finiteCascadeTreeGaussianReferenceLaw L T R H := by
  let shift : FiniteStateGaussianInput J → FiniteStateField S := fun z => H + R z
  have hshift : Measurable shift := by dsimp [shift]; fun_prop
  have hs := stdGaussian_map_finiteGaussianSplit (I:=J) (J:=GaussianCoordinateIndex I T)
  have hs' := Measure.map_prod_map
    (stdGaussian (FiniteStateGaussianInput (J ⊕ GaussianCoordinateIndex I T)))
    (terminalSpinCountingLaw S T) measurable_finiteGaussianSplit measurable_id
  rw [hs,Measure.map_id] at hs'
  have hassoc := Measure.prodAssoc_prod (μ:=stdGaussian (FiniteStateGaussianInput J))
    (ν:=stdGaussian (FiniteStateGaussianInput (GaussianCoordinateIndex I T)))
    (τ:=terminalSpinCountingLaw S T)
  have hrec : Measurable (fun p : FiniteStateGaussianInput J ×
      (FiniteStateGaussianInput (GaussianCoordinateIndex I T) × TerminalSpins S T) =>
      (shift p.1,finiteCascadeTreeReferenceFlatRecord L T (shift p.1) p.2)) :=
    (hshift.comp measurable_fst).prodMk
      ((measurable_finiteCascadeTreeReferenceFlatRecord L T).comp
        ((hshift.comp measurable_fst).prodMk measurable_snd))
  have hp : Measurable (fun p :
      (FiniteStateGaussianInput J × FiniteStateGaussianInput (GaussianCoordinateIndex I T)) ×
        TerminalSpins S T =>
      (shift p.1.1,finiteCascadeTreeReferenceFlatRecord L T (shift p.1.1) (p.1.2,p.2))) :=
    hrec.comp MeasurableEquiv.prodAssoc.measurable
  calc
    _ = (((stdGaussian (FiniteStateGaussianInput J)).prod
        (stdGaussian (FiniteStateGaussianInput (GaussianCoordinateIndex I T)))).prod
          (terminalSpinCountingLaw S T)).map
          (fun p => (shift p.1.1,finiteCascadeTreeReferenceFlatRecord L T (shift p.1.1) (p.1.2,p.2))) := by
      rw [hs',Measure.map_map hp
        (measurable_finiteGaussianSplit.prodMap measurable_id)]
      rfl
    _ = ((stdGaussian (FiniteStateGaussianInput J)).prod
        ((stdGaussian (FiniteStateGaussianInput (GaussianCoordinateIndex I T))).prod
          (terminalSpinCountingLaw S T))).map
          (fun p => (shift p.1,finiteCascadeTreeReferenceFlatRecord L T (shift p.1) p.2)) := by
      rw [←hassoc,Measure.map_map hrec MeasurableEquiv.prodAssoc.measurable]
      rfl
    _ = _ := by
      ext s hset
      rw [Measure.map_apply hrec hset,Measure.prod_apply (hrec hset)]
      change _ = ((finiteStateGaussianRawKernel R H) ⊗ₘ finiteCascadeTreeReferenceKernel L T) s
      rw [Measure.compProd_apply hset,finiteStateGaussianRawKernel_apply,
        lintegral_map (Kernel.measurable_kernel_prodMk_left hset) hshift]
      apply lintegral_congr
      intro z
      rw [←finiteCascadeTreeReferenceKernel_eq_flat_gaussian L T (shift z),
        Measure.map_apply
          (show Measurable (finiteCascadeTreeReferenceFlatRecord L T (shift z)) from
            (measurable_finiteCascadeTreeReferenceFlatRecord L T).comp measurable_prodMk_left)
          (measurable_prodMk_left hset)]
      rfl

end FourPapersCommon
