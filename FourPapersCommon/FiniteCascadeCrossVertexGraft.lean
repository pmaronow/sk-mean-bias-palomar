module
public import FourPapersCommon.FiniteCascadeVertexGraftLaw
public import FourPapersCommon.FiniteCascadeGraftVertices
public import FourPapersCommon.FiniteCascadeCrossVertexMarks

@[expose] public section

/-! Two independent conditional terminal marks are genuine terminal leaves
of an explicit larger tree, including coincident marked vertices. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def finiteCascadeCrossVertexGraft {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) : FiniteTerminalGenealogy j :=
  finiteCascadeVertexGraft (finiteCascadeGraftVertexEmbed v w)

@[reducible] def finiteCascadeCrossGraftExtract {E S : Type}
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeCrossVertexGraft v w)) : Records E S T × (S × S) :=
  let z' := finiteCascadeGraftRecordExtract (finiteCascadeGraftVertexEmbed v w) z
  let z'' := finiteCascadeGraftRecordExtract v z'.1
  (z''.1,(z''.2,z'.2))

theorem measurable_finiteCascadeCrossGraftExtract {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S]
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    Measurable (finiteCascadeCrossGraftExtract (E:=E) (S:=S) v w) := by
  have h1 := measurable_finiteCascadeGraftRecordExtract (E:=E) (S:=S)
    (finiteCascadeGraftVertexEmbed v w)
  have h2 := (measurable_finiteCascadeGraftRecordExtract (E:=E) (S:=S) v).comp h1.fst
  exact h2.fst.prodMk (h2.snd.prodMk h1.snd)

theorem finiteCascadeCrossVertexGraft_leafCount {j : ℕ} {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeCrossVertexGraft v w)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+2 := by
  rw [finiteCascadeCrossVertexGraft, finiteCascadeVertexGraft_leafCount,
    finiteCascadeVertexGraft_leafCount]

theorem finiteCascadeCrossVertexGraft_branchSum (χ : ℕ → ℝ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    finiteCascadeUnweightedBranchSum χ (finiteCascadeCrossVertexGraft v w) =
      finiteCascadeUnweightedBranchSum χ T+χ v.depth+χ w.depth := by
  rw [finiteCascadeCrossVertexGraft, finiteCascadeVertexGraft_branchSum,
    finiteCascadeVertexGraft_branchSum, finiteCascadeGraftVertexEmbed_depth]

variable {S I : Type} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

private theorem measurable_cross_mark_inner (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (w : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (G : Records (FiniteStateField S) S T × (S × S) → ℝ≥0∞)
    (hG : Measurable G) :
    Measurable (fun z : Records (FiniteStateField S) S T × S =>
      ∫⁻τ, G (z.1,(z.2,τ))
        ∂finiteStateCascadeGibbsKernel V a L w.depth (w.field H z.1)) := by
  let κ : Kernel (Records (FiniteStateField S) S T × S) S :=
    (finiteCascadeSingleVertexKernel (S:=S) (I:=I) V a L w).comap
    (fun z : Records (FiniteStateField S) S T × S => (H,z.1))
      (measurable_const.prodMk measurable_fst)
  haveI := finiteCascadeSingleVertexKernel_markov V a ha L w
  haveI : IsMarkovKernel κ := inferInstance
  have hm : Measurable (fun z : (Records (FiniteStateField S) S T × S) × S =>
      G (z.1.1,(z.1.2,z.2))) := by
    simpa only [Function.comp_def] using hG.comp
      ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  convert! hm.lintegral_kernel_prod_right' (κ:=κ) using 1

theorem lintegral_finiteCascadeCrossVertexGraft (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (H : FiniteStateField S) (G : Records (FiniteStateField S) S T × (S × S) → ℝ≥0∞)
    (hG : Measurable G) :
    (∫⁻z, G (finiteCascadeCrossGraftExtract v w z)
        ∂finiteCascadeTreeRecordKernel V a L (finiteCascadeCrossVertexGraft v w) H) =
      ∫⁻z, ∫⁻σ, ∫⁻τ, G (z,(σ,τ))
        ∂finiteStateCascadeGibbsKernel V a L w.depth (w.field H z)
        ∂finiteStateCascadeGibbsKernel V a L v.depth (v.field H z)
        ∂finiteCascadeTreeRecordKernel V a L T H := by
  have hm : Measurable (fun z : Records (FiniteStateField S) S
      (finiteCascadeVertexGraft v) × S =>
      G ((finiteCascadeGraftRecordExtract v z.1).1,
        ((finiteCascadeGraftRecordExtract v z.1).2,z.2))) := by
    have he := (measurable_finiteCascadeGraftRecordExtract (E:=FiniteStateField S) (S:=S) v).comp
      (measurable_fst : Measurable (Prod.fst :
        Records (FiniteStateField S) S (finiteCascadeVertexGraft v) × S → _))
    simpa only [Function.comp_def] using hG.comp (he.fst.prodMk (he.snd.prodMk measurable_snd))
  change (∫⁻z, (fun z => G ((finiteCascadeGraftRecordExtract v z.1).1,
      ((finiteCascadeGraftRecordExtract v z.1).2,z.2)))
      (finiteCascadeGraftRecordExtract (finiteCascadeGraftVertexEmbed v w) z) ∂_) = _
  rw [lintegral_finiteCascadeVertexGraft V a ha L _ H _ hm]
  simp_rw [finiteCascadeGraftVertexEmbed_depth, finiteCascadeGraftVertexEmbed_field]
  exact lintegral_finiteCascadeVertexGraft V a ha L v H _
    (measurable_cross_mark_inner V a ha L w H G hG)

theorem finiteCascadeCrossVertexGraft_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T) :
    (finiteCascadeTreeRecordKernel V a L (finiteCascadeCrossVertexGraft v w)).map
      (finiteCascadeCrossGraftExtract v w) =
      finiteCascadeTreeRecordKernel V a L T ⊗ₖ finiteCascadeCrossVertexPairKernel V a L v w := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := finiteCascadeCrossVertexPairKernel_markov V a ha L v w
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L v.depth
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L w.depth
  ext H : 1
  apply Measure.ext_of_lintegral
  intro G hG
  rw [Kernel.lintegral_map _ (measurable_finiteCascadeCrossGraftExtract _ _) _ hG,
    lintegral_finiteCascadeCrossVertexGraft V a ha L v w H G hG,
    Kernel.lintegral_compProd _ _ _ hG]
  apply lintegral_congr
  intro z
  rw [finiteCascadeCrossVertexPairKernel, Kernel.prod_apply, Kernel.comap_apply, Kernel.comap_apply]
  have hm : Measurable (fun c : S × S => G (z,c)) := hG.comp measurable_prodMk_left
  exact (MeasureTheory.lintegral_prod _ hm.aemeasurable).symm


theorem finiteCascadeCrossVertexGraft_joint_law (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (v w : FiniteCascadeRecordVertex T)
    (μ : Measure (FiniteStateField S)) [SFinite μ] :
    (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L (finiteCascadeCrossVertexGraft v w)).map
      (fun z => ((z.1,(finiteCascadeCrossGraftExtract v w z.2).1),
        (finiteCascadeCrossGraftExtract v w z.2).2)) =
      finiteCascadeCrossVertexMarkedLaw V a L v w (μ ⊗ₘ finiteCascadeTreeRecordKernel V a L T) := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L (finiteCascadeCrossVertexGraft v w)
  haveI := finiteCascadeCrossVertexPairKernel_markov V a ha L v w
  have hm := measurable_finiteCascadeCrossGraftExtract (S:=S) (E:=FiniteStateField S) v w
  rw [show (fun z : FiniteStateField S × Records (FiniteStateField S) S
      (finiteCascadeCrossVertexGraft v w) =>
      ((z.1,(finiteCascadeCrossGraftExtract v w z.2).1),
        (finiteCascadeCrossGraftExtract v w z.2).2)) =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id (finiteCascadeCrossGraftExtract v w)
      from rfl,
    ←Measure.map_map (MeasurableEquiv.measurable _) (measurable_id.prodMap hm),
    ←Measure.compProd_map hm, finiteCascadeCrossVertexGraft_kernel V a ha L v w,
    Measure.compProd_assoc]
  rfl

end FourPapersCommon
