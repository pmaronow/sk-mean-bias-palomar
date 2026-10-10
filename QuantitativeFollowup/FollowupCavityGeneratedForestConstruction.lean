module
public import QuantitativeFollowup.FollowupCavityGeneratedForestCheckpoint

@[expose] public section

/-! Actual genealogy constructors preserve generated branch clocks. The
forest receiver derives every pair's clock label from linear continuations,
marked forks and genuine continuation grafts; no pair-clock or marginal
domination assumption is supplied to its cubic conclusion. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

inductive CavityGeneratedGenealogyConstruction {m : ℕ}
    (labels : ℕ → CavityGeneratedClockLabel m) :
    {j : ℕ} → FiniteTerminalGenealogy j → Prop
  | linear (d : ℕ) : CavityGeneratedGenealogyConstruction labels
      (finiteCascadeLinearTerminalTree d)
  | advance {j : ℕ} {T : FiniteTerminalGenealogy j}
      (previous : CavityGeneratedGenealogyConstruction labels T) :
      CavityGeneratedGenealogyConstruction labels (.advance T)
  | fork {j : ℕ} {T U : FiniteTerminalGenealogy j}
      (i : Fin m) (atMark : labels j = .mark i)
      (left : CavityGeneratedGenealogyConstruction labels T)
      (right : CavityGeneratedGenealogyConstruction labels U) :
      CavityGeneratedGenealogyConstruction labels (.fork T U)
  | graft {j : ℕ} {T : FiniteTerminalGenealogy j}
      (U : (d : ℕ) → FiniteTerminalGenealogy d) (v : FiniteCascadeRecordVertex T)
      (i : Fin m) (atMark : labels v.depth = .mark i)
      (old : CavityGeneratedGenealogyConstruction labels T)
      (fresh : CavityGeneratedGenealogyConstruction labels (U v.depth)) :
      CavityGeneratedGenealogyConstruction labels (finiteCascadeContinuationGraft U v)

theorem CavityGeneratedGenealogyConstruction.pair_clock_labels {m j : ℕ}
    {labels : ℕ → CavityGeneratedClockLabel m} {T : FiniteTerminalGenealogy j}
    (H : CavityGeneratedGenealogyConstruction labels T) :
    cavityGeneratedPairClockLabels T labels := by
  induction H with
  | linear d => exact cavityGenerated_linear_clock_labels d labels
  | advance previous ih => exact cavityGenerated_advance_clock_labels _ labels ih
  | fork i hi left right ihLeft ihRight =>
      exact cavityGenerated_fork_clock_labels _ _ labels ihLeft ihRight ⟨i,hi⟩
  | graft U v i hi old fresh ihOld ihFresh =>
      exact cavityGenerated_continuation_graft_clock_labels U v labels ihOld ⟨i,hi⟩ ihFresh

def cavityGeneratedFiniteClockLabels {m J : ℕ}
    (labels : Fin (J+1) → CavityGeneratedClockLabel m) (j : ℕ) :
    CavityGeneratedClockLabel m :=
  if hj : j ≤ J then labels ⟨j,by omega⟩ else .initial

structure CavityGeneratedConstructedForest (m : ℕ) where
  componentCount : ℕ
  depth : Fin componentCount → ℕ
  tree : (c : Fin componentCount) → FiniteTerminalGenealogy (depth c)
  label : (c : Fin componentCount) → Fin (depth c+1) → CavityGeneratedClockLabel m
  terminal_label : ∀c, label c 0 = .terminal
  initial_label : ∀c, label c (Fin.last (depth c)) = .initial
  construction : ∀c, CavityGeneratedGenealogyConstruction
    (cavityGeneratedFiniteClockLabels (label c)) (tree c)

def CavityGeneratedConstructedForest.clockTemplate {m : ℕ}
    (W : CavityGeneratedConstructedForest m) : CavityGeneratedForestClockTemplate m where
  componentCount := W.componentCount
  depth := W.depth
  tree := W.tree
  label := W.label
  terminal_label := W.terminal_label
  initial_label := W.initial_label
  branch_label := by
    intro c b e hbe
    obtain ⟨i,hi⟩ := (W.construction c).pair_clock_labels b e hbe
    refine ⟨i,?_⟩
    have hj := cavityGenerated_observationCommonLevel_le (W.tree c) b e
    simpa only [cavityGeneratedFiniteClockLabels, dif_pos hj] using hi

theorem cavityGeneratedConstructedForest_three_defects_count_bound {n m : ℕ}
    (hn : 0 < n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : 0 ≤ a) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedForest m)
    (c : Fin 3 → Fin W.componentCount)
    (b e : (r : Fin 3) → ObservationLeaf (W.tree (c r)))
    (L : ℕ) (hL : P.largestMultiplicity ≤ L) :
    (∫ h, cavityGeneratedForestThreeDefectMoment D μ a W.depth W.tree
      (W.clockTemplate.clock h) c b e
      ∂(P.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)) ≤
      (cavityGeneratedThreeDefectCountConstant L P.constructorCount : ℝ) *
        cavityThirdMoment D μ a :=
  cavityGeneratedForestTemplate_threeDefects_count_bound hn D μ a ha P W.clockTemplate c b e L hL

theorem followup_cavity_constructed_history_three_defect_bound {n m : ℕ}
    (hn : 0 < n) (beta rho : ℝ) (hbeta : 0 < beta)
    (hrho : rho ∈ Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ) (ha : 0 ≤ a)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1)
    (H : CavityGeneratedStreamingMarkHistory μ m)
    (W : CavityGeneratedConstructedForest m)
    (c : Fin 3 → Fin W.componentCount)
    (b e : (r : Fin 3) → ObservationLeaf (W.tree (c r)))
    (L r : ℕ) (hL : H.maximumArity ≤ L) (hr : H.attachmentCount ≤ 2*r) :
    (∫ h, cavityGeneratedForestThreeDefectMoment
      (followupCavitySpinModel n beta rho hbeta hrho u hu) μ a W.depth W.tree
      (W.clockTemplate.clock h) c b e
      ∂(H.program.restrict W.clockTemplate.orderSet).measure (parisiFreeMeasure μ a)) ≤
      (((2*r+1)*L^(2*r) : ℕ) : ℝ) *
        cavityThirdMoment (followupCavitySpinModel n beta rho hbeta hrho u hu) μ a :=
  H.threeDefects_count_bound hn _ a ha W.clockTemplate c b e L r hL hr

end QuantitativeFollowup
