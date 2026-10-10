module
public import FourPapersCommon.FiniteObservationTreeRefinement
public import FourPapersCommon.FiniteObservationTreeTransport

@[expose] public section

/-! Strict index embeddings and the explicit retained-record projection
commute with measurable changes of physical field coordinates. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
open FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128

 def observationEmbeddingGaps (e : ℕ→ℕ) (j : ℕ) : ℕ := e (j+1)-e j-1

theorem observationRefinementDepth_embedding (e : ℕ→ℕ) (he : StrictMono e)
    (hzero : e 0=0) (j : ℕ) : observationRefinementDepth (observationEmbeddingGaps e) j=e j := by
  induction j with
  | zero => exact hzero.symm
  | succ j ih =>
    rw [observationRefinementDepth,ih]
    have hs : e j < e (j+1) := he (Nat.lt_succ_self j)
    unfold observationEmbeddingGaps
    omega

@[reducible] def observationTreeDepthCast {j l : ℕ} (h : j=l) (T : FiniteTerminalGenealogy j) :
    FiniteTerminalGenealogy l := h ▸ T

@[reducible] def observationRecordDepthCast {E S : Type} {j l : ℕ} (h : j=l)
    (T : FiniteTerminalGenealogy j) : Records E S (observationTreeDepthCast h T)→Records E S T := by
  subst l
  exact id

theorem measurable_observationRecordDepthCast {E S : Type} [MeasurableSpace E] [MeasurableSpace S]
    {j l : ℕ} (h : j=l) (T : FiniteTerminalGenealogy j) :
    Measurable (observationRecordDepthCast (E:=E) (S:=S) h T) := by
  subst l
  exact measurable_id

theorem continuous_observationRecordDepthCast {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    {j l : ℕ} (h : j=l) (T : FiniteTerminalGenealogy j) :
    Continuous (observationRecordDepthCast (E:=E) (S:=S) h T) := by
  subst l
  exact continuous_id

theorem observationBlockCollapse_map {E F S : Type} (φ : E→F) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d : ℕ) :
    Prod.map φ (observationTreeMap (S:=S) φ T) ∘ observationBlockCollapse (S:=S) T d=
      observationBlockCollapse T d ∘ observationTreeMap (S:=S) φ (.advance (observationTreePad T d)) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change _ ∘ (observationBlockCollapse T d ∘ Prod.snd)=
      (observationBlockCollapse T d ∘ Prod.snd) ∘ Prod.map φ _
    rw [←Function.comp_assoc,ih,Function.comp_assoc]
    rfl

theorem observationRefinementProject_map {E F S : Type} (φ : E→F) (d : ℕ→ℕ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    observationTreeMap (S:=S) φ T ∘ observationRefinementProject (S:=S) d T=
      observationRefinementProject (S:=S) d T ∘ observationTreeMap (S:=S) φ (observationRefineTree d T) := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
    change Prod.map φ _ ∘ (Prod.map id _ ∘ observationBlockCollapse _ _)=
      (Prod.map id _ ∘ observationBlockCollapse _ _) ∘ observationTreeMap (S:=S) φ _
    rw [←Function.comp_assoc,Prod.map_comp_map]
    have he : Prod.map φ (observationTreeMap (S:=S) φ T ∘ observationRefinementProject (S:=S) d T)=
        Prod.map φ (observationRefinementProject (S:=S) d T ∘ observationTreeMap (S:=S) φ (observationRefineTree d T)) :=
      congrArg (Prod.map φ) ih
    rw [show φ ∘ id=φ from rfl,he]
    have hc : Prod.map φ (observationRefinementProject (S:=S) d T ∘ observationTreeMap (S:=S) φ (observationRefineTree d T))=
        Prod.map id (observationRefinementProject (S:=S) d T) ∘ Prod.map φ (observationTreeMap (S:=S) φ (observationRefineTree d T)) := by
      rw [Prod.map_comp_map]
      rfl
    rw [hc,Function.comp_assoc,observationBlockCollapse_map,←Function.comp_assoc]
  | fork T U ihT ihU =>
    change Prod.map _ _ ∘ Prod.map _ _=Prod.map _ _ ∘ Prod.map _ _
    rw [Prod.map_comp_map,Prod.map_comp_map,ihT,ihU]


theorem observationRecordDepthCast_map {E F S : Type} (φ : E→F) {j l : ℕ}
    (h : j=l) (T : FiniteTerminalGenealogy j) :
    observationTreeMap (S:=S) φ T ∘ observationRecordDepthCast (S:=S) h T=
      observationRecordDepthCast h T ∘ observationTreeMap (S:=S) φ (observationTreeDepthCast h T) := by
  subst l
  rfl

@[reducible] def observationRefinementDepthProject {E S : Type} (d : ℕ→ℕ)
    {j l : ℕ} (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l) :
    Records E S (observationTreeDepthCast h (observationRefineTree d T))→Records E S T :=
  observationRefinementProject (S:=S) d T ∘ observationRecordDepthCast h (observationRefineTree d T)

theorem measurable_observationRefinementDepthProject {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S] (d : ℕ→ℕ) {j l : ℕ}
    (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l) :
    Measurable (observationRefinementDepthProject (E:=E) (S:=S) d T h) :=
  (measurable_observationRefinementProject (S:=S) d T).comp
    (measurable_observationRecordDepthCast h (observationRefineTree d T))

theorem observationRefinementDepthProject_map {E F S : Type} (φ : E→F) (d : ℕ→ℕ)
    {j l : ℕ} (T : FiniteTerminalGenealogy j) (h : observationRefinementDepth d j=l) :
    observationTreeMap (S:=S) φ T ∘ observationRefinementDepthProject (S:=S) d T h=
      observationRefinementDepthProject d T h ∘
        observationTreeMap (S:=S) φ (observationTreeDepthCast h (observationRefineTree d T)) := by
  unfold observationRefinementDepthProject
  rw [←Function.comp_assoc,observationRefinementProject_map,Function.comp_assoc,
    observationRecordDepthCast_map,←Function.comp_assoc]


theorem continuous_observationTreeMap {E F S : Type} [TopologicalSpace E]
    [TopologicalSpace F] [TopologicalSpace S] (φ : E→F) (hφ : Continuous φ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) : Continuous (observationTreeMap (S:=S) φ T) := by
  induction T with
  | leaf => exact continuous_id
  | advance T ih => exact hφ.prodMap ih
  | fork T U ihT ihU => exact ihT.prodMap ihU

end FourPapersCommon
