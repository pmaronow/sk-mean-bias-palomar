module
public import HexagonPaper.PathHeatSignedJetPullback
public import HexagonPaper.PathHeatTreeBernsteinMixedFlatten

@[expose] public section

/-! Actual source index reduction for finite coordinates together with tree
paths. Finite coordinates are read only at terminal rows. Their signed jets
are pushed forward from the original index space, retaining every atom. -/
noncomputable section
open Set Filter MeasureTheory
open scoped unitInterval Topology BigOperators
namespace HexagonPaper
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Generic
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X] [CompactSpace Y] [SecondCountableTopology X] [SecondCountableTopology Y]

def pathHeatIndexRestriction (ι : C(X,Y)) : C(Y,ℝ) →L[ℝ] C(X,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ ι

@[simp] theorem pathHeatIndexRestriction_apply (ι : C(X,Y)) (h : C(Y,ℝ)) (x : X) :
    pathHeatIndexRestriction ι h x = h (ι x) := rfl

theorem norm_pathHeatIndexRestriction_le (ι : C(X,Y)) : ‖pathHeatIndexRestriction ι‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simp only [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg h)).mpr
  intro x
  exact h.norm_coe_le_norm (ι x)

theorem pathHeatIndexPushforward_tv_le (ι : C(X,Y)) (S : SignedMeasure X) :
    signedTV (S.map ι) ≤ signedTV S := by
  have ht : (S.map ι).variation univ ≤ S.variation univ := by
    calc
      _ ≤ (S.variation.map ι) univ := VectorMeasure.variation_map_le _
      _ = S.variation univ := by rw [Measure.map_apply ι.continuous.measurable MeasurableSet.univ]; simp
  exact ENNReal.toReal_mono (measure_ne_top S.variation univ) ht

theorem pathHeatIndexPushforward_tv_sub_le (ι : C(X,Y)) (S T : SignedMeasure X) :
    signedTV (S.map ι-T.map ι) ≤ signedTV (S-T) := by
  have he : (S-T).map ι=S.map ι-T.map ι :=
    map_sub (VectorMeasure.mapₗ (R:=ℝ) ι) S T
  rw [←he]
  exact pathHeatIndexPushforward_tv_le ι (S-T)

theorem tendsto_pathHeatIndexPushforward_tv_sub {Z : Type*} (l : Filter Z)
    (ι : C(X,Y)) (S : Z → SignedMeasure X) (T : SignedMeasure X)
    (h : Tendsto (fun z => signedTV (S z-T)) l (𝓝 0)) :
    Tendsto (fun z => signedTV ((S z).map ι-T.map ι)) l (𝓝 0) :=
  squeeze_zero (fun _ => signedTV_nonneg _) (fun z => pathHeatIndexPushforward_tv_sub_le ι (S z) T) h

theorem pathHeatIndexPushforward_score (ι : C(X,Y)) (S : SignedMeasure X) (h : C(Y,ℝ)) :
    pathHeatSignedScore (S.map ι) h = pathHeatSignedScore S (pathHeatIndexRestriction ι h) := by
  change (∫ᵛy,h y ∂•S.map ι) = ∫ᵛx,h (ι x) ∂•S
  exact VectorMeasure.integral_map ι.continuous.measurable h.continuous.aestronglyMeasurable
    (pathHeat_continuous_integrable (h.comp ι) S)

theorem pathHeatIndexPushforward_score_clm (ι : C(X,Y)) (S : SignedMeasure X) :
    pathHeatSignedScore (S.map ι) = (pathHeatSignedScore S).comp (pathHeatIndexRestriction ι) := by
  ext h
  exact pathHeatIndexPushforward_score ι S h

def pathHeatIndexPairMap (ι : C(X,Y)) : C(X×X,Y×Y) :=
  ⟨fun x => (ι x.1,ι x.2), (ι.continuous.comp continuous_fst).prodMk
    (ι.continuous.comp continuous_snd)⟩

theorem pathHeatIndexPushforward_hessian (ι : C(X,Y)) (M : SignedMeasure (X×X))
    (h k : C(Y,ℝ)) :
    pathHeatSignedHessian (M.map (pathHeatIndexPairMap ι)) h k =
      pathHeatSignedHessian M (pathHeatIndexRestriction ι h) (pathHeatIndexRestriction ι k) := by
  change (∫ᵛy,h y.1*k y.2 ∂•M.map (pathHeatIndexPairMap ι)) =
    ∫ᵛx,h (ι x.1)*k (ι x.2) ∂•M
  exact VectorMeasure.integral_map (pathHeatIndexPairMap ι).continuous.measurable
    (pathHeatTensor h k).continuous.aestronglyMeasurable
    (pathHeat_continuous_integrable ((pathHeatTensor h k).comp (pathHeatIndexPairMap ι)) M)

theorem hasFDerivAt_pathHeatIndexExtension (ι : C(X,Y))
    (f : C(X,ℝ) → ℝ) (S : SignedMeasure X) (p : C(Y,ℝ))
    (hf : HasFDerivAt f (pathHeatSignedScore S) (pathHeatIndexRestriction ι p)) :
    HasFDerivAt (fun v => f (pathHeatIndexRestriction ι v)) (pathHeatSignedScore (S.map ι)) p := by
  rw [pathHeatIndexPushforward_score_clm]
  exact hf.comp p (pathHeatIndexRestriction ι).hasFDerivAt

theorem contDiff_two_pathHeatIndexExtension (ι : C(X,Y))
    (f : C(X,ℝ) → ℝ) (S : C(X,ℝ) → SignedMeasure X)
    (M : C(X,ℝ) → SignedMeasure (X×X))
    (hf : ∀p, HasFDerivAt f (pathHeatSignedScore (S p)) p)
    (hS : ∀p, HasFDerivAt (fun q => pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (hM : ∀p, Tendsto (fun q => signedTV (M q-M p)) (𝓝 p) (𝓝 0)) :
    ContDiff ℝ 2 (fun p => f (pathHeatIndexRestriction ι p)) :=
  contDiff_two_pathHeatPullback (pathHeatIndexRestriction ι) f S M hf hS hM

end Generic

def pathHeatFiniteTreeIndex (A J : ℕ) := Fin A ⊕ (Fin J × I)

instance (A J : ℕ) : TopologicalSpace (pathHeatFiniteTreeIndex A J) :=
  inferInstanceAs (TopologicalSpace (Fin A ⊕ (Fin J × I)))
instance (A J : ℕ) : MeasurableSpace (pathHeatFiniteTreeIndex A J) :=
  borel (pathHeatFiniteTreeIndex A J)
instance (A J : ℕ) : BorelSpace (pathHeatFiniteTreeIndex A J) :=
  ⟨rfl⟩
instance (A J : ℕ) : CompactSpace (pathHeatFiniteTreeIndex A J) :=
  inferInstanceAs (CompactSpace (Fin A ⊕ (Fin J × I)))
instance (A J : ℕ) : SecondCountableTopology (pathHeatFiniteTreeIndex A J) :=
  inferInstanceAs (SecondCountableTopology (Fin A ⊕ (Fin J × I)))

def pathHeatFiniteTreeIndexEmbedding (A J : ℕ) :
    C(pathHeatFiniteTreeIndex A J,Fin (A+J) × I) :=
  ⟨Sum.elim (fun a => (finSumFinEquiv (Sum.inl a),1))
    (fun x => (finSumFinEquiv (Sum.inr x.1),x.2)),
    by
      apply continuous_sum_dom.mpr
      constructor
      · change Continuous (fun a : Fin A => (finSumFinEquiv (Sum.inl a),(1:I)))
        exact continuous_of_discreteTopology
      · change Continuous (fun x : Fin J × I => (finSumFinEquiv (Sum.inr x.1),x.2))
        have hc : Continuous (fun j : Fin J => (finSumFinEquiv (Sum.inr j) : Fin (A+J))) :=
          continuous_of_discreteTopology
        exact (hc.comp continuous_fst).prodMk continuous_snd⟩

@[simp] theorem pathHeatFiniteTreeIndexEmbedding_finite (A J : ℕ) (a : Fin A) :
    pathHeatFiniteTreeIndexEmbedding A J (Sum.inl a) = (finSumFinEquiv (Sum.inl a),1) := rfl

@[simp] theorem pathHeatFiniteTreeIndexEmbedding_tree (A J : ℕ) (x : Fin J × I) :
    pathHeatFiniteTreeIndexEmbedding A J (Sum.inr x) = (finSumFinEquiv (Sum.inr x.1),x.2) := rfl

theorem pathHeatFiniteTreeIndexEmbedding_injective (A J : ℕ) :
    Function.Injective (pathHeatFiniteTreeIndexEmbedding A J) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have he := finSumFinEquiv.injective (congrArg Prod.fst h)
      exact congrArg Sum.inl (Sum.inl.inj he)
    | inr b =>
      have he := finSumFinEquiv.injective (congrArg Prod.fst h)
      cases he
  | inr a =>
    cases y with
    | inl b =>
      have he := finSumFinEquiv.injective (congrArg Prod.fst h)
      cases he
    | inr b =>
      have he := finSumFinEquiv.injective (congrArg Prod.fst h)
      have ht : a.2=b.2 := congrArg (fun p : Fin (A+J) × I => p.2) h
      exact congrArg Sum.inr (Prod.ext (Sum.inr.inj he) ht)

end HexagonPaper
