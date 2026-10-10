module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionLocations
public import QuantitativeFollowup.SupportingGeneratedOriginClockMeasure
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! The selected-origin measure retains the true fork/edge/root payload.
Its integral is the actual source origin functional. The subsequent clock
pushforward forgets only the location, not a coefficient or endpoint atom. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
variable {j : ℕ}

abbrev CavityGeneratedOriginSelection (T : FiniteTerminalGenealogy j) :=
  Fin (cavityGeneratedOriginForkVertices T).length ⊕
    ((Fin (cavityGeneratedOriginEdges T).length × Paper.Overlap) ⊕ Unit)

def cavityGeneratedOriginSelectionOrigin (T : FiniteTerminalGenealogy j) :
    CavityGeneratedOriginSelection T → NativeStreamingOrigin T
  | .inl i => .vertex ((cavityGeneratedOriginForkVertices T).get i)
  | .inr (.inl z) => .edge ((cavityGeneratedOriginEdges T).get z.1) z.2
  | .inr (.inr _) => .vertex (.root T)

def cavityGeneratedOriginSelectionEdge (T : FiniteTerminalGenealogy j)
    (i : Fin (cavityGeneratedOriginEdges T).length) (r : Paper.Overlap) :
    CavityGeneratedOriginSelection T := Sum.inr (Sum.inl (i,r))

theorem measurable_cavityGeneratedOriginSelectionEdge
    (T : FiniteTerminalGenealogy j) (i : Fin (cavityGeneratedOriginEdges T).length) :
    Measurable (cavityGeneratedOriginSelectionEdge T i) :=
  measurable_inr.comp (measurable_inl.comp (measurable_const.prodMk measurable_id))

instance cavityGeneratedOriginSelection_dirac_smul_finite
    (T : FiniteTerminalGenealogy j) (c : ℝ) (g : CavityGeneratedOriginSelection T) :
    IsFiniteMeasure (ENNReal.ofReal c • Measure.dirac g) :=
  Measure.smul_finite _ ENNReal.ofReal_ne_top

def cavityGeneratedOriginSelectionMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy j) (s : ℝ) : Measure (CavityGeneratedOriginSelection T) :=
  (∑i : Fin (cavityGeneratedOriginForkVertices T).length,
    ENNReal.ofReal (Paper.parisiCDF μ (q ((cavityGeneratedOriginForkVertices T).get i).depth)) •
      Measure.dirac (Sum.inl i)) +
  (∑i : Fin (cavityGeneratedOriginEdges T).length,
    ((parisiFreeMeasure μ a).restrict
      (Ioc (q (((cavityGeneratedOriginEdges T).get i).depth+1))
        (q ((cavityGeneratedOriginEdges T).get i).depth))).map
          (cavityGeneratedOriginSelectionEdge T i)) +
  ENNReal.ofReal (Paper.parisiCDF μ (q j)-s) •
    Measure.dirac (Sum.inr (Sum.inr ()))

instance cavityGeneratedOriginSelectionMeasure_finite
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy j) (s : ℝ) :
    IsFiniteMeasure (cavityGeneratedOriginSelectionMeasure μ a q T s) := by
  unfold cavityGeneratedOriginSelectionMeasure
  infer_instance

theorem integral_cavityGeneratedOriginSelectionMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (hq0 : q 0=1) (T : FiniteTerminalGenealogy j) (s : ℝ)
    (hs : s ≤ Paper.parisiCDF μ (q j)) (Φ : NativeStreamingOrigin T → ℝ)
    (hΦ : Measurable (fun g => Φ (cavityGeneratedOriginSelectionOrigin T g)))
    (C : ℝ) (hC : ∀o, |Φ o| ≤ C) :
    (∫g, Φ (cavityGeneratedOriginSelectionOrigin T g)
      ∂cavityGeneratedOriginSelectionMeasure μ a q T s) =
      nativeStreamingOriginWeightIntegral μ a q T s Φ := by
  let f : CavityGeneratedOriginSelection T → ℝ :=
    fun g => Φ (cavityGeneratedOriginSelectionOrigin T g)
  have hi (M : Measure (CavityGeneratedOriginSelection T)) [IsFiniteMeasure M] :
      Integrable f M :=
    (integrable_const C).mono' hΦ.aestronglyMeasurable
      (.of_forall fun g => by simpa only [Real.norm_eq_abs] using hC _)
  have hf (i : Fin (cavityGeneratedOriginForkVertices T).length) :
      (∫g,f g ∂(ENNReal.ofReal
        (Paper.parisiCDF μ (q ((cavityGeneratedOriginForkVertices T).get i).depth)) •
          Measure.dirac (Sum.inl i))) =
      Paper.parisiCDF μ (q ((cavityGeneratedOriginForkVertices T).get i).depth)*
        Φ (.vertex ((cavityGeneratedOriginForkVertices T).get i)) := by
    rw [integral_smul_measure, integral_dirac' _ _ hΦ.stronglyMeasurable,
      ENNReal.toReal_ofReal (Paper.parisiCDF_nonneg μ _), smul_eq_mul]
    rfl
  have he (i : Fin (cavityGeneratedOriginEdges T).length) :
      (∫g,f g ∂(((parisiFreeMeasure μ a).restrict
        (Ioc (q (((cavityGeneratedOriginEdges T).get i).depth+1))
          (q ((cavityGeneratedOriginEdges T).get i).depth))).map
            (cavityGeneratedOriginSelectionEdge T i))) =
      ∫r in Ioc (q (((cavityGeneratedOriginEdges T).get i).depth+1))
        (q ((cavityGeneratedOriginEdges T).get i).depth),
          Φ (.edge ((cavityGeneratedOriginEdges T).get i) r) ∂parisiFreeMeasure μ a := by
    rw [integral_map (measurable_cavityGeneratedOriginSelectionEdge T i).aemeasurable
      hΦ.aestronglyMeasurable]
    rfl
  have hroot : (∫g,f g ∂(ENNReal.ofReal (Paper.parisiCDF μ (q j)-s) •
      Measure.dirac (Sum.inr (Sum.inr ())))) =
      (Paper.parisiCDF μ (q j)-s)*Φ (.vertex (.root T)) := by
    rw [integral_smul_measure, integral_dirac' _ _ hΦ.stronglyMeasurable,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hs), smul_eq_mul]
    rfl
  have hlist {A : Type} (L : List A) (F : A → ℝ) :
      (L.map F).sum = ∑i : Fin L.length, F (L.get i) := by
    have hh := congrArg (fun A : List A => (A.map F).sum) (List.ofFn_get L)
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using hh.symm
  rw [cavityGeneratedOriginSelectionMeasure,
    integral_add_measure (hi _) (hi _), integral_add_measure (hi _) (hi _),
    integral_finsetSum_measure (fun i _ => hi _),
    integral_finsetSum_measure (fun i _ => hi _), hroot]
  simp_rw [hf, he]
  rw [cavityGeneratedOriginWeightIntegral_eq_selected_locations μ a q hq0 T s Φ]
  rw [hlist (cavityGeneratedOriginEdges T)
    (fun e : NativeStreamingEdge T => ∫r in Ioc (q (e.depth+1)) (q e.depth),
      Φ (.edge e r) ∂parisiFreeMeasure μ a),
    hlist (cavityGeneratedOriginForkVertices T)
    (fun v : FiniteCascadeRecordVertex T => Paper.parisiCDF μ (q v.depth)*Φ (.vertex v))]
  ring

end QuantitativeFollowup
