module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsResults

@[expose] public section

/-! An interior retained mark is copied by the actual coalesced branch
instruction. Its source arity is a separate input, and its appended clock
agrees with the old physical clock under the genuine generated measure. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

theorem nativeStreamingGeneratedComponentClock_eq_selected_mark
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (i : Fin m) (hi : cavityGeneratedFiniteClockLabels W.label v.depth = .mark i)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet W) :
    nativeStreamingGeneratedComponentClock W h v.depth = h i := by
  rw [nativeStreamingGeneratedComponentClock_eq_label_of_mem W h hh v.depth v.depth_le,hi]
  rfl

theorem nativeStreamingGeneratedVertexBranchComponent_clock_consistent
    (μ : Paper.ParisiMeasure) (a : ℝ) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < W.depth)
    (i : Fin m) (hi : cavityGeneratedFiniteClockLabels W.label v.depth = .mark i)
    (l : ℕ) (k : NativeStreamingGeneratedVertexKind) :
    ∀ᵐ H ∂(cavityGeneratedBranchMarkProgram μ P i l).measure (parisiFreeMeasure μ a),
      nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedVertexComponent W v hv0 hvJ k) H =
        nativeStreamingGeneratedComponentClock W (cavityGeneratedHistoryPrefix H) := by
  have he := cavityGeneratedBranchAttachedClockLabels_consistent μ a P
    (cavityGeneratedFiniteClockLabels W.label) v.depth i hi l
  apply he.mono
  intro H hh
  unfold nativeStreamingGeneratedComponentClock
  change cavityGeneratedClippedClock
    (fun j => (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedVertexLabels W v.depth) j).value H) = _
  rw [nativeStreamingGeneratedVertexLabels_global W v.depth hvJ.le]
  exact congrArg cavityGeneratedClippedClock (funext hh)

theorem nativeStreamingGeneratedVertexBranchProgram_ordered_prefix_law
    (μ : Paper.ParisiMeasure) (a : ℝ) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (i : Fin m) (hi : cavityGeneratedFiniteClockLabels W.label v.depth = .mark i)
    (l : ℕ) (hl : 1 ≤ l) :
    ((cavityGeneratedBranchMarkProgram μ
      (P.restrict (nativeStreamingGeneratedComponentOrderSet W)) i l).measure
        (parisiFreeMeasure μ a)).map cavityGeneratedHistoryPrefix =
      ((P.measure (parisiFreeMeasure μ a)).restrict (nativeStreamingGeneratedComponentOrderSet W)).withDensity
        (fun h => ENNReal.ofReal (nativeStreamingBranchCharge μ a
          (nativeStreamingGeneratedComponentClock W h v.depth) l)) := by
  rw [cavityGeneratedBranch_prefix_law]
  change ((P.measure (parisiFreeMeasure μ a)).restrict
    (nativeStreamingGeneratedComponentOrderSet W)).withDensity _ = _
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (isClosed_nativeStreamingGeneratedComponentOrderSet W).measurableSet]
    with h hh
  rw [nativeStreamingGeneratedComponentClock_eq_selected_mark W v i hi h hh]
  exact cavityGeneratedBranchWeight_eq_native μ a i l hl h

theorem nativeStreamingGeneratedVertexBranchCharge_nonneg
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (l : ℕ) (hl : 1 ≤ l) :
    0 ≤ nativeStreamingBranchCharge μ a q l := by
  have hlr : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  exact add_nonneg measureReal_nonneg
    (mul_nonneg (sub_nonneg.mpr hlr) (Paper.parisiCDF_nonneg μ q))

theorem measurable_nativeStreamingGeneratedVertexBranchCharge
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree)
    (l : ℕ) :
    Measurable (fun h => nativeStreamingBranchCharge μ a
      (nativeStreamingGeneratedComponentClock W h v.depth) l) := by
  have hq := (nativeStreamingGeneratedComponentClock_continuous W v.depth).measurable
  exact (measurable_nativeStreamingGeneratedAtomMass (parisiFreeMeasure μ a) _ hq).ennreal_toReal.add
    (((Paper.parisiCDF_measurable μ).comp (measurable_subtype_coe.comp hq)).const_mul _)

end QuantitativeFollowup
