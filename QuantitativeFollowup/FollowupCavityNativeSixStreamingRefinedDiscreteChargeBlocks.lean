module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingChargeRefinement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingDiscreteWeightAgreement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingNormalizedSchemeAtoms

@[expose] public section

/-! Actual unary subdivision charges and the corresponding half-closed
finite-profile Stieltjes cells. Equal clocks give empty cells, while the
first upper-cell coefficient is retained explicitly. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {k j : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingVertexChargeSum_pad_block
    (b : ℕ → ℝ) (incoming : ℝ) (T : FiniteTerminalGenealogy j) (t : ℕ)
    (Φ : FiniteCascadeRecordVertex (.advance (observationTreePad T t)) → ℝ) :
    nativeStreamingVertexChargeSum b incoming (.advance (observationTreePad T t)) Φ =
      nativeStreamingVertexChargeSum b (b j) T
        (fun v => Φ (.child (nativeStreamingPadVertexEmbed T t v))) +
      (∑p ∈ Finset.range t, (b (j+p)-b (j+p+1)) *
        Φ (nativeStreamingBlockSelectedVertexAt T t p)) +
      (b (j+t)-incoming)*Φ (.root (.advance (observationTreePad T t))) := by
  induction t generalizing incoming with
  | zero =>
      simpa only [observationTreePad, nativeStreamingPadVertexEmbed,
        Nat.add_zero, Finset.range_zero, Finset.sum_empty, add_zero] using
        nativeStreamingVertexChargeSum_advance b T incoming Φ
  | succ t ih =>
      rw [nativeStreamingVertexChargeSum_advance]
      simp only [observationTreePad]
      rw [ih (incoming := b (j+(t+1))) (fun v => Φ (.child v)), Finset.sum_range_succ]
      have hsum :
          (∑p ∈ Finset.range t, (b (j+p)-b (j+p+1)) *
            Φ (.child (nativeStreamingBlockSelectedVertexAt T t p))) =
          ∑p ∈ Finset.range t, (b (j+p)-b (j+p+1)) *
            Φ (nativeStreamingBlockSelectedVertexAt T (t+1) p) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpt : p ≠ t := (Finset.mem_range.mp hp).ne
        simp only [nativeStreamingBlockSelectedVertexAt, if_neg hpt]
      rw [hsum]
      simp only [nativeStreamingPadVertexEmbed, nativeStreamingBlockSelectedVertexAt,
        ite_true, Nat.add_assoc]
      ring

private theorem refinedDiscrete_integrable_free
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme s) ∈ scalarFloor a)
    (G : Paper.Overlap → ℝ) :
    Integrable G (parisiFreeMeasure (Paper.parisiSchemeMeasure (cdfMassScheme s)) a) := by
  have H : Integrable G (Paper.parisiSchemeMeasure (cdfMassScheme s) : Measure Paper.Overlap) := by
    change Integrable G (Paper.parisiSchemeRawMeasure (cdfMassScheme s))
    unfold Paper.parisiSchemeRawMeasure
    apply integrable_finsetSum_measure.mpr
    intro i hi
    exact (integrable_dirac (by simp)).smul_measure (by simp)
  apply H.mono_measure
  rw [←root_add_parisiFreeMeasure _ a ha hfloor]
  exact Measure.le_add_left le_rfl

private theorem refinedDiscrete_Ioc_telescope
    (ν : Measure Paper.Overlap) (Q : ℕ → Paper.Overlap) (hQ : Antitone Q)
    (G : Paper.Overlap → ℝ) (hG : Integrable G ν) (N t : ℕ) :
    (∑i ∈ Finset.range t, ∫r in Ioc (Q (N+i+1)) (Q (N+i)), G r ∂ν) =
      ∫r in Ioc (Q (N+t)) (Q N), G r ∂ν := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [Finset.sum_range_succ, ih, add_comm]
      rw [←setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        hG.integrableOn hG.integrableOn,
        Ioc_union_Ioc_eq_Ioc (hQ (by omega)) (hQ (by omega))]
      simp only [Nat.add_assoc]

theorem nativeStreamingNormalizedScheme_Ioc_pad_cells
    (s : RSBScheme k) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme s) ∈ scalarFloor a)
    (N t : ℕ) (hNt : N+t+1 ≤ k+1) (G : Paper.Overlap → ℝ) :
    let μ := Paper.parisiSchemeMeasure (cdfMassScheme s)
    let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme s)
    let b := anisotropicSchemeMass (cdfMassScheme s)
    (∫r in Ioc (Q (N+t+1)) (Q N), G r ∂parisiFreeMeasure μ a) =
      (Paper.parisiCDF μ (Q N)-b N)*G (Q N) +
        ∑p ∈ Finset.range t, (b (N+p)-b (N+p+1))*G (Q (N+p+1)) := by
  dsimp only
  let μ := Paper.parisiSchemeMeasure (cdfMassScheme s)
  let Q := anisotropicRecordedSchemeSchedule (cdfMassScheme s)
  let b := anisotropicSchemeMass (cdfMassScheme s)
  change (∫r in Ioc (Q (N+t+1)) (Q N), G r ∂parisiFreeMeasure μ a) =
    (Paper.parisiCDF μ (Q N)-b N)*G (Q N) +
      ∑p ∈ Finset.range t, (b (N+p)-b (N+p+1))*G (Q (N+p+1))
  have H := refinedDiscrete_Ioc_telescope (parisiFreeMeasure μ a) Q
    (anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme s)) G
    (refinedDiscrete_integrable_free s a ha hfloor G) N (t+1)
  simp only [←Nat.add_assoc] at H
  rw [←H, Finset.sum_range_succ', add_comm]
  simp only [Nat.add_zero]
  rw [integral_nativeStreamingNormalizedScheme_Ioc_upper_atom s a ha hfloor N (by omega) G]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpn : N+p < k+1 := by have := Finset.mem_range.mp hp; omega
  have hpnext : N+(p+1) < k+1 := by have := Finset.mem_range.mp hp; omega
  rw [integral_nativeStreamingNormalizedScheme_Ioc_upper_atom s a ha hfloor _ hpnext G]
  simp only [←Nat.add_assoc]
  rw [←nativeStreamingNormalizedSchemeMass_eq_lower_CDF s (N+p) hpn]

end QuantitativeFollowup
