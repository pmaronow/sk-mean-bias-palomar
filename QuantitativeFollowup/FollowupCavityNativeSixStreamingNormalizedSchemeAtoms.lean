module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCanonicalSchemeAtoms
public import FourPapersCommon.FiniteSchemeCDFMassNormalization

@[expose] public section

/-! CDF-normalized masses on arbitrary unchanged finite nodes. Adjacent
observation intervals carry only their genuine upper atom; equal clocks
give an empty interval with zero coefficient. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {k : ℕ}
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128

theorem nativeStreamingNormalizedSchemeMass_eq_lower_CDF
    (s : RSBScheme k) (j : ℕ) (hj : j < k+1) :
    anisotropicSchemeMass (cdfMassScheme s) j =
      Paper.parisiCDF (Paper.parisiSchemeMeasure (cdfMassScheme s))
        (anisotropicRecordedSchemeSchedule (cdfMassScheme s) (j+1)) := by
  have hp : k+1-j≠0 := by omega
  rw [parisiSchemeMeasure_cdfMassScheme]
  change (if k+1-j=0 then 0 else Paper.parisiCDF (Paper.parisiSchemeMeasure s)
    (s.q (min (k+1-j) (k+1)))) = _
  rw [if_neg hp,min_eq_left (Nat.sub_le _ _)]
  congr 1
  change s.q (k+1-j)=(anisotropicFiniteMeshNode (cdfMassScheme s) (k+2-(j+1)) : ℝ)
  rw [show k+2-(j+1)=k+1-j by omega,anisotropicFiniteMeshNode_coe _ _ (by omega)]
  rfl

private theorem normalizedScheme_Ioc_upper_atom_ae_general
    (s : RSBScheme k) (j : ℕ) (hj : j < k+1) :
    ∀ᵐx∂(Paper.parisiSchemeMeasure s : Measure Paper.Overlap),
      x∈Ioc (anisotropicRecordedSchemeSchedule s (j+1)) (anisotropicRecordedSchemeSchedule s j) →
      x=anisotropicRecordedSchemeSchedule s j := by
  classical
  have hlo : (anisotropicRecordedSchemeSchedule s (j+1) : ℝ)=s.q (k+1-j) := by
    change (anisotropicFiniteMeshNode s (k+2-(j+1)) : ℝ)=_
    rw [show k+2-(j+1)=k+1-j by omega]
    exact anisotropicFiniteMeshNode_coe s _ (by omega)
  have hhi : (anisotropicRecordedSchemeSchedule s j : ℝ)=s.q (k+2-j) :=
    anisotropicFiniteMeshNode_coe s _ (by omega)
  change ∀ᵐx∂Paper.parisiSchemeRawMeasure s, _
  rw [Paper.parisiSchemeRawMeasure,ae_finsetSum_measure_iff]
  intro i hi
  apply Measure.ae_smul_measure
  rw [ae_dirac_eq]
  change Paper.parisiSchemeAtom s i∈Ioc _ _ → _
  intro h
  have hl : s.q (k+1-j) < s.q (i.val+1) := by
    have H : (anisotropicRecordedSchemeSchedule s (j+1) : ℝ) < Paper.parisiSchemeAtom s i := h.1
    simpa only [hlo,Paper.parisiSchemeAtom] using H
  have hu : s.q (i.val+1) ≤ s.q (k+2-j) := by
    have H : (Paper.parisiSchemeAtom s i : ℝ) ≤ anisotropicRecordedSchemeSchedule s j := h.2
    simpa only [hhi,Paper.parisiSchemeAtom] using H
  have hiq : k+2-j ≤ i.val+1 := by
    by_contra hn
    have hle : i.val+1 ≤ k+1-j := by omega
    exact (not_lt_of_ge (s.q_mono' (k+1-j) (by omega) (i.val+1) hle)) hl
  apply Subtype.ext
  rw [hhi]
  exact le_antisymm hu (s.q_mono' (i.val+1) (by omega) (k+2-j) hiq)

theorem nativeStreamingNormalizedScheme_Ioc_upper_atom_ae
    (s : RSBScheme k) (j : ℕ) (hj : j < k+1) :
    ∀ᵐx∂(Paper.parisiSchemeMeasure (cdfMassScheme s) : Measure Paper.Overlap),
      x∈Ioc (anisotropicRecordedSchemeSchedule (cdfMassScheme s) (j+1))
        (anisotropicRecordedSchemeSchedule (cdfMassScheme s) j) →
      x=anisotropicRecordedSchemeSchedule (cdfMassScheme s) j :=
  normalizedScheme_Ioc_upper_atom_ae_general (cdfMassScheme s) j hj

theorem nativeStreamingNormalizedScheme_Ioc_upper_atom
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme s)∈scalarFloor a)
    (j : ℕ) (hj : j < k+1) :
    let μ := Paper.parisiSchemeMeasure (cdfMassScheme s)
    let q := anisotropicRecordedSchemeSchedule (cdfMassScheme s)
    (parisiFreeMeasure μ a).restrict (Ioc (q (j+1)) (q j)) =
      (parisiFreeMeasure μ a) (Ioc (q (j+1)) (q j)) • Measure.dirac (q j) := by
  classical
  dsimp only
  let μ := Paper.parisiSchemeMeasure (cdfMassScheme s)
  let q := anisotropicRecordedSchemeSchedule (cdfMassScheme s)
  let ν := parisiFreeMeasure μ a
  have hle : ν ≤ (μ : Measure Paper.Overlap) := by
    rw [←root_add_parisiFreeMeasure μ a ha hfloor]
    exact Measure.le_add_left le_rfl
  have hx : ∀ᵐx∂ν, x∈Ioc (q (j+1)) (q j) → x=q j :=
    ae_mono hle (nativeStreamingNormalizedScheme_Ioc_upper_atom_ae s j hj)
  have hsingle : ∀ᵐx∂ν.restrict (Ioc (q (j+1)) (q j)), x∈({q j} : Finset Paper.Overlap) := by
    filter_upwards [ae_restrict_of_ae hx,ae_restrict_mem measurableSet_Ioc] with x h H
    simpa only [Finset.mem_singleton] using h H
  have H : ν.restrict (Ioc (q (j+1)) (q j)) =
      (ν.restrict (Ioc (q (j+1)) (q j))) {q j} • Measure.dirac (q j) := by
    simpa only [Finset.sum_singleton] using (Measure.ae_mem_finset_iff.mp hsingle)
  have hc := congrArg (fun m : Measure Paper.Overlap => m univ) H
  simp only [Measure.restrict_apply_univ,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] at hc
  exact H.trans (congrArg (fun c => c • Measure.dirac (q j)) hc.symm)

theorem integral_nativeStreamingNormalizedScheme_Ioc_upper_atom
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : Paper.parisiSchemeMeasure (cdfMassScheme s)∈scalarFloor a)
    (j : ℕ) (hj : j < k+1) (G : Paper.Overlap → ℝ) :
    let μ := Paper.parisiSchemeMeasure (cdfMassScheme s)
    let q := anisotropicRecordedSchemeSchedule (cdfMassScheme s)
    (∫r in Ioc (q (j+1)) (q j), G r ∂parisiFreeMeasure μ a) =
      (Paper.parisiCDF μ (q j)-anisotropicSchemeMass (cdfMassScheme s) j)*G (q j) := by
  dsimp only
  let μ := Paper.parisiSchemeMeasure (cdfMassScheme s)
  let q := anisotropicRecordedSchemeSchedule (cdfMassScheme s)
  have hle : parisiFreeMeasure μ a ≤ (μ : Measure Paper.Overlap) := by
    rw [←root_add_parisiFreeMeasure μ a ha hfloor]
    exact Measure.le_add_left le_rfl
  have hx : ∀ᵐx∂parisiFreeMeasure μ a, x∈Ioc (q (j+1)) (q j) → x=q j :=
    ae_mono hle (nativeStreamingNormalizedScheme_Ioc_upper_atom_ae s j hj)
  have he : (∫r in Ioc (q (j+1)) (q j), G r ∂parisiFreeMeasure μ a) =
      ∫r in Ioc (q (j+1)) (q j), G (q j) ∂parisiFreeMeasure μ a :=
    setIntegral_congr_ae measurableSet_Ioc (hx.mono fun r hr hI => congrArg G (hr hI))
  rw [he,setIntegral_const,nativeStreaming_free_real_Ioc μ a ha hfloor _ _
    (anisotropicRecordedSchemeSchedule_antitone (cdfMassScheme s) (Nat.le_succ j)),
    ←nativeStreamingNormalizedSchemeMass_eq_lower_CDF s j hj]
  rfl

end QuantitativeFollowup
