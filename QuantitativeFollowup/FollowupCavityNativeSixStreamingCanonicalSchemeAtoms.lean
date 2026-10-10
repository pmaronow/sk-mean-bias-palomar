module
public import QuantitativeFollowup.AnisotropicRecordedProfileFiniteTree
public import QuantitativeFollowup.AnisotropicObservationSchemeEmbedding
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginWeightIntegral
public import FRSB.FiniteSchemeRepresentation

@[expose] public section

/-! Canonical finite-support schemes retain every actual support point.
Their masses are the right CDF at the next lower observation clock, and
each nonempty adjacent observation interval carries only its upper atom.
The repeated terminal clocks and both endpoint atoms remain explicit. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem nativeStreamingCanonicalSchemeMass_eq_lower_CDF
    (μ : Paper.ParisiMeasure) (hμ : (μ : Measure Paper.Overlap).support.Finite)
    (j : ℕ) (hj : j<(FRSB.finiteLawNodes μ hμ).card+1) :
    anisotropicSchemeMass (FRSB.finiteLawRSBScheme μ hμ) j =
      Paper.parisiCDF μ
        (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) (j+1)) := by
  let k := (FRSB.finiteLawNodes μ hμ).card
  let s := FRSB.finiteLawRSBScheme μ hμ
  have hp : k+1-j≠0 := by dsimp only [k]; omega
  change FRSB.finiteLawSchemeMass μ hμ (k+1-j) = _
  rw [FRSB.finiteLawSchemeMass, if_neg hp]
  congr 1
  change FRSB.finiteLawSchemeOverlap μ hμ (k+1-j) =
    (anisotropicFiniteMeshNode s (k+2-(j+1)) : ℝ)
  rw [show k+2-(j+1)=k+1-j by omega,
    anisotropicFiniteMeshNode_coe s _ (by omega)]
  rfl

theorem nativeStreamingCanonicalScheme_Ioc_upper_atom_ae
    (μ : Paper.ParisiMeasure) (hμ : (μ : Measure Paper.Overlap).support.Finite)
    (j : ℕ) (hj : j<(FRSB.finiteLawNodes μ hμ).card+1) :
    ∀ᵐx∂(μ : Measure Paper.Overlap),
      x∈Ioc (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) (j+1))
        (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j) →
      x=anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j := by
  let k := (FRSB.finiteLawNodes μ hμ).card
  let s := FRSB.finiteLawRSBScheme μ hμ
  let p := k+1-j
  have hp : 0<p := by dsimp only [p,k]; omega
  have hlo : (anisotropicRecordedSchemeSchedule s (j+1) : ℝ) =
      FRSB.finiteLawSchemeOverlap μ hμ p := by
    change (anisotropicFiniteMeshNode s (k+2-(j+1)) : ℝ) = _
    rw [show k+2-(j+1)=p by dsimp only [p]; omega,
      anisotropicFiniteMeshNode_coe s _ (by dsimp only [p]; omega)]
    rfl
  have hhi : (anisotropicRecordedSchemeSchedule s j : ℝ) =
      FRSB.finiteLawSchemeOverlap μ hμ (p+1) := by
    change (anisotropicFiniteMeshNode s (k+2-j) : ℝ) = _
    rw [show k+2-j=p+1 by dsimp only [p]; omega,
      anisotropicFiniteMeshNode_coe s _ (by dsimp only [p]; omega)]
    rfl
  filter_upwards [(μ : Measure Paper.Overlap).support_mem_ae] with x hx hxI
  by_cases hpk : p<k
  · let il : Fin (FRSB.finiteLawNodes μ hμ).card := ⟨p-1,by dsimp only [k] at hpk; omega⟩
    let ih : Fin (FRSB.finiteLawNodes μ hμ).card := ⟨p,by dsimp only [k] at hpk; exact hpk⟩
    have hlow : anisotropicRecordedSchemeSchedule s (j+1) =
        FRSB.finiteLawNodeEmbedding μ hμ il := by
      apply Subtype.ext
      rw [hlo]
      have H := FRSB.finiteLawSchemeOverlap_at_index μ hμ il
      simpa only [il,show p-1+1=p by omega] using H
    have hhigh : anisotropicRecordedSchemeSchedule s j =
        FRSB.finiteLawNodeEmbedding μ hμ ih := by
      apply Subtype.ext
      rw [hhi]
      exact FRSB.finiteLawSchemeOverlap_at_index μ hμ ih
    have hxn : x∈FRSB.finiteLawNodes μ hμ := by
      simp only [FRSB.finiteLawNodes,Finset.mem_insert]
      exact Or.inr (Or.inr (hμ.mem_toFinset.mpr hx))
    let E := (FRSB.finiteLawNodes μ hμ).orderIsoOfFin rfl
    let ix := E.symm ⟨x,hxn⟩
    have hex : FRSB.finiteLawNodeEmbedding μ hμ ix=x := by
      change (E (E.symm _)).val=x
      simp
    have hli : il < ix := (FRSB.finiteLawNodeEmbedding μ hμ).lt_iff_lt.mp (by
      rw [hex,←hlow]
      exact hxI.1)
    have hih : ix ≤ ih := (FRSB.finiteLawNodeEmbedding μ hμ).le_iff_le.mp (by
      rw [hex,←hhigh]
      exact hxI.2)
    have hval : ix.val=p := by
      change p - 1 < ix.val at hli
      change ix.val ≤ p at hih
      omega
    have hix : ix=ih := Fin.ext hval
    rw [hix] at hex
    exact hex.symm.trans hhigh.symm
  · have hge : k≤p := Nat.le_of_not_gt hpk
    have hlowone : (anisotropicRecordedSchemeSchedule s (j+1) : ℝ)=1 := by
      rw [hlo,FRSB.finiteLawSchemeOverlap_top μ hμ hge]
    have hhighone : (anisotropicRecordedSchemeSchedule s j : ℝ)=1 := by
      rw [hhi,FRSB.finiteLawSchemeOverlap_top μ hμ (hge.trans (Nat.le_succ p))]
    have H₁ : (anisotropicRecordedSchemeSchedule s (j+1) : ℝ)<x := hxI.1
    have H₂ : (x : ℝ)≤anisotropicRecordedSchemeSchedule s j := hxI.2
    rw [hlowone] at H₁
    rw [hhighone] at H₂
    exact False.elim (not_lt_of_ge H₂ H₁)

theorem integral_nativeStreamingCanonicalScheme_Ioc_upper_atom
    (μ : Paper.ParisiMeasure) (hμ : (μ : Measure Paper.Overlap).support.Finite)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a)
    (j : ℕ) (hj : j<(FRSB.finiteLawNodes μ hμ).card+1)
    (G : Paper.Overlap → ℝ) :
    (∫r in Ioc
      (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) (j+1))
      (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j),
      G r ∂parisiFreeMeasure μ a) =
    (Paper.parisiCDF μ
      (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j)-
      anisotropicSchemeMass (FRSB.finiteLawRSBScheme μ hμ) j) *
        G (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j) := by
  have hle : parisiFreeMeasure μ a≤(μ : Measure Paper.Overlap) := by
    rw [←root_add_parisiFreeMeasure μ a ha hfloor]
    exact Measure.le_add_left le_rfl
  have hx : ∀ᵐ r ∂parisiFreeMeasure μ a,
      r∈Ioc (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) (j+1))
        (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j) →
      r=anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j :=
    ae_mono hle (nativeStreamingCanonicalScheme_Ioc_upper_atom_ae μ hμ j hj)
  have he : (∫r in Ioc
      (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) (j+1))
      (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j),
      G r ∂parisiFreeMeasure μ a) =
      ∫r in Ioc
      (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) (j+1))
      (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j),
      G (anisotropicRecordedSchemeSchedule (FRSB.finiteLawRSBScheme μ hμ) j)
        ∂parisiFreeMeasure μ a :=
    setIntegral_congr_ae measurableSet_Ioc (hx.mono fun r hr hI => congrArg G (hr hI))
  rw [he,setIntegral_const,nativeStreaming_free_real_Ioc μ a ha hfloor _ _
    (anisotropicRecordedSchemeSchedule_antitone (FRSB.finiteLawRSBScheme μ hμ)
      (Nat.le_succ j)),←nativeStreamingCanonicalSchemeMass_eq_lower_CDF μ hμ j hj]
  rfl

end QuantitativeFollowup
