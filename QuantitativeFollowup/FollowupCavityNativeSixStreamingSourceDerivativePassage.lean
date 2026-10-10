module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingWeakJets
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracketLimit

@[expose] public section

/-! A supporting passage from a genuine finite-profile source identity to
the same literal source bracket for arbitrary profiles. The finite identity
is an explicit hypothesis here; its model proof belongs to the finite
fine-to-coarse streaming assembly. No native bracket is defined as a jet. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128

theorem nativeStreamingSource_derivative_of_finite_profiles
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (hfloor : μ ∈ scalarFloor a)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (hJ : 0 < J)
    (hzero : (q 0:ℝ) = 1) (htop : (q J:ℝ) = 0)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1)
    (hfinite : ∀ν : Paper.ParisiMeasure,
      (ν : Measure Paper.Overlap).support.Finite → ν ∈ scalarFloor a →
      withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ ν a q T F)
        (Icc (0:ℝ) 1) 1 u =
        (followupCavityAlpha n β ρ / 2) * nativeStreamingSourceSixBracket
          (followupCavitySpinModel n β ρ hβ hρ u hu) ν a q T F) :
    withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) 1 u =
      (followupCavityAlpha n β ρ / 2) * nativeStreamingSourceSixBracket
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T F := by
  classical
  let S : Finset Paper.Overlap := insert zeroOverlap ((Finset.range (J+1)).image q)
  have hS : zeroOverlap ∈ S := Finset.mem_insert_self _ _
  have hcuts : ∀j, j ≤ J → q j ∈ S := by
    intro j hj
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j, Finset.mem_range.mpr (by omega), rfl⟩)
  have hroot : a ≤ Paper.parisiCDF μ 0 := by
    rw [←zeroMass_eq_parisiCDF_zero]
    exact (mem_scalarFloor_iff a μ).mp hfloor
  have hjet := (tendstoUniformlyOn_followupCavityNativeJets_preserving
    hn β ρ hβ hρ μ S hS a ha hroot q hq hJ hzero htop T F 1).tendsto_at hu
  have hbracket := (tendsto_nativeStreamingSourceSixBracket
    (followupCavitySpinModel n β ρ hβ hρ u hu) μ a ha hfloor q hq T S hS hcuts F).const_mul
      (followupCavityAlpha n β ρ / 2)
  apply tendsto_nhds_unique hjet
  apply hbracket.congr'
  exact Eventually.of_forall fun N =>
    (hfinite (FRSB.preservingMeasure μ S N)
      (FRSB.finite_support_preservingMeasure μ S N)
      (nativeStreaming_preserving_floor μ S hS a hfloor N)).symm

end QuantitativeFollowup
