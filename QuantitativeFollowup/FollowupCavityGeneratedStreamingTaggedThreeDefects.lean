module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTerm

@[expose] public section

/-! Any three accumulated physical tags of a genuine recursively streamed
observable satisfy the literal cubic bound. All three pairs remain inside
their actual components, which may coincide or be independent. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {n C r m : ℕ}

def cavityGeneratedTaggedThreeDefectMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (A : CavityGeneratedTaggedTest n W r) (ι : Fin 3 → Fin r)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  ∫σ,|cavityGeneratedForestPairDefect n W (A.pairs (ι 0)) h σ *
    cavityGeneratedForestPairDefect n W (A.pairs (ι 1)) h σ *
    cavityGeneratedForestPairDefect n W (A.pairs (ι 2)) h σ|
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clockTemplate.clock h) : Measure _)

theorem cavityGeneratedActualTaggedStreamingTerm_three_defects
    (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
    (ι : Fin 3 → Fin r) :
    (∫h,cavityGeneratedTaggedThreeDefectMoment D μ a W A ι h ∂M) ≤
      (printedGeneratedStreamingCubicConstant (cavityGeneratedStreamingInitialLeafCount S) r : ℝ)*
        cavityThirdMoment D μ a :=
  cavityGeneratedActualStreamingTerm_three_defects hn D μ a ha hμ S
    (cavityGeneratedActualTaggedStreamingTerm_path μ a S F H)
    (fun j=>(A.pairs (ι j)).component) (fun j=>(A.pairs (ι j)).first) (fun j=>(A.pairs (ι j)).second)

theorem cavityGeneratedActualTaggedStreamingTerm_physical_three_defects
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (ι : Fin 3 → Fin r) :
    (∫h,cavityGeneratedTaggedThreeDefectMoment
      (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W A ι h
      ∂(ENNReal.ofReal (|followupCavityAlpha n β ρ/2|^r) • M)) ≤
      |followupCavityAlpha n β ρ/2|^r *
        (printedGeneratedStreamingCubicConstant (cavityGeneratedStreamingInitialLeafCount S) r : ℝ)*
          cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a :=
  cavityGeneratedActualStreamingTerm_physical_three_defects hn β ρ hβ hρ μ a ha hμ S
    (cavityGeneratedActualTaggedStreamingTerm_path μ a S F H) u hu
    (fun j=>(A.pairs (ι j)).component) (fun j=>(A.pairs (ι j)).first) (fun j=>(A.pairs (ι j)).second)

end QuantitativeFollowup
