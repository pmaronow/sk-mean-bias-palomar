module
public import QuantitativeFollowup.FollowupCavityMarkLevelDomination
public import QuantitativeFollowup.FollowupCavityStreamingCoefficientBound

@[expose] public section

/-! Actual levels introduced by one cavity streaming operation. The
vertex charges, strict-future marks, and root-normalizer marks use their
literal weights. Their domination retains inherited branch marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
variable {k : ℕ}

def cavityStreamingAddedLevelTest (s : RSBScheme k) (a : ℝ)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap → ℝ) : ℝ :=
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  ((finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)).map
    (fun c=>c.1*(f (anisotropicVertexOverlap s c.2)+
      (∫q : Paper.Overlap, if anisotropicVertexOverlap s c.2<q then f q else 0∂ν)))).sum+
        a*(∫q, f q∂ν)

private theorem weighted_sum_le {A : Type*} (xs : List (ℝ×A)) (f : A → ℝ) (B : ℝ)
    (hw : ∀c∈xs, 0 ≤ c.1) (hf : ∀c∈xs, f c.2 ≤ B) :
    (xs.map (fun c=>c.1*f c.2)).sum≤(xs.map Prod.fst).sum*B := by
  induction xs with
  | nil=>simp
  | cons c xs ih=>
    simp only [List.map_cons, List.sum_cons, add_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (hf c (by simp)) (hw c (by simp)))
      (ih (fun d hd=>hw d (by simp [hd])) (fun d hd=>hf d (by simp [hd])))

theorem cavityStreamingAddedLevelTest_le_free_and_branches
    (s : RSBScheme k) (a : ℝ) (ha : 0 ≤ a) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T : FiniteTerminalGenealogy (k+2)) (f : Paper.Overlap → ℝ) (hf : ∀q, 0 ≤ f q) :
    cavityStreamingAddedLevelTest s a T f≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)*
        (2*(∫q, f q∂parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)+
          finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)) := by
  let ν:=parisiFreeMeasure (Paper.parisiSchemeMeasure s) a
  let E:=∫q, f q∂ν
  let cs:=finiteCascadeVertexCharges (anisotropicSchemeMass s) a (trimRoot T)
  let L:ℝ:=FiniteCascadeGenealogy.leafCount (asGenealogy T)
  have hE : 0 ≤ E:=integral_nonneg hf
  have hi : Integrable f ν := by
    change Integrable f (parisiFreeMeasure (Paper.parisiSchemeMeasure s) a)
    rw [←vectorProfileFreeMeasure_eq_actual_free s a ha has hq]
    exact integrable_vectorProfileFreeMeasure s a f
  have hv (v : FiniteCascadeRecordVertex (trimRoot T)) :
      (∫q : Paper.Overlap, if anisotropicVertexOverlap s v<q then f q else 0∂ν) ≤ E := by
    have hi' : Integrable (fun q : Paper.Overlap=>if anisotropicVertexOverlap s v<q then f q else 0) ν := by
      convert! hi.indicator (measurableSet_Ioi (a:=anisotropicVertexOverlap s v)) using 1
    exact integral_mono hi' hi (fun q=>by split_ifs <;> simp [hf])
  have hW : (cs.map Prod.fst).sum=L-a := by
    dsimp only [cs, L]
    rw [finiteCascadeVertexCharges_sum, leafCount_trimRoot]
  have hfuture : (cs.map (fun c=>c.1*
      (∫q : Paper.Overlap, if anisotropicVertexOverlap s c.2<q then f q else 0∂ν))).sum≤(L-a)*E := by
    have hh:=weighted_sum_le cs
      (fun v=>∫q : Paper.Overlap, if anisotropicVertexOverlap s v<q then f q else 0∂ν)
      E (anisotropicTrimmedVertexCharges_nonneg s a has T)
      (fun c _=>hv c.2)
    rw [hW] at hh
    exact hh
  have hvertex:=cavityLevelCharges_le_free_and_branch_marks s a ha has hq (trimRoot T) f hf
  rw [leafCount_trimRoot] at hvertex
  change (cs.map (fun c=>c.1*f (anisotropicVertexOverlap s c.2))).sum≤
    L*(E+finiteCascadeUnweightedBranchSum (fun j=>f (cavityProfileLevel s j)) (trimRoot T)) at hvertex
  have hexpand : cavityStreamingAddedLevelTest s a T f=
      (cs.map (fun c=>c.1*f (anisotropicVertexOverlap s c.2))).sum+
        (cs.map (fun c=>c.1*
          (∫q : Paper.Overlap, if anisotropicVertexOverlap s c.2<q then f q else 0∂ν))).sum+a*E := by
    unfold cavityStreamingAddedLevelTest
    dsimp only [cs, E, ν]
    simp_rw [mul_add]
    rw [List.sum_map_add]
  rw [hexpand]
  change _ ≤ L*(2*E+_)
  nlinarith only [hvertex, hfuture]

end QuantitativeFollowup
