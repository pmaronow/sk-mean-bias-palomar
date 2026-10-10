module
public import FourPapersCommon.FiniteCascadeChargeLevels

@[expose] public section

/-! Exact charge separation for a vertex-dependent mark observable.
Forks at one retained state use the same mark value.  The identity retains
each actual edge and branch, rather than replacing the mark by a function
of its level alone. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 900000

@[reducible] def nativeStreamingRootCoherent : {j : ℕ} →
    (T : FiniteTerminalGenealogy j) → (FiniteCascadeRecordVertex T→ℝ) → Prop
  | _, .leaf, _ => True
  | _, .advance T, φ => nativeStreamingRootCoherent T (fun v=>φ (.child v))
  | _, .fork T U, φ =>
      φ (.left (.root T))=φ (.root (.fork T U)) ∧
      φ (.right (.root U))=φ (.root (.fork T U)) ∧
      nativeStreamingRootCoherent T (fun v=>φ (.left v)) ∧
      nativeStreamingRootCoherent U (fun v=>φ (.right v))

def nativeStreamingVertexChargeSum (a : ℕ→ℝ) (s : ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (φ : FiniteCascadeRecordVertex T→ℝ) : ℝ :=
  ((finiteCascadeVertexCharges a s T).map (fun c=>c.1*φ c.2)).sum

@[reducible] def nativeStreamingVertexEdgeSum (a : ℕ→ℝ) : {j : ℕ} →
    (T : FiniteTerminalGenealogy j) → (FiniteCascadeRecordVertex T→ℝ) → ℝ
  | _, .leaf, φ => (1-a 0)*φ (.root .leaf)
  | _, @FiniteTerminalGenealogy.advance j T, φ =>
      nativeStreamingVertexEdgeSum a T (fun v=>φ (.child v))+
        (a j-a (j+1))*φ (.root (.advance T))
  | _, .fork T U, φ =>
      nativeStreamingVertexEdgeSum a T (fun v=>φ (.left v))+
        nativeStreamingVertexEdgeSum a U (fun v=>φ (.right v))

@[reducible] def nativeStreamingVertexBranchSum (a : ℕ→ℝ) : {j : ℕ} →
    (T : FiniteTerminalGenealogy j) → (FiniteCascadeRecordVertex T→ℝ) → ℝ
  | _, .leaf, _ => 0
  | _, .advance T, φ => nativeStreamingVertexBranchSum a T (fun v=>φ (.child v))
  | j, .fork T U, φ =>
      nativeStreamingVertexBranchSum a T (fun v=>φ (.left v))+
        nativeStreamingVertexBranchSum a U (fun v=>φ (.right v))+a j*φ (.root (.fork T U))

theorem nativeStreamingVertexChargeSum_eq_edges_branches (a : ℕ→ℝ) (s : ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (φ : FiniteCascadeRecordVertex T→ℝ)
    (hφ : nativeStreamingRootCoherent T φ) :
    nativeStreamingVertexChargeSum a s T φ=
      nativeStreamingVertexEdgeSum a T φ+nativeStreamingVertexBranchSum a T φ+
        (a j-s)*φ (.root T) := by
  induction T generalizing s with
  | leaf =>
      simp only [nativeStreamingVertexChargeSum,finiteCascadeVertexCharges,
        finiteCascadeVertexInteriorCharges,finiteCascadeTreeRootCoefficient,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
        nativeStreamingVertexEdgeSum,nativeStreamingVertexBranchSum]
      ring
  | @advance j T ih =>
      have hi:=ih (a j) (fun v=>φ (.child v)) hφ
      simp only [nativeStreamingVertexChargeSum,finiteCascadeVertexCharges,
        finiteCascadeVertexInteriorCharges,finiteCascadeTreeRootCoefficient,
        List.map_cons,List.sum_cons,List.map_map,Function.comp_def] at hi ⊢
      change _=nativeStreamingVertexEdgeSum a T (fun v=>φ (.child v))+
        (a j-a (j+1))*φ (.root (.advance T))+
        nativeStreamingVertexBranchSum a T (fun v=>φ (.child v))+
        (a (j+1)-s)*φ (.root (.advance T))
      nlinarith only [hi]
  | @fork j T U ihT ihU =>
      obtain ⟨hleft,hright,hT,hU⟩:=hφ
      have ht:=ihT (a j) (fun v=>φ (.left v)) hT
      have hu:=ihU (a j) (fun v=>φ (.right v)) hU
      simp only [nativeStreamingVertexChargeSum,finiteCascadeVertexCharges,
        finiteCascadeVertexInteriorCharges,finiteCascadeTreeRootCoefficient,
        List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,hleft,hright] at ht hu ⊢
      change _=nativeStreamingVertexEdgeSum a T (fun v=>φ (.left v))+
        nativeStreamingVertexEdgeSum a U (fun v=>φ (.right v))+
        (nativeStreamingVertexBranchSum a T (fun v=>φ (.left v))+
          nativeStreamingVertexBranchSum a U (fun v=>φ (.right v))+a j*φ (.root (.fork T U)))+
        (a j-s)*φ (.root (.fork T U))
      nlinarith only [ht,hu]

end QuantitativeFollowup
