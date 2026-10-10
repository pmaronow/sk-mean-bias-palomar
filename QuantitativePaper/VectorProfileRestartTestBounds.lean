module
public import QuantitativePaper.VectorProfileCellTestEnvelopes
public import QuantitativePaper.VectorProfileRawDerivativeEnvelopes
public import QuantitativePaper.VectorRestartCellDynkin

@[expose] public section

/-! Genuine second profile variations furnish the exponential-growth tests
for the restarted cell Dynkin theorem, including its elapsed-time shift. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfile_second_restart_test_bounds (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (hβ : β≠0) (ht : t<1) (i : ℕ) (hi : i≤k+1)
    (l u : ℝ) (hl : s₀.q i≤l) (hu : u<s₀.q (i+1))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (q : Paper.Overlap) (p : Couplings n×ℝ) :
    let f : ℝ×Field n→ℝ:=fun z=>
      vectorProfileCellPotentialSecondVariation s₀ s₁ β t i ((q:ℝ)+z.1,θ,p) z.2
    ContDiffOn ℝ ∞ f (Prod.fst ⁻¹' Ioo (l-(q:ℝ)) (u-(q:ℝ))) ∧
      ∃B K : ℝ,0≤B ∧ 0≤K ∧
        (∀r∈Ioo (l-(q:ℝ)) (u-(q:ℝ)),∀y : Field n,∀j : ℕ,j≤2→
          ‖iteratedFDeriv ℝ j (fun z=>f (r,z)) y‖≤B*Real.exp (K*‖y‖)) ∧
        (∀r∈Ioo (l-(q:ℝ)) (u-(q:ℝ)),∀y : Field n,
          ‖vectorRestartCellTimeField f (r,y)‖≤B*Real.exp (K*‖y‖)) := by
  let A:=θ/2
  let D:=(θ+1)/2
  have hA : 0<A:=by dsimp [A];linarith [hθ.1]
  have hD : D<1:=by dsimp [D];linarith [hθ.2]
  have hθAD : θ∈Ioo A D:=⟨by dsimp [A];linarith [hθ.1],by dsimp [D];linarith [hθ.2]⟩
  let F : VectorProfileCellParameter n×Field n→ℝ:=fun z=>
    vectorProfileCellPotentialSecondVariation s₀ s₁ β t i z.1 z.2
  let g:=vectorProfileTestRestriction θ F
  let f : ℝ×Field n→ℝ:=fun z=>F (((q:ℝ)+z.1,θ,p),z.2)
  have hF:=exponentialSmoothOn_vectorProfileCellPotentialSecondVariation
    (n:=n) s₀ s₁ β t hβ ht i hi l u A D hu hA hD
  obtain ⟨hg,B,K,hB,hK,hJ,hT⟩:=vectorProfileTestRestriction_exponential_bounds F l u A D θ
    hF ((s₀.q_nonneg (by omega)).trans hl) (hu.le.trans (s₀.q_le_one (by omega))) hA hD hθAD
  have hMem (r : ℝ) (hr : r∈Ioo (l-(q:ℝ)) (u-(q:ℝ))) : (q:ℝ)+r∈Ioo l u:=
    ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have hAt (r : ℝ) (hr : r∈Ioo (l-(q:ℝ)) (u-(q:ℝ))) (y : Field n) :
      ContDiffAt ℝ ∞ f (r,y) := by
    have hgAt : ContDiffAt ℝ ∞ g ((q:ℝ)+r,(p,y)):=
      hg.contDiffAt ((isOpen_Ioo.preimage continuous_fst).mem_nhds (hMem r hr))
    exact ContDiffAt.comp (f := fun z : ℝ×Field n=>((q:ℝ)+z.1,(p,z.2)))
      (g := g) (r,y) hgAt (by fun_prop)
  refine ⟨fun z hz=>(hAt z.1 hz z.2).contDiffWithinAt,
    B*Real.exp (K*‖p‖),K,by positivity,hK,?_,?_⟩
  · intro r hr y j hj
    have hh:=hJ ((q:ℝ)+r) (hMem r hr) p y j hj
    change ‖iteratedFDeriv ℝ j (fun z=>F (((q:ℝ)+r,θ,p),z)) y‖≤_ at hh ⊢
    exact hh.trans_eq (by rw [mul_add,Real.exp_add];ring)
  · intro r hr y
    have hgAt : ContDiffAt ℝ ∞ g ((q:ℝ)+r,(p,y)):=
      hg.contDiffAt ((isOpen_Ioo.preimage continuous_fst).mem_nhds (hMem r hr))
    have hd:=(hasDerivAt_vectorCell_time hgAt).comp r
      ((hasDerivAt_const r (q:ℝ)).add (hasDerivAt_id r))
    have he:=(hasDerivAt_vectorRestartCell_time (hAt r hr y)).unique hd
    simp only [zero_add,mul_one] at he
    rw [he]
    exact (hT ((q:ℝ)+r) (hMem r hr) p y).trans_eq (by rw [mul_add,Real.exp_add];ring)

end QuantitativePaper
