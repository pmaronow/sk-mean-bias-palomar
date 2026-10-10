module
public import QuantitativePaper.VectorProfileTentCellSource
public import QuantitativePaper.VectorProfileExpectedNodeMatching
public import FourPapersCommon.CellDifferenceTelescope

@[expose] public section

/-! Actual tent-tested global variation identities. The trace-reaction
jumps are retained literally at every mass node, including repeated
overlap nodes; pairing values genuinely match there. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfile_curvature_pairing_tent_sum (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : ell∈Ioc (0:ℝ) 1) :
    let R:=fun i=>vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i)
    let H:=fun (i : ℕ) (q : ℝ)=>vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) q.toNNReal
    (∑i∈Finset.range (k+2),∫q in (s₀.q i)..(s₀.q (i+1)),
      responseTentSlope ell q*R i q+responseTent ell q*H i q)=0 := by
  let F : ℕ→ℝ→ℝ:=fun i q=>responseTent ell q*vectorProfileRetainedExpectation (n:=n)
    s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩ (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i) q
  have hm : ∀i<k+1,F (i+1) (s₀.q (i+1))=F i (s₀.q (i+1)):=by
    intro i hi
    unfold F
    rw [vectorProfile_retained_pairing_expected_match s₀ s₁ β t outer θ hβ.ne' ht hθ
      i (i+1) (by omega) (by omega) (s₀.q (i+1))
      ⟨s₀.q_mono i (by omega),le_rfl⟩ ⟨le_rfl,s₀.q_mono (i+1) (by omega)⟩]
  have hc : ∀i∈Finset.range (k+2),
      (∫q in (s₀.q i)..(s₀.q (i+1)),responseTentSlope ell q*
        vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
          (vectorProfileRetainedCurvaturePairing s₀ s₁ β t i) q+
        responseTent ell q*vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
          (vectorProfileFieldCurvaturePairingSource s₀ s₁ β t i) q.toNNReal)=
        F i (s₀.q (i+1))-F i (s₀.q i):=by
    intro i hi
    exact (vectorProfile_curvature_pairing_tent_closed_cell hn s₀ s₁ β t outer θ hβ ht i
      (by have:=Finset.mem_range.mp hi;omega) hθ ell hell.1).symm
  dsimp only
  rw [Finset.sum_congr rfl hc,sum_cell_differences_of_match F s₀.q (k+1) hm]
  simp only [F,s₀.q_top,s₀.q_zero,responseTent_zero_left hell.1 (by linarith [hell.1] : (0:ℝ)≤ell/4),
    responseTent_zero_right hell.1 (by linarith [hell.2] : 3*ell/4≤1),zero_mul,sub_self]

theorem vectorProfile_trace_reaction_squared_tent_sum (hn : 0<n)
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (hβ : 0<β) (ht : t<1)
    (hθ : θ∈Ioo (0:ℝ) 1) (ell : ℝ) (hell : ell∈Ioc (0:ℝ) 1) :
    let R:=fun i=>vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceReaction s₀ s₁ β t i)
    let H:=fun (i : ℕ) (q : ℝ)=>vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q.toNNReal
    let T:=fun i=>vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedTraceSquare s₀ s₁ β t i)
    (∑i∈Finset.range (k+2),∫q in (s₀.q i)..(s₀.q (i+1)),
      2*responseTentSlope ell q*responseTent ell q*R i q+(responseTent ell q)^2*H i q)=
      (1-t)*β*∑i∈Finset.range (k+1),
        (vectorProfileMass s₀ s₁ θ (i+1)-vectorProfileMass s₀ s₁ θ i)*
          (responseTent ell (s₀.q (i+1)))^2*T i (s₀.q (i+1)) := by
  let R:=fun i=>vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (vectorProfileRetainedTraceReaction s₀ s₁ β t i)
  let T:=fun i=>vectorProfileRetainedExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
    (vectorProfileRetainedTraceSquare s₀ s₁ β t i)
  let F : ℕ→ℝ→ℝ:=fun i q=>(responseTent ell q)^2*R i q
  have hc : ∀i∈Finset.range (k+2),
      (∫q in (s₀.q i)..(s₀.q (i+1)),2*responseTentSlope ell q*responseTent ell q*R i q+
        (responseTent ell q)^2*vectorProfileCellExpectation (n:=n) s₀ s₁ β t outer θ ht.le ⟨hθ.1.le,hθ.2.le⟩
          (vectorProfileFieldTraceTimeSource s₀ s₁ β t i) q.toNNReal)=
        F i (s₀.q (i+1))-F i (s₀.q i):=by
    intro i hi
    exact (vectorProfile_trace_reaction_squared_tent_closed_cell hn s₀ s₁ β t outer θ hβ ht i
      (by have:=Finset.mem_range.mp hi;omega) hθ ell hell.1).symm
  have hj : ∀i∈Finset.range (k+1),F (i+1) (s₀.q (i+1))-F i (s₀.q (i+1))=
      -(1-t)*β*((vectorProfileMass s₀ s₁ θ (i+1)-vectorProfileMass s₀ s₁ θ i)*
        (responseTent ell (s₀.q (i+1)))^2*T i (s₀.q (i+1))):=by
    intro i hi
    have hin:=Finset.mem_range.mp hi
    have hh:=vectorProfile_retained_reaction_expected_jump hn s₀ s₁ β t outer θ ht.le hθ
      i (i+1) (by omega) (by omega) (s₀.q (i+1))
      ⟨s₀.q_mono i (by omega),le_rfl⟩ ⟨le_rfl,s₀.q_mono (i+1) (by omega)⟩
    unfold F
    rw [←mul_sub,hh]
    ring
  dsimp only
  rw [Finset.sum_congr rfl hc,sum_cell_differences_with_jumps F s₀.q (k+1),Finset.sum_congr rfl hj]
  simp only [F,s₀.q_top,s₀.q_zero,responseTent_zero_left hell.1 (by linarith [hell.1] : (0:ℝ)≤ell/4),
    responseTent_zero_right hell.1 (by linarith [hell.2] : 3*ell/4≤1),zero_pow (by norm_num : (2:ℕ)≠0),
    zero_mul,sub_self,←Finset.mul_sum]
  ring

end QuantitativePaper
