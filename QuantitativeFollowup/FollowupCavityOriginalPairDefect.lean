module
public import QuantitativeFollowup.FollowupCavityStreamingCurrent

@[expose] public section

/-! The original terminal-pair term is the literal overlap defect, and its
diagonal terms vanish exactly, without an expectation or limit argument. -/
noncomputable section
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2000000
variable {n k : ℕ}

theorem cavitySpinOverlapDefect_self (n : ℕ) (hn : 0<n) (σ : Configuration (n+1)) :
    cavitySpinOverlapDefect n 1 σ σ=0 := by
  rw [cavitySpinOverlapDefect_eq]
  have hs : Paper.spinSign (σ (Fin.last n))*Paper.spinSign (σ (Fin.last n))=1 := by
    rw [←pow_two,Paper.spinSign_sq]
  have he : (∑l : Fin n,Paper.spinSign (σ l.castSucc)*Paper.spinSign (σ l.castSucc))=(n:ℝ) := by
    simp_rw [←pow_two,Paper.spinSign_sq]
    simp
  rw [hs,he,div_self (by exact_mod_cast hn.ne')]
  ring

theorem cavityRecordedMarkPairDefect_originals (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ) (r : CavityPathRecordSpace (trimRoot T) (n+1))
    (c d : FiniteCascadeRecordVertex (trimRoot T)×Configuration (n+1)) :
    cavityRecordedMarkPairDefect D s T b r (.inl c) (.inl d)=
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.1 d.1) c.2 d.2 := rfl

theorem cavityRecordedMarkPairDefect_terminal_diagonal (D : AnisotropicSpinModel (n+1))
    (hn : 0<n) (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1))
    (c : FiniteCascadeRecordVertex (trimRoot T)×Configuration (n+1))
    (hc : c∈finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)) :
    cavityRecordedMarkPairDefect D s T b r (.inl c) (.inl c)=0 := by
  rw [cavityRecordedMarkPairDefect_originals,cavityPhysicalCommonOverlap_self,
    finiteCascadeTerminalVertices_depth_zero _ _ _ hc,Nat.sub_zero,s.q_top]
  exact cavitySpinOverlapDefect_self n hn c.2

def cavityRecordedOriginalOriginalOffDiagonal (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ := by
  classical
  let xs:=finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
  exact (xs.map (fun c=>(xs.map (fun d=>if c=d then 0 else
    cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.1 d.1) c.2 d.2)).sum)).sum

theorem cavityRecordedOriginalOriginalDefect_eq_offDiagonal (D : AnisotropicSpinModel (n+1))
    (hn : 0<n) (s : RSBScheme k) (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityRecordedOriginalOriginalDefect D s T b r=cavityRecordedOriginalOriginalOffDiagonal D s T b r := by
  classical
  unfold cavityRecordedOriginalOriginalDefect cavityRecordedOriginalOriginalOffDiagonal
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  by_cases h:c=d
  · subst d
    rw [ite_eq_left rfl,cavityRecordedMarkPairDefect_terminal_diagonal D hn s T b r c hc]
  · rw [ite_eq_right h,cavityRecordedMarkPairDefect_originals]

end QuantitativeFollowup
