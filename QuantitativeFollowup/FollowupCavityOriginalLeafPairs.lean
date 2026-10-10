module
public import QuantitativeFollowup.FollowupCavityOriginalPairDefect
public import FourPapersCommon.FiniteCascadeTerminalDistinct

@[expose] public section

/-! The original-original streaming sum excludes equal leaf vertices,
as in the manuscript, rather than comparing the values of sampled spins. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 600000
variable {n k : ℕ}

def cavityOriginalDistinctLeafDefect (n : ℕ) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2))
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) : ℝ := by
  classical
  let xs:=finiteCascadeTerminalVertices (trimRoot T) (finiteCascadeRecordTerminalSpins (trimRoot T) r.2)
  exact (xs.map (fun c=>(xs.map (fun d=>if c.1=d.1 then 0 else
    cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) c.1 d.1) c.2 d.2)).sum)).sum

theorem cavityRecordedOriginalOriginalDefect_eq_distinct_leaves
    (D : AnisotropicSpinModel (n+1)) (hn : 0<n) (s : RSBScheme k)
    (T : FiniteTerminalGenealogy (k+2)) (b : ℝ)
    (r : CavityPathRecordSpace (trimRoot T) (n+1)) :
    cavityRecordedOriginalOriginalDefect D s T b r=cavityOriginalDistinctLeafDefect n s T r := by
  classical
  rw [cavityRecordedOriginalOriginalDefect_eq_offDiagonal D hn s T b r]
  unfold cavityRecordedOriginalOriginalOffDiagonal cavityOriginalDistinctLeafDefect
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  have he : c=d ↔ c.1=d.1:=⟨fun h=>congrArg Prod.fst h,
    finiteCascadeTerminalVertices_eq_of_vertex_eq _ _ c d hc hd⟩
  simp only [he]

end QuantitativeFollowup
