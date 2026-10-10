module
public import FourPapersCommon.FiniteCascadeTerminalVertices

@[expose] public section

/-! An original leaf is identified by its actual tree vertex, independently
of which spin configuration happened to be drawn there. -/
noncomputable section
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 600000
variable {S : Type} [Fintype S]

theorem finiteCascadeTerminalVertices_eq_of_vertex_eq {j : ℕ}
    (T : FiniteTerminalGenealogy j) (σ : TerminalSpins S T)
    (c d : FiniteCascadeRecordVertex T×S)
    (hc : c∈finiteCascadeTerminalVertices T σ) (hd : d∈finiteCascadeTerminalVertices T σ)
    (h : c.1=d.1) : c=d := by
  induction T with
  | leaf =>
    have hc' : c=(.root .leaf,σ):=by simpa only [finiteCascadeTerminalVertices,List.mem_singleton] using hc
    have hd' : d=(.root .leaf,σ):=by simpa only [finiteCascadeTerminalVertices,List.mem_singleton] using hd
    exact hc'.trans hd'.symm
  | advance T ih =>
    obtain ⟨c',hc',rfl⟩:=List.mem_map.mp hc
    obtain ⟨d',hd',rfl⟩:=List.mem_map.mp hd
    have he : c'.1=d'.1:=by injection h
    rw [ih σ c' d' hc' hd' he]
  | fork T U ihT ihU =>
    rcases List.mem_append.mp hc with hc|hc <;>
      rcases List.mem_append.mp hd with hd|hd
    · obtain ⟨c',hc',rfl⟩:=List.mem_map.mp hc
      obtain ⟨d',hd',rfl⟩:=List.mem_map.mp hd
      have he : c'.1=d'.1:=by injection h
      rw [ihT σ.1 c' d' hc' hd' he]
    · obtain ⟨c',hc',rfl⟩:=List.mem_map.mp hc
      obtain ⟨d',hd',rfl⟩:=List.mem_map.mp hd
      cases h
    · obtain ⟨c',hc',rfl⟩:=List.mem_map.mp hc
      obtain ⟨d',hd',rfl⟩:=List.mem_map.mp hd
      cases h
    · obtain ⟨c',hc',rfl⟩:=List.mem_map.mp hc
      obtain ⟨d',hd',rfl⟩:=List.mem_map.mp hd
      have he : c'.1=d'.1:=by injection h
      rw [ihU σ.2 c' d' hc' hd' he]

end FourPapersCommon
