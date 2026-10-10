module
public import FourPapersCommon.FiniteCascadeReferenceEnergyLinear
public import FourPapersCommon.FiniteCascadeTreeReferenceSpins

@[expose] public section

/-! Terminal marks retain their actual vertices in the recorded genealogy.
Their linear field evaluations sum to the literal terminal energy. -/
noncomputable section
namespace FourPapersCommon
open SpinGlass.AT FiniteTerminalGenealogy
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {S I : Type} [Fintype S] [Fintype I]

@[reducible] def finiteCascadeTerminalVertices : {j : ℕ}→(T : FiniteTerminalGenealogy j)→
    TerminalSpins S T→List (FiniteCascadeRecordVertex T×S)
  | _,.leaf,σ => [(.root .leaf,σ)]
  | _,.advance T,σ => (finiteCascadeTerminalVertices T σ).map (fun c=>(.child c.1,c.2))
  | _,.fork T U,σ =>
      (finiteCascadeTerminalVertices T σ.1).map (fun c=>(.left c.1,c.2)) ++
      (finiteCascadeTerminalVertices U σ.2).map (fun c=>(.right c.1,c.2))

theorem finiteCascadeTerminalVertices_depth_zero {j : ℕ} (T : FiniteTerminalGenealogy j)
    (σ : TerminalSpins S T) (c : FiniteCascadeRecordVertex T×S)
    (hc : c∈finiteCascadeTerminalVertices T σ) : c.1.depth=0 := by
  induction T with
  | leaf =>
    have he : c=(.root .leaf,σ):=by simpa only [finiteCascadeTerminalVertices,List.mem_singleton] using hc
    subst c
    rfl
  | advance T ih =>
    obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
    exact ih σ d hd
  | fork T U ihT ihU =>
    rcases List.mem_append.mp hc with hc|hc
    · obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
      exact ihT σ.1 d hd
    · obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
      exact ihU σ.2 d hd

theorem finiteCascadeReferenceTerminalEnergy_eq_vertex_sum
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (σ : TerminalSpins S T)
    (H : FiniteStateField S) (z : FiniteStateGaussianInput (GaussianCoordinateIndex I T)) :
    finiteCascadeReferenceTerminalEnergyCLM L T σ (H,z)=
      ((finiteCascadeTerminalVertices T σ).map (fun c=>
        finiteCascadeRecordVertexCLM L T c.1 (H,z) c.2)).sum := by
  induction T generalizing H with
  | leaf =>
    simp only [finiteCascadeTerminalVertices,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,finiteCascadeReferenceTerminalEnergyCLM,
      finiteCascadeRecordVertexCLM,ContinuousLinearMap.comp_apply]
    rfl
  | @advance j T ih =>
    simpa only [finiteCascadeReferenceTerminalEnergyCLM,finiteCascadeTerminalVertices,
      List.map_map,Function.comp_def,finiteCascadeRecordVertexCLM,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      Function.comp_apply]
      using ih σ (H+L j (finiteGaussianLeft z)) (finiteGaussianRight z)
  | fork T U ihT ihU =>
    simp only [finiteCascadeReferenceTerminalEnergyCLM,finiteCascadeTerminalVertices,
      List.map_append,List.sum_append,List.map_map,Function.comp_def,
      finiteCascadeRecordVertexCLM,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      Function.comp_apply]
    exact congrArg₂ (fun x y : ℝ=>x+y) (ihT σ.1 H (finiteGaussianLeft z))
      (ihU σ.2 H (finiteGaussianRight z))

end FourPapersCommon
