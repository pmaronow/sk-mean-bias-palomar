module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionMeasure
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalBasisLinearityMoments

@[expose] public section

/-! Literal selected payloads for one source application. Each exterior
edge callback is zero only outside its own original halfclosed cell.
Both cross draws use the same original selection measure. The strict
future cells and the independent normalizer remain explicit. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedOriginCellMask (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (Φ : NativeStreamingOrigin T → ℝ) :
    NativeStreamingOrigin T → ℝ
  | .vertex v => Φ (.vertex v)
  | .edge e r => if r∈Ioc (q (e.depth+1)) (q e.depth) then Φ (.edge e r) else 0

def cavityGeneratedSelectedOriginPayload (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (Φ : NativeStreamingOrigin T → ℝ)
    (g : CavityGeneratedOriginSelection T) : ℝ :=
  cavityGeneratedOriginCellMask q T Φ (cavityGeneratedOriginSelectionOrigin T g)

theorem nativeStreamingOriginWeightIntegral_cellMask
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (s : ℝ) (Φ : NativeStreamingOrigin T → ℝ) :
    nativeStreamingOriginWeightIntegral μ a q T s (cavityGeneratedOriginCellMask q T Φ)=
      nativeStreamingOriginWeightIntegral μ a q T s Φ := by
  apply nativeStreamingOriginWeightIntegral_congr_ae_edges μ a q T s _ Φ
  · intro v
    rfl
  · intro e
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp only [cavityGeneratedOriginCellMask,if_pos hr]

theorem measurable_cavityGeneratedSelectedOriginPayload
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (Φ : NativeStreamingOrigin T → ℝ)
    (hE : ∀e : NativeStreamingEdge T,
      Measurable (fun r => if r∈Ioc (q (e.depth+1)) (q e.depth) then Φ (.edge e r) else 0)) :
    Measurable (cavityGeneratedSelectedOriginPayload q T Φ) := by
  have hf := measurable_of_countable (fun i : Fin (cavityGeneratedOriginForkVertices T).length =>
    Φ (.vertex ((cavityGeneratedOriginForkVertices T).get i)))
  have he : Measurable (fun z : Fin (cavityGeneratedOriginEdges T).length × Paper.Overlap =>
      if z.2∈Ioc (q (((cavityGeneratedOriginEdges T).get z.1).depth+1))
        (q ((cavityGeneratedOriginEdges T).get z.1).depth) then
        Φ (.edge ((cavityGeneratedOriginEdges T).get z.1) z.2) else 0) :=
    measurable_from_prod_countable_right (fun i => hE ((cavityGeneratedOriginEdges T).get i))
  have hr : Measurable (fun _ : Unit => Φ (.vertex (.root T))) := measurable_const
  exact hf.sumElim (he.sumElim hr)

def cavityGeneratedSelectedOriginalFreshPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (i : ObservationLeaf T) :
    CavityGeneratedOriginSelection T → ℝ :=
  cavityGeneratedSelectedOriginPayload q T
    (fun o => nativeStreamingPatternMoment D μ a q T F (.originalFresh i o))

def cavityGeneratedSelectedCurrentPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    CavityGeneratedOriginSelection T → ℝ :=
  cavityGeneratedSelectedOriginPayload q T (fun o =>
    Paper.parisiCDF μ (nativeStreamingOriginLevel q o)*
      nativeStreamingPatternMoment D μ a q T F (.current o))

def cavityGeneratedSelectedCrossPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (z : CavityGeneratedOriginSelection T × CavityGeneratedOriginSelection T) : ℝ :=
  cavityGeneratedSelectedOriginPayload q T (fun o =>
    cavityGeneratedSelectedOriginPayload q T
      (fun p => nativeStreamingPatternMoment D μ a q T F (.cross o p)) z.2) z.1

def cavityGeneratedSelectedFutureCellPayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (j : ℕ)
    (z : CavityGeneratedOriginSelection T × Paper.Overlap) : ℝ :=
  cavityGeneratedSelectedOriginPayload q T (fun o =>
    if z.2∈Ioc (q (j+1)) (q j) ∧ nativeStreamingOriginLevel q o<z.2 then
      nativeStreamingPatternMoment D μ a q T F (.future o j z.2) else 0) z.1

def cavityGeneratedSelectedFuturePayload
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (z : CavityGeneratedOriginSelection T × Paper.Overlap) : ℝ :=
  ∑j∈Finset.range J,cavityGeneratedSelectedFutureCellPayload D μ a q T F j z

def cavityGeneratedSelectedSourceSixBracket
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) : ℝ :=
  let M := cavityGeneratedOriginSelectionMeasure μ a q T a
  nativeStreamingSourceOriginalTerm D μ a q T F +
    (-2*∑i : ObservationLeaf T,∫g,cavityGeneratedSelectedOriginalFreshPayload D μ a q T F i g ∂M) +
    (∫z,cavityGeneratedSelectedCrossPayload D μ a q T F z ∂M.prod M) +
    (∫g,cavityGeneratedSelectedCurrentPayload D μ a q T F g ∂M) +
    (∫z,cavityGeneratedSelectedFuturePayload D μ a q T F z ∂M.prod (parisiFreeMeasure μ a)) +
    a*(∫l,nativeStreamingPatternMoment D μ a q T F (.normalizer l) ∂parisiFreeMeasure μ a)

end QuantitativeFollowup
