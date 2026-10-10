module
public import QuantitativeFollowup.AnisotropicPairResponses
public import FourPapersCommon.ParisiCDFRight

@[expose] public section

/-! Actual upward grid nodes retain right-CDF atoms and provide the correct
suffix posterior at zero, one, and every physical observation time. -/
noncomputable section
open Set Filter MeasureTheory FourPapersCommon QuantitativePaper
open scoped Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n : ℕ}
set_option maxHeartbeats 800000

def anisotropicGridNodeIndex (N : ℕ) (q : Paper.Overlap) : ℕ :=
  (Paper.parisiGridIndex N q).val+1

theorem anisotropicGridNodeIndex_pos (N : ℕ) (q : Paper.Overlap) :
    0<anisotropicGridNodeIndex N q := by unfold anisotropicGridNodeIndex;omega

theorem anisotropicGridNodeIndex_le (N : ℕ) (q : Paper.Overlap) :
    anisotropicGridNodeIndex N q≤N+2 := by
  have h:=(Paper.parisiGridIndex N q).isLt
  unfold anisotropicGridNodeIndex
  omega

theorem anisotropicGridNode_overlap (μ : Paper.ParisiMeasure) (N : ℕ) (q : Paper.Overlap) :
    (Paper.parisiGridRSBScheme μ N).q (anisotropicGridNodeIndex N q)=Paper.parisiGridRound N q := by
  have hi : (Paper.parisiGridIndex N q).val≤N+1 := Nat.le_of_lt_succ (Paper.parisiGridIndex N q).isLt
  simp only [Paper.parisiGridRSBScheme,Paper.parisiGridSchemeOverlap,anisotropicGridNodeIndex,
    Nat.add_sub_cancel,Nat.min_eq_left hi]
  rfl

theorem anisotropicGridNode_eq_round (μ : Paper.ParisiMeasure) (N : ℕ) (q : Paper.Overlap) :
    anisotropicSchemeNode (Paper.parisiGridRSBScheme μ N) (anisotropicGridNodeIndex N q)
      (by have h:=anisotropicGridNodeIndex_le N q;omega)=Paper.parisiGridRound N q := by
  apply Subtype.ext
  exact anisotropicGridNode_overlap μ N q

theorem anisotropicGridNode_mass (μ : Paper.ParisiMeasure) (N : ℕ) (q : Paper.Overlap) :
    (Paper.parisiGridRSBScheme μ N).m (anisotropicGridNodeIndex N q)=
      Paper.parisiCDF (Paper.parisiGridMeasure μ N) (Paper.parisiGridRound N q) := by
  change Paper.parisiGridSchemeMass μ N (anisotropicGridNodeIndex N q)=_
  rw [Paper.parisiGridSchemeMass,if_neg (Nat.ne_of_gt (anisotropicGridNodeIndex_pos N q))]
  congr 1
  exact anisotropicGridNode_overlap μ N q

theorem tendsto_anisotropicGridNode_mass (μ : Paper.ParisiMeasure) (q : Paper.Overlap) :
    Tendsto (fun j=>(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).m
      (anisotropicGridNodeIndex (vectorDyadicIndex j) q)) atTop (𝓝 (Paper.parisiCDF μ q)) := by
  simp_rw [anisotropicGridNode_mass]
  exact (tendsto_parisiCDF_grid_at_round μ q).comp tendsto_vectorDyadicIndex

theorem anisotropicGridNode_after (μ : Paper.ParisiMeasure) (N : ℕ) (q : Paper.Overlap) :
    (q : ℝ)≤(Paper.parisiGridRSBScheme μ N).q (anisotropicGridNodeIndex N q) := by
  rw [anisotropicGridNode_overlap]
  exact Paper.le_parisiGridRound N q

theorem anisotropicFiniteTailPairResponse_gridNode (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (N : ℕ) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) :
    anisotropicFiniteTailPairResponse D (Paper.parisiGridRSBScheme μ N) (Paper.parisiGridRound N q) P e=
      ∫σ,Paper.spinSign (σ e.1.1)*Paper.spinSign (σ e.1.2)
        ∂anisotropicFiniteSpinKernel D (Paper.parisiGridRSBScheme μ N)
          (N+3-anisotropicGridNodeIndex N q) P := by
  have hi : anisotropicGridNodeIndex N q≤(N+1)+2 := by
    have h:=anisotropicGridNodeIndex_le N q
    omega
  rw [←anisotropicGridNode_eq_round μ N q]
  convert anisotropicFiniteTailPairResponse_node D (Paper.parisiGridRSBScheme μ N)
    (anisotropicGridNodeIndex N q) hi P e using 1 <;> congr 2 <;> omega

end QuantitativeFollowup
