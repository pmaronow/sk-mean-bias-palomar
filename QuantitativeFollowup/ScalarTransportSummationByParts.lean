module
public import QuantitativeFollowup.ScalarTransportPartialResponse
public import FourPapersCommon.FiniteTransportSummation

@[expose] public section

/-! Exact finite Stieltjes summation by parts for the actual transported
scalar potential derivative, including coincident levels. The future
moments here are the actual refined Gaussian endpoint kernel moments. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon OverlapPaper
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
variable {k : ℕ}

def scalarTransportOriginalFuture (s : RSBScheme k) (β : ℝ) (hβ : 0 < β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ)
    (r J : ℕ) (x : ℝ) : ℝ :=
  scalarSchemeFutureSquareKernel (scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu)
    β hβ 0 (3*(r+1)) (3*J) (EuclideanSpace.single (0:Fin 1) x)

theorem scalarTransport_refined_mass_sum (s : RSBScheme k) (β : ℝ) (hβ : 0 < β)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| ≤ δ)
    (i J : ℕ) (x : ℝ) :
    (∑p∈Finset.range (3*i+2),(coefficientScheduleMass s (p+1)-coefficientScheduleMass s p)*
      scalarSchemeFutureSquareKernel (scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu)
        β hβ 0 (p+1) (3*J) (EuclideanSpace.single (0:Fin 1) x))=
      ∑r∈Finset.range i,(scalarSchemeMass s (r+1)-scalarSchemeMass s r)*
        scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu r J x := by
  simpa only [scalarTransportOriginalFuture,scalarSchemeMass,coefficientScheduleMass] using
    sum_threefold_mass_differences (scalarSchemeMass s)
      (fun p=>scalarSchemeFutureSquareKernel
        (scalarTransportRefinedScheme s φ L hφ h0 h1 δ u hδ hsmall hu)
          β hβ 0 p (3*J) (EuclideanSpace.single (0:Fin 1) x)) i

theorem scalarTransportNodeScheduleDerivative_eq_original_cells (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| < δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    scalarTransportNodeScheduleDerivative s β φ δ J u x=
      β^2/2*∑i∈Finset.range J,scalarTransportCellSlope s φ (k+1-i)*
        (1+∑r∈Finset.range i,(scalarSchemeMass s (r+1)-scalarSchemeMass s r)*
          scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu.le r J x) := by
  rw [scalarTransportNodeScheduleDerivative_eq_refined_futures s β hβ φ L hφ h0 h1 δ u x
    hδ hsmall hu J hJ]
  simp_rw [scalarTransport_refined_mass_sum]

theorem scalarTransportNodeScheduleDerivative_summation_by_parts (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ u x : ℝ) (hδ : 0 < δ) (hsmall : δ*L < 1) (hu : |u| < δ)
    (J : ℕ) (hJ : J ≤ k+2) :
    scalarTransportNodeScheduleDerivative s β φ δ J u x=
      -(β^2/2)*(
        φ (scalarSchemeTransportNode s (k+2-J))*
          (1+∑r∈Finset.range J,(scalarSchemeMass s (r+1)-scalarSchemeMass s r)*
            scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu.le r J x)-
        ∑r∈Finset.range J,(scalarSchemeMass s (r+1)-scalarSchemeMass s r)*
          scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu.le r J x*
            φ (scalarSchemeTransportNode s (k+1-r))) := by
  let B:=fun i=>φ (scalarSchemeTransportNode s (k+2-i))
  let A:=fun r=>(scalarSchemeMass s (r+1)-scalarSchemeMass s r)*
    scalarTransportOriginalFuture s β hβ φ L hφ h0 h1 δ u hδ hsmall hu.le r J x
  have hB : B 0=0 := by
    dsimp only [B]
    rw [Nat.sub_zero]
    have hnode : scalarSchemeTransportNode s (k+2)=1 := by
      apply Subtype.ext
      simp [scalarSchemeTransportNode,s.q_top]
    rw [hnode,h1]
  have he (i : ℕ) (hi : i∈Finset.range J) :
      scalarTransportCellSlope s φ (k+1-i)=B i-B (i+1) := by
    have hij:=Finset.mem_range.mp hi
    dsimp only [scalarTransportCellSlope,B]
    rw [show k+1-i+1=k+2-i by omega,show k+1-i=k+2-(i+1) by omega]
  rw [scalarTransportNodeScheduleDerivative_eq_original_cells s β hβ φ L hφ h0 h1 δ u x
    hδ hsmall hu J hJ]
  have hs : (∑i∈Finset.range J,scalarTransportCellSlope s φ (k+1-i)*(1+∑r∈Finset.range i,A r))=
      -(B J*(1+∑r∈Finset.range J,A r)-∑r∈Finset.range J,A r*B (r+1)) := by
    rw [←sum_transport_cell_response_of_terminal_zero B A hB J]
    apply Finset.sum_congr rfl
    intro i hi
    rw [he i hi]
  change β^2/2*(∑i∈Finset.range J,scalarTransportCellSlope s φ (k+1-i)*(1+∑r∈Finset.range i,A r))=_
  rw [hs]
  dsimp only [B,A]
  have hnodes (r : ℕ) : k+2-(r+1)=k+1-r := by omega
  simp_rw [hnodes]
  ring

end QuantitativeFollowup
