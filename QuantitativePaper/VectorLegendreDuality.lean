module
public import QuantitativePaper.VectorLegendrePotential
public import QuantitativePaper.VectorMagnetizationGauge
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Identification of the actual selected Legendre value with the supremum
over all fields, and the literal zero-field duality identity. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff InnerProductSpace
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem vectorRecursion_supporting_plane {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (x y : Field n) :
    vectorRecursion s β t p j x+inner ℝ (vectorMagnetization s β t p j x) (y-x) ≤
      vectorRecursion s β t p j y:=by
  let g:ℝ→ℝ:=vectorRecursion s β t p j ∘ AffineMap.lineMap x y
  have hc:ConvexOn ℝ univ g:=by
    simpa only [preimage_univ] using
      (convexOn_vectorRecursion_field s β t p j).comp_affineMap (AffineMap.lineMap x y)
  have he:g=fun r : ℝ=>vectorRecursion s β t p j (x+r • (y-x)):=by
    funext r
    simp only [g,Function.comp_def,AffineMap.lineMap_apply_module',add_comm]
  have hd:HasDerivAt g (inner ℝ (vectorMagnetization s β t p j x) (y-x)) 0:=by
    rw [he]
    simpa only [zero_smul,add_zero] using
      hasDerivAt_vectorRecursion_field_gradient s β t p j x (y-x) 0
  have hh:=hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num : (0 : ℝ)<1) hd
  simp only [slope,vsub_eq_sub,smul_eq_mul,sub_zero,inv_one,one_mul,g,
    Function.comp_def,AffineMap.lineMap_apply_zero,AffineMap.lineMap_apply_one] at hh
  linarith

theorem vectorLegendrePotential_ge_pairing {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) (y : Field n) :
    inner ℝ m y-vectorRecursion s β t p j y ≤ vectorLegendrePotential s β t p j m:=by
  have hh:=vectorRecursion_supporting_plane s β t p j (vectorLegendreField s β t p j m) y
  rw [vectorMagnetization_legendreField s β t p j m hm,inner_sub_right] at hh
  unfold vectorLegendrePotential
  linarith

def vectorLegendreSup {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) : ℝ:=
  sSup (range (fun y : Field n=>inner ℝ m y-vectorRecursion s β t p j y))

theorem vectorLegendreSup_eq_potential {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) (m : Field n) (hm:m∈vectorOpenSpinCube n) :
    vectorLegendreSup s β t p j m=vectorLegendrePotential s β t p j m:=by
  apply IsGreatest.csSup_eq
  refine ⟨⟨vectorLegendreField s β t p j m,rfl⟩,?_⟩
  rintro z ⟨y,rfl⟩
  exact vectorLegendrePotential_ge_pairing s β t p j m hm y

theorem vectorLegendrePotential_zero {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (j : ℕ) :
    vectorLegendrePotential s β t p j 0= -vectorRecursion s β t p j 0:=by
  have hy:vectorLegendreField s β t p j 0=0:=by
    simpa only [vectorMagnetization_zero_field] using
      vectorLegendreField_magnetization s β t p j (0 : Field n)
  simp [vectorLegendrePotential,hy]

end QuantitativePaper
