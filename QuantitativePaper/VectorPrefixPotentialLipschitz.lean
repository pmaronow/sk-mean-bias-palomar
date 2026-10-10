module
public import QuantitativePaper.VectorPrefixRestriction
public import QuantitativePaper.VectorSiteDerivativeBounds

@[expose] public section

/-! Every chronological actual potential has incident-site Lipschitz
constant beta, independent of the number of Gaussian coordinates. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def sitePrefixGaussianPotential {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (j : Fin (N+1)) (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) : ℝ :=
  vectorRecursion s β t (sitePrefixGaussianState s β t i b j g).1
    (k+2-j.val) (sitePrefixGaussianState s β t i b j g).2

theorem contDiff_sitePrefixGaussianPotential {n k N : ℕ} (s : RSBScheme k) (β t : ℝ)
    (i : Fin n) (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i))
    (j : Fin (N+1)) : ContDiff ℝ ∞ (sitePrefixGaussianPotential s β t i b j) :=
  (contDiff_vectorRecursion_joint s β t (k+2-j.val)).comp
    (contDiff_sitePrefixGaussianState s β t i b j)

theorem lipschitzWith_sitePrefixGaussianPotential {n k N : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : 0 ≤ β) (ht : t ∈ Icc 0 1) (hN : N ≤ k+2) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)) (j : Fin (N+1)) :
    LipschitzWith β.toNNReal (sitePrefixGaussianPotential s β t i b j) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro g z
  let w := z-g
  let p := sitePrefixGaussianState s β t i b j g
  let W := sitePrefixGaussianState s β t i 0 j w
  let R := (β*‖w‖).toNNReal
  have hR : (R:ℝ)=β*‖w‖ := Real.coe_toNNReal _ (mul_nonneg hβ (norm_nonneg _))
  have hb (σ : Configuration n) : |vectorTerminalExponent n β t W.1 W.2 σ|≤(R:ℝ) := by
    rw [hR]
    exact siteTerminalEnergy_at_prefix_bound s β t hβ ht hN i (by omega : j.val≤N) σ w
  let f : ℝ → ℝ := fun r => vectorRecursion s β t (p.1+r • W.1)
    (k+2-j.val) (p.2+r • W.2)
  have hd (r : ℝ) := hasDerivAt_vectorRecursion_joint_line s β t p W (k+2-j.val) r
  have hLip : LipschitzWith R f := lipschitzWith_of_nnnorm_deriv_le
    (fun r => (hd r).differentiableAt) (fun r => by
      rw [←NNReal.coe_le_coe,coe_nnnorm,Real.norm_eq_abs,(hd r).deriv]
      exact abs_vectorObservableResponse_le s β t p.1 _ R hb (k+2-j.val) r p.2)
  have h0 : f 0=sitePrefixGaussianPotential s β t i b j g := by
    simp [f,p,sitePrefixGaussianPotential]
  have hz : g+w=z := by dsimp [w];abel
  have hs : sitePrefixGaussianState s β t i b j z=p+W := by
    simpa only [one_smul,hz] using sitePrefixGaussianState_add_smul s β t i b j g w 1
  have h1 : f 1=sitePrefixGaussianPotential s β t i b j z := by
    simp only [f,one_smul,sitePrefixGaussianPotential,hs,Prod.fst_add,Prod.snd_add]
  have hh := hLip.dist_le_mul 0 1
  simpa [h0,h1,hR,w,Real.coe_toNNReal β hβ,dist_eq_norm,norm_sub_rev] using hh

theorem norm_fderiv_sitePrefixGaussianPotential_le {n k N : ℕ} (s : RSBScheme k)
    (β t : ℝ) (hβ : 0 ≤ β) (ht : t ∈ Icc 0 1) (hN : N ≤ k+2) (i : Fin n)
    (b : EuclideanSpace ℝ (SiteComplementIndex (N:=N) i)) (j : Fin (N+1))
    (g : EuclideanSpace ℝ (SiteGaussianIndex (N:=N) i)) :
    ‖fderiv ℝ (sitePrefixGaussianPotential s β t i b j) g‖ ≤ β := by
  simpa only [Real.coe_toNNReal β hβ] using norm_fderiv_le_of_lipschitz ℝ
    (lipschitzWith_sitePrefixGaussianPotential s β t hβ ht hN i b j) (x₀:=g)

end QuantitativePaper
