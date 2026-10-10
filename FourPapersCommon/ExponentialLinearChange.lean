module
public import FourPapersCommon.ExponentialSmoothBounds

@[expose] public section

/-! Actual linear changes of coordinates preserve exponential jet bounds
without global smoothness outside the chosen open source domain. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem norm_iteratedFDeriv_precomp_clm_le_at (L : E→L[ℝ]F) (f : F→G) (x : E)
    (hf : ContDiffAt ℝ ∞ f (L x)) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (f ∘ L) x‖≤‖iteratedFDeriv ℝ r f (L x)‖*‖L‖^r := by
  obtain ⟨u,hu,hxu,hfu⟩:=(hf.contDiffWithinAt (s:=univ)).contDiffOn'
    (m:=(r:ℕ∞ω)) (by simp) (by simp)
  have hfu' : ContDiffOn ℝ r f u:=by simpa using hfu
  have hp : IsOpen (L⁻¹' u):=hu.preimage L.continuous
  have he:=L.iteratedFDerivWithin_comp_right hfu' hu.uniqueDiffOn hp.uniqueDiffOn hxu le_rfl
  rw [iteratedFDerivWithin_of_isOpen r hp hxu,iteratedFDerivWithin_of_isOpen r hu hxu] at he
  rw [he]
  exact ((iteratedFDeriv ℝ r f (L x)).norm_compContinuousLinearMap_le (fun _=>L)).trans_eq
    (by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin])

theorem ExponentialSmoothOn.precompCLM {f : F→G} {s : Set F} {u : Set E}
    (hf : ExponentialSmoothOn f s) (L : E→L[ℝ]F) (hmap : MapsTo L u s) :
    ExponentialSmoothOn (f ∘ L) u := by
  refine ⟨fun x hx=>(hf.smooth (L x) (hmap hx)).comp x L.contDiff.contDiffAt,fun r=>?_⟩
  obtain ⟨C,R,hC,hR,hb⟩:=hf.bound r
  refine ⟨C*‖L‖^r,R*‖L‖,by positivity,mul_nonneg hR (norm_nonneg _),fun x hx=>?_⟩
  apply (norm_iteratedFDeriv_precomp_clm_le_at L f x (hf.smooth (L x) (hmap hx)) r).trans
  calc
    _≤(C*Real.exp (R*‖L x‖))*‖L‖^r:=
      mul_le_mul_of_nonneg_right (hb (L x) (hmap hx)) (pow_nonneg (norm_nonneg _) _)
    _≤(C*Real.exp (R*(‖L‖*‖x‖)))*‖L‖^r:=by
      gcongr
      exact L.le_opNorm x
    _=_:=by
      rw [show R*(‖L‖*‖x‖)=(R*‖L‖)*‖x‖ by ring]
      ring

end FourPapersCommon
