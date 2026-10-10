module
public import QuantitativePaper.LocalJetBounds
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-! Actual scalar parameter slices of a jointly smooth function on a crop.
The retained random coordinate is unrestricted. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem iteratedFDeriv_scalarParameterSlice (f : ℝ×E→ℝ) (a b : ℝ)
    (hf : ∀z : ℝ×E,z.1∈Ioo a b → ContDiffAt ℝ ∞ f z)
    (θ : ℝ) (hθ : θ∈Ioo a b) (p : E) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y=>f (y,p)) θ=
      (iteratedFDeriv ℝ r f (θ,p)).compContinuousLinearMap
        (fun _=>ContinuousLinearMap.inl ℝ ℝ E) := by
  let U : Set (ℝ×E):={z|z.1∈Ioo a b}
  have hU : IsOpen U:=isOpen_Ioo.preimage continuous_fst
  let g:=fun z : ℝ×E=>f ((0,p)+z)
  have hg : ContDiffOn ℝ r g U:=by
    intro z hz
    have hbase : ContDiffAt ℝ ∞ g z:=(hf ((0,p)+z) (by simpa [U] using hz)).comp z
      (contDiffAt_const.add contDiffAt_id)
    exact (hbase.of_le (by simp)).contDiffWithinAt
  let A:=ContinuousLinearMap.inl ℝ ℝ E
  have hV : IsOpen (A⁻¹' U):=hU.preimage A.continuous
  have hx : A θ∈U:=hθ
  have he:=A.iteratedFDerivWithin_comp_right hg hU.uniqueDiffOn hV.uniqueDiffOn hx (i:=r) le_rfl
  rw [iteratedFDerivWithin_of_isOpen r hV hx,iteratedFDerivWithin_of_isOpen r hU hx] at he
  simpa [g,A,Function.comp_def,iteratedFDeriv_comp_add_left] using he

theorem norm_iteratedFDeriv_scalarParameterSlice_le (f : ℝ×E→ℝ) (a b : ℝ)
    (hf : ∀z : ℝ×E,z.1∈Ioo a b → ContDiffAt ℝ ∞ f z)
    (θ : ℝ) (hθ : θ∈Ioo a b) (p : E) (r : ℕ) :
    ‖iteratedFDeriv ℝ r (fun y=>f (y,p)) θ‖≤‖iteratedFDeriv ℝ r f (θ,p)‖ := by
  rw [iteratedFDeriv_scalarParameterSlice f a b hf θ hθ p r]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : (∏_ : Fin r,‖ContinuousLinearMap.inl ℝ ℝ E‖)≤1:=by
    simpa only [Finset.prod_const_one] using Finset.prod_le_prod₀
      (fun _ _=>norm_nonneg _) (fun _ _=>ContinuousLinearMap.norm_inl_le_one (𝕜:=ℝ) (E:=ℝ) (F:=E))
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

theorem continuous_iteratedFDeriv_scalarParameterSlice (f : ℝ×E→ℝ) (a b : ℝ)
    (hf : ∀z : ℝ×E,z.1∈Ioo a b → ContDiffAt ℝ ∞ f z)
    (θ : ℝ) (hθ : θ∈Ioo a b) (r : ℕ) :
    Continuous (fun p : E=>iteratedFDeriv ℝ r (fun y=>f (y,p)) θ) := by
  let U : Set (ℝ×E):={z|z.1∈Ioo a b}
  have hU : IsOpen U:=isOpen_Ioo.preimage continuous_fst
  have hs : ContDiffOn ℝ r f U:=fun z hz=>(hf z hz).of_le (by simp) |>.contDiffWithinAt
  have hc : ContinuousOn (iteratedFDerivWithin ℝ r f U) U:=
    hs.continuousOn_iteratedFDerivWithin (by norm_cast) hU.uniqueDiffOn
  have hj : Continuous (fun p : E=>iteratedFDeriv ℝ r f (θ,p)):=by
    have hh : Continuous (fun p : E=>iteratedFDerivWithin ℝ r f U (θ,p)):=
      hc.comp_continuous (show Continuous (fun p : E=>(θ,p)) from
        continuous_const.prodMk continuous_id) (fun p=>hθ)
    exact hh.congr (fun p=>iteratedFDerivWithin_of_isOpen r hU hθ)
  have hpre:=ContinuousMultilinearMap.continuous_precomp (F:=ℝ)
    (fun _ : Fin r=>ContinuousLinearMap.inl ℝ ℝ E)
  exact (hpre.comp hj).congr (fun p=>(iteratedFDeriv_scalarParameterSlice f a b hf θ hθ p r).symm)

end QuantitativePaper
