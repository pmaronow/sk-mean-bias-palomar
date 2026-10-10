module
public import QuantitativePaper.SmoothCoordinateDivision
public import QuantitativePaper.LocalSmoothIntegralJets
public import QuantitativePaper.OpenGaussianRelativeBounds

@[expose] public section

/-! Local full derivatives for a linear coordinate contraction. These are
actual derivatives on an open domain, including contraction to coordinate zero. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1600000
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_comp_linear_on_open (f : E → F) (U : Set E)
    (hU : IsOpen U) {N j : ℕ} (hf : ContDiffOn ℝ N f U) (hj : j ≤ N)
    (L : G →L[ℝ] E) (x : G) (hx : L x ∈ U) :
    iteratedFDeriv ℝ j (f ∘ L) x =
      (iteratedFDeriv ℝ j f (L x)).compContinuousLinearMap (fun _ => L) := by
  have hV := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hV.uniqueDiffOn hx
    (show (j : ℕ∞ω) ≤ N by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen j hV hx,
    iteratedFDerivWithin_of_isOpen j hU hx] at he
  exact he

theorem norm_iteratedFDeriv_comp_linear_on_open (f : E → F) (U : Set E)
    (hU : IsOpen U) {N j : ℕ} (hf : ContDiffOn ℝ N f U) (hj : j ≤ N)
    (L : G →L[ℝ] E) (x : G) (hx : L x ∈ U) (hL : ‖L‖ ≤ 1) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  rw [iteratedFDeriv_comp_linear_on_open f U hU hf hj L x hx]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hp : ‖L‖^j ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg L) hL j
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)

theorem gaussianCoordinate_iteratedFDeriv_fieldSlice_eq_on_open {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (f : A×E → F)
    (U : Set (A×E)) (hU : IsOpen U) {N j : ℕ} (hf : ContDiffOn ℝ N f U)
    (hj : j ≤ N) (a : A) (x : E) (hx : (a,x) ∈ U) :
    iteratedFDeriv ℝ j (fun y => f (a,y)) x =
      (iteratedFDeriv ℝ j f (a,x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ A E) := by
  let L : E →L[ℝ] A×E := ContinuousLinearMap.inr ℝ A E
  let G : A×E → F := fun z => f (z+(a,0))
  let V : Set (A×E) := (fun z => z+(a,0)) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_id.add continuous_const)
  have hG : ContDiffOn ℝ N G V := hf.comp
    (contDiff_id.add contDiff_const).contDiffOn (fun _ h => h)
  have hLx : L x ∈ V := by simpa [V,L] using hx
  have he : (fun y => f (a,y)) = G ∘ L := by
    funext y
    simp [G,L,Function.comp_def]
  rw [he, iteratedFDeriv_comp_linear_on_open G V hV hG hj L x hLx,
    iteratedFDeriv_comp_add_right]
  simp only [L,ContinuousLinearMap.inr_apply,zero_add,add_zero,Prod.mk_add_mk]

theorem continuousOn_fieldSlice_iteratedFDeriv_on_open {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] (f : A×E → F)
    (U : Set (A×E)) (hU : IsOpen U) {N j : ℕ} (hf : ContDiffOn ℝ N f U)
    (hj : j ≤ N) :
    ContinuousOn (fun z : A×E => iteratedFDeriv ℝ j (fun y => f (z.1,y)) z.2) U := by
  have hc := (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ A E)).continuous.comp_continuousOn
      (ContinuousOn.continuousOn_iteratedFDeriv hf hU
        (show (j : ℕ∞ω) ≤ N by exact_mod_cast hj))
  apply hc.congr
  intro z hz
  exact gaussianCoordinate_iteratedFDeriv_fieldSlice_eq_on_open f U hU hf hj z.1 z.2 hz

def coordinateContraction (r : ℝ) : ℝ×E →L[ℝ] ℝ×E :=
  r • ((ContinuousLinearMap.inl ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ ℝ E)) +
    (ContinuousLinearMap.inr ℝ ℝ E).comp (ContinuousLinearMap.snd ℝ ℝ E)

@[simp] theorem coordinateContraction_apply (r : ℝ) (x : ℝ×E) :
    coordinateContraction r x = (r*x.1,x.2) := by
  simp [coordinateContraction, Prod.smul_mk, Prod.mk_add_mk]

theorem norm_coordinateContraction_le_one (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
    ‖coordinateContraction (E:=E) r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [one_mul, coordinateContraction_apply, Prod.norm_def, Real.norm_eq_abs]
  apply max_le
  · have hh := mul_le_mul_of_nonneg_right hr.2 (abs_nonneg x.1)
    rw [abs_mul, abs_of_nonneg hr.1]
    exact hh.trans (by simpa only [one_mul] using le_max_left |x.1| ‖x.2‖)
  · exact le_max_right _ _

theorem continuous_coordinateContraction :
    Continuous (coordinateContraction (E:=E)) := by
  unfold coordinateContraction
  exact (continuous_id.smul continuous_const).add continuous_const

def coordinateDerivative (f : ℝ×E → ℝ) (x : ℝ×E) : ℝ :=
  fderiv ℝ f x (1,0)

theorem coordinateDerivative_smooth_on_open (f : ℝ×E → ℝ) (U : Set (ℝ×E))
    (hU : IsOpen U) (N : ℕ) (hf : ContDiffOn ℝ (N+1) f U) :
    ContDiffOn ℝ N (coordinateDerivative f) U := by
  exact (hf.fderiv_of_isOpen hU (by norm_cast)).clm_apply contDiffOn_const

theorem coordinateDerivative_jet_bound (f : ℝ×E → ℝ) (U : Set (ℝ×E))
    (hU : IsOpen U) {N j : ℕ} (hf : ContDiffOn ℝ (N+1) f U)
    (hj : j ≤ N) (x : ℝ×E) (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ j (coordinateDerivative f) x‖ ≤
      ‖iteratedFDeriv ℝ (j+1) f x‖ := by
  have hd : ContDiffAt ℝ N (fderiv ℝ f) x :=
    (hf.fderiv_of_isOpen hU (by norm_cast)).contDiffAt (hU.mem_nhds hx)
  have hh := norm_iteratedFDeriv_clm_apply_const (c:=((1:ℝ),(0:E))) hd
    (show (j : ℕ∞ω) ≤ N by exact_mod_cast hj)
  change ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ f y (1,0)) x‖ ≤ _
  simpa only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one,
    one_mul, norm_iteratedFDeriv_fderiv] using hh

end QuantitativePaper
