module
public import HexagonPaper.PathHeatFiniteTreeModelLaw

@[expose] public section

/-! Bounded real Brownian clocks have an actual normalized representation.
The scale is fixed on the compact parameter interval, and is obtained from
continuity rather than supplied as an additional manuscript hypothesis. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper FourPapersCommon
open scoped unitInterval Topology BigOperators NNReal
namespace HexagonPaper
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {J : ℕ} {Z : Type*}

def pathHeatRealClockNormalize (c : C(I,ℝ)) (R : ℝ) (hR : 0<R)
    (hc : ∀q,0≤c q) (hbound : ∀q,c q≤R) : C(I,I) :=
  ⟨fun q=>⟨c q/R,div_nonneg (hc q) hR.le,(div_le_one hR).mpr (hbound q)⟩,
    Continuous.subtype_mk (c.continuous.div_const R) _⟩

@[simp] theorem pathHeatRealClockNormalize_apply (c : C(I,ℝ)) (R : ℝ) (hR : 0<R)
    (hc : ∀q,0≤c q) (hbound : ∀q,c q≤R) (q : I) :
    (pathHeatRealClockNormalize c R hR hc hbound q:ℝ)=c q/R := rfl

def pathHeatRealClockNormalizeDerivative (dc : C(I,ℝ)) (R : ℝ) : C(I,ℝ) :=
  ⟨fun q=>dc q/R,dc.continuous.div_const R⟩

@[simp] theorem pathHeatRealClockNormalizeDerivative_apply (dc : C(I,ℝ)) (R : ℝ) (q : I) :
    pathHeatRealClockNormalizeDerivative dc R q=dc q/R := rfl

theorem pathHeatRealClock_nonneg (c : C(I,ℝ)) (hc : Monotone c) (hroot : c 0=0) (q : I) :
    0≤c q := by
  rw [←hroot]
  exact hc (unitInterval.nonneg q)

theorem pathHeatRealClockNormalize_root (c : C(I,ℝ)) (R : ℝ) (hR : 0<R)
    (hc : ∀q,0≤c q) (hbound : ∀q,c q≤R) (hroot : c 0=0) :
    pathHeatRealClockNormalize c R hR hc hbound 0=0 := by
  apply Subtype.ext
  simp [hroot]

theorem pathHeatRealClockNormalize_monotone (c : C(I,ℝ)) (R : ℝ) (hR : 0<R)
    (hc : ∀q,0≤c q) (hbound : ∀q,c q≤R) (hm : Monotone c) :
    Monotone (pathHeatRealClockNormalize c R hR hc hbound) := by
  intro q r hqr
  exact div_le_div_of_nonneg_right (hm hqr) hR.le

theorem pathHeatRealClockNormalize_strictMono (c : C(I,ℝ)) (R : ℝ) (hR : 0<R)
    (hc : ∀q,0≤c q) (hbound : ∀q,c q≤R) (hm : StrictMono c) :
    StrictMono (pathHeatRealClockNormalize c R hR hc hbound) := by
  intro q r hqr
  exact div_lt_div_of_pos_right (hm hqr) hR

theorem continuous_pathHeatRealClockNormalize_family [TopologicalSpace Z]
    (c : Z→C(I,ℝ)) (R : ℝ) (hR : 0<R)
    (hc : ∀z q,0≤c z q) (hbound : ∀z q,c z q≤R) (hcont : Continuous c) :
    Continuous (fun z=>pathHeatRealClockNormalize (c z) R hR (hc z) (hbound z)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply Continuous.subtype_mk
  exact ((continuous_eval.comp (hcont.comp continuous_fst |>.prodMk continuous_snd))).div_const R

theorem continuous_pathHeatRealClockNormalizeDerivative_family [TopologicalSpace Z]
    (dc : Z→C(I,ℝ)) (R : ℝ) (hcont : Continuous dc) :
    Continuous (fun z=>pathHeatRealClockNormalizeDerivative (dc z) R) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact ((continuous_eval.comp (hcont.comp continuous_fst |>.prodMk continuous_snd))).div_const R

theorem hasDerivAt_pathHeatRealClockNormalize
    (c : ℝ→C(I,ℝ)) (dc : C(I,ℝ)) (R z : ℝ) (hR : 0<R)
    (hc : ∀u q,0≤c u q) (hbound : ∀u q,c u q≤R)
    (hd : ∀q,HasDerivAt (fun u=>c u q) (dc q) z) (q : I) :
    HasDerivAt (fun u=>(pathHeatRealClockNormalize (c u) R hR (hc u) (hbound u) q:ℝ))
      (pathHeatRealClockNormalizeDerivative dc R q) z :=
  (hd q).div_const R

theorem pathHeatRealClockNormalize_covariance_restored (c : C(I,ℝ)) (R : ℝ) (hR : 0<R)
    (hc : ∀q,0≤c q) (hbound : ∀q,c q≤R) (q : I) :
    (Real.sqrt R)^2*(pathHeatRealClockNormalize c R hR hc hbound q:ℝ)=c q := by
  rw [Real.sq_sqrt hR.le,pathHeatRealClockNormalize_apply]
  field_simp

theorem pathHeatRealClockNormalize_derivative_restored (dc : C(I,ℝ)) (R : ℝ) (hR : 0<R)
    (q : I) : (Real.sqrt R)^2*pathHeatRealClockNormalizeDerivative dc R q=dc q := by
  rw [Real.sq_sqrt hR.le,pathHeatRealClockNormalizeDerivative_apply]
  field_simp

theorem exists_pathHeatRealClock_uniform_scale [TopologicalSpace Z] [CompactSpace Z]
    (c : Z→Fin J→C(I,ℝ)) (hc : ∀j,Continuous (fun z=>c z j)) :
    ∃R : ℝ,0<R ∧ ∀z j q,c z j q≤R := by
  obtain ⟨R,hR,hbound⟩ := exists_pathHeatFiniteVariance_uniform_scale
    (fun z j=>‖c z j‖) (fun j=>(hc j).norm)
  refine ⟨R,hR,?_⟩
  intro z j q
  exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm (c z j) q).trans (hbound z j))

end HexagonPaper
