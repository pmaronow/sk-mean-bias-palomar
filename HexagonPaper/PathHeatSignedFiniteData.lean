module
public import HexagonPaper.PathHeatSignedJetPullback
public import QuantitativePaper.VectorExponentialHeatData

@[expose] public section

/-! Genuine finite exponential heat data from the source signed path jets.
The growth bound and all first/second derivative bounds are derived inside
this module, rather than being supplied as a Gaussian datum premise. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff
namespace HexagonPaper
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def pathHeat_heatDatum_of_bounded_finite_jets
    (f g : Field n→ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (B Sf Mf Pg Qg C0 C1 : ℝ≥0)
    (hg0 : ∀x,‖g x‖≤B) (hf1 : ∀x,‖fderiv ℝ f x‖≤Sf)
    (hf2 : ∀x,‖vectorHessian f x‖≤Mf)
    (hg1 : ∀x,‖fderiv ℝ g x‖≤Pg) (hg2 : ∀x,‖vectorHessian g x‖≤Qg)
    (hval : ∀x,|f x|≤C0+C1*‖x‖) :
    VectorHeatDatum (fun x=>Real.exp (f x)*g x) := by
  let T : ℝ := 1+Sf+Mf
  let G : ℕ→ℝ := fun _=>B+Pg+Qg
  have hT : 1≤T := by dsimp [T];linarith [Sf.coe_nonneg,Mf.coe_nonneg]
  have hG : ∀i,0≤G i := by intro i;dsimp [G];positivity
  have hfj : ∀ i : ℕ, 1 ≤ i → i ≤ 2 → ∀x,‖iteratedFDeriv ℝ i f x‖≤T^i := by
    intro i hi hi' x
    interval_cases i
    · rw [norm_iteratedFDeriv_one,pow_one]
      exact (hf1 x).trans (by dsimp [T];linarith [Sf.coe_nonneg,Mf.coe_nonneg])
    · rw [←vectorHessian_norm_eq]
      exact (hf2 x).trans (by dsimp [T];nlinarith [Sf.coe_nonneg,Mf.coe_nonneg])
  have hgj : ∀ i : ℕ, i ≤ 2 → ∀x,‖iteratedFDeriv ℝ i g x‖≤G i := by
    intro i hi x
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      exact (hg0 x).trans (by dsimp [G];linarith [B.coe_nonneg,Pg.coe_nonneg,Qg.coe_nonneg])
    · rw [norm_iteratedFDeriv_one]
      exact (hg1 x).trans (by dsimp [G];linarith [B.coe_nonneg,Pg.coe_nonneg,Qg.coe_nonneg])
    · rw [←vectorHessian_norm_eq]
      exact (hg2 x).trans (by dsimp [G];linarith [B.coe_nonneg,Pg.coe_nonneg,Qg.coe_nonneg])
  let P := gaussianWeightedJetCoefficient 1 T G
  have hP (j : ℕ) : 0≤P j := gaussianWeightedJetCoefficient_nonneg 1 T (by linarith) G hG j
  let C := (P 0+P 1+P 2)*Real.exp C0
  have hC : 0≤C := mul_nonneg (add_nonneg (add_nonneg (hP 0) (hP 1)) (hP 2)) (Real.exp_pos _).le
  have hc (j : ℕ) (hj : j≤2) : P j≤P 0+P 1+P 2 := by
    interval_cases j <;> linarith [hP 0,hP 1,hP 2]
  have hb (j : ℕ) (hj : j≤2) (x : Field n) :
      ‖iteratedFDeriv ℝ j (fun y=>Real.exp (f y)*g y) x‖≤C*Real.exp (C1*‖x‖) := by
    have hjet := norm_iteratedFDeriv_exp_mul_observable_le f g hf hg 1 T
      (by linarith) G hG hfj hgj hj x
    simp only [one_mul] at hjet
    have he : Real.exp (f x)≤Real.exp C0*Real.exp (C1*‖x‖) := by
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hval x))
    apply hjet.trans
    have hh := mul_le_mul (hc j hj) he (Real.exp_pos _).le
      (add_nonneg (add_nonneg (hP 0) (hP 1)) (hP 2))
    simpa only [C,mul_assoc] using hh
  refine {
    regularity := hf.exp.mul hg
    growthBound := ⟨C,hC⟩
    rate := C1
    value_bound := fun x=>by
      change ‖Real.exp (f x)*g x‖≤C*Real.exp (C1*‖x‖)
      simpa only [norm_iteratedFDeriv_zero] using hb 0 (by omega) x
    first_bound := fun x=>by rw [←norm_iteratedFDeriv_one];exact hb 1 (by omega) x
    second_bound := fun x=>by rw [vectorHessian_norm_eq];exact hb 2 le_rfl x
  }

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
local instance instDataPathNormed : NormedAddCommGroup C(X,ℝ) := inferInstance
local instance instDataPathSpace : NormedSpace ℝ C(X,ℝ) := inferInstance
local instance instDataPathTopo : TopologicalSpace C(X,ℝ) := instDataPathNormed.toUniformSpace.toTopologicalSpace
local instance instDataPathAdd : AddCommGroup C(X,ℝ) := instDataPathNormed.toAddCommGroup
local instance instDataPathMod : Module ℝ C(X,ℝ) := instDataPathSpace.toModule
local instance instDataDualNormed : NormedAddCommGroup (C(X,ℝ)→L[ℝ]ℝ) := inferInstance
local instance instDataDualSpace : NormedSpace ℝ (C(X,ℝ)→L[ℝ]ℝ) := inferInstance
local instance instDataDualTopo : TopologicalSpace (C(X,ℝ)→L[ℝ]ℝ) := instDataDualNormed.toUniformSpace.toTopologicalSpace
local instance instDataDualAdd : AddCommGroup (C(X,ℝ)→L[ℝ]ℝ) := instDataDualNormed.toAddCommGroup
local instance instDataDualMod : Module ℝ (C(X,ℝ)→L[ℝ]ℝ) := instDataDualSpace.toModule
local instance instDataFiniteDualNormed : NormedAddCommGroup (Field n→L[ℝ]ℝ) := inferInstance
local instance instDataFiniteDualSpace : NormedSpace ℝ (Field n→L[ℝ]ℝ) := inferInstance
local instance instDataFiniteDualTopo : TopologicalSpace (Field n→L[ℝ]ℝ) :=
  instDataFiniteDualNormed.toUniformSpace.toTopologicalSpace
local instance instDataFiniteDualAdd : AddCommGroup (Field n→L[ℝ]ℝ) := instDataFiniteDualNormed.toAddCommGroup
local instance instDataFiniteDualMod : Module ℝ (Field n→L[ℝ]ℝ) := instDataFiniteDualSpace.toModule

theorem norm_pathHeatPullbackScore_le (A : Field n→L[ℝ]C(X,ℝ)) (S : SignedMeasure X)
    (L K : ℝ≥0) (hS : signedTV S≤L) (hA : ‖A‖≤K) :
    ‖pathHeatPullbackScore A S‖≤L*K := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul ((norm_pathHeatSignedScore_le S).trans hS) hA (norm_nonneg _) L.coe_nonneg)

theorem norm_pathHeatPullbackHessian_le (A : Field n→L[ℝ]C(X,ℝ)) (M : SignedMeasure (X×X))
    (L K : ℝ≥0) (hM : signedTV M≤L) (hA : ‖A‖≤K) :
    ‖pathHeatPullbackHessian A M‖≤L*K^2 := by
  apply (pathHeatPullbackHessian A M).opNorm_le_bound₂ (by positivity)
  intro h k
  have hh : ‖A h‖≤K*‖h‖ := (A.le_opNorm h).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hk : ‖A k‖≤K*‖k‖ := (A.le_opNorm k).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hb := (pathHeatSignedHessian M).le_opNorm₂ (A h) (A k)
  have hnorm := (norm_pathHeatSignedHessian_le M).trans hM
  have hc := mul_le_mul (mul_le_mul hnorm hh (norm_nonneg _) L.coe_nonneg) hk
    (norm_nonneg _) (mul_nonneg L.coe_nonneg (mul_nonneg K.coe_nonneg (norm_nonneg _)))
  exact hb.trans (hc.trans_eq (by ring))

def pathHeat_finiteData_from_signedJets
    (A : Field n→L[ℝ]C(X,ℝ)) (ell Phi : C(X,ℝ)→ℝ)
    (S P : C(X,ℝ)→SignedMeasure X) (M Q : C(X,ℝ)→SignedMeasure (X×X))
    (hEll : ∀p,HasFDerivAt ell (pathHeatSignedScore (S p)) p)
    (hPhi : ∀p,HasFDerivAt Phi (pathHeatSignedScore (P p)) p)
    (hS : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (S q)) (pathHeatSignedHessian (M p)) p)
    (hP : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (P q)) (pathHeatSignedHessian (Q p)) p)
    (hMc : ∀p,Tendsto (fun q=>signedTV (M q-M p)) (𝓝 p) (𝓝 0))
    (hQc : ∀p,Tendsto (fun q=>signedTV (Q q-Q p)) (𝓝 p) (𝓝 0))
    (B Ls Lm Lp Lq C0 C1 K : ℝ≥0)
    (hSb : ∀p,signedTV (S p)≤Ls) (hMb : ∀p,signedTV (M p)≤Lm)
    (hPb : ∀p,signedTV (P p)≤Lp) (hQb : ∀p,signedTV (Q p)≤Lq)
    (hPhib : ∀p,|Phi p|≤B) (hEllb : ∀p,|ell p|≤C0+C1*‖p‖) (hA : ‖A‖≤K) :
    VectorHeatDatum (fun x=>Real.exp (ell (A x))) ×
    VectorHeatDatum (fun x=>Real.exp (ell (A x))*Phi (A x)) := by
  let f : Field n→ℝ := fun x=>ell (A x)
  let g : Field n→ℝ := fun x=>Phi (A x)
  have hf : ContDiff ℝ 2 f := contDiff_two_pathHeatPullback A ell S M hEll hS hMc
  have hg : ContDiff ℝ 2 g := contDiff_two_pathHeatPullback A Phi P Q hPhi hP hQc
  have hf1 (x : Field n) : ‖fderiv ℝ f x‖≤(Ls*K:ℝ≥0) := by
    rw [(hasFDerivAt_pathHeatPullback A ell S hEll x).fderiv]
    exact norm_pathHeatPullbackScore_le A _ Ls K (hSb _) hA
  have hg1 (x : Field n) : ‖fderiv ℝ g x‖≤(Lp*K:ℝ≥0) := by
    rw [(hasFDerivAt_pathHeatPullback A Phi P hPhi x).fderiv]
    exact norm_pathHeatPullbackScore_le A _ Lp K (hPb _) hA
  have hess (v : C(X,ℝ)→ℝ) (R : C(X,ℝ)→SignedMeasure X) (T : C(X,ℝ)→SignedMeasure (X×X))
      (hv : ∀p,HasFDerivAt v (pathHeatSignedScore (R p)) p)
      (hr : ∀p,HasFDerivAt (fun q=>pathHeatSignedScore (R q)) (pathHeatSignedHessian (T p)) p)
      (x : Field n) : vectorHessian (fun y=>v (A y)) x=pathHeatPullbackHessian A (T (A x)) := by
    ext h k
    exact pathHeatPullback_second_fderiv A v R T hv hr x h k
  have hf2 (x : Field n) : ‖vectorHessian f x‖≤(Lm*K^2:ℝ≥0) := by
    rw [hess ell S M hEll hS x]
    exact norm_pathHeatPullbackHessian_le A _ Lm K (hMb _) hA
  have hg2 (x : Field n) : ‖vectorHessian g x‖≤(Lq*K^2:ℝ≥0) := by
    rw [hess Phi P Q hPhi hP x]
    exact norm_pathHeatPullbackHessian_le A _ Lq K (hQb _) hA
  have hg0 (x : Field n) : ‖g x‖≤B := by simpa only [g,Real.norm_eq_abs] using hPhib (A x)
  have hf0 (x : Field n) : |f x|≤C0+(C1*K:ℝ≥0)*‖x‖ := by
    apply (hEllb (A x)).trans
    have hb := mul_le_mul_of_nonneg_left ((A.le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) C1.coe_nonneg
    simpa only [NNReal.coe_mul,mul_assoc,add_comm] using add_le_add_left hb (C0:ℝ)
  constructor
  · have hd := pathHeat_heatDatum_of_bounded_finite_jets f (fun _=>1) hf contDiff_const
      1 (Ls*K) (Lm*K^2) 0 0 C0 (C1*K) (fun _=>by norm_num) hf1 hf2
      (fun _=>by simp) (fun _=>by simp [vectorHessian]) hf0
    exact {
      regularity := hf.exp
      growthBound := hd.growthBound
      rate := hd.rate
      value_bound := fun x=>by simpa only [f,mul_one] using hd.value_bound x
      first_bound := fun x=>by simpa only [f,mul_one] using hd.first_bound x
      second_bound := fun x=>by simpa only [f,mul_one] using hd.second_bound x
    }
  · exact pathHeat_heatDatum_of_bounded_finite_jets f g hf hg B (Ls*K) (Lm*K^2)
      (Lp*K) (Lq*K^2) C0 (C1*K) hg0 hf1 hf2 hg1 hg2 hf0

end HexagonPaper
