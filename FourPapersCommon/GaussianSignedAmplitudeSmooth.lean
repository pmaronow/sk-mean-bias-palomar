module
public import FourPapersCommon.GaussianSmoothOperatorParameter
public import FourPapersCommon.GaussianTwoMaskScale
public import FourPapersCommon.GaussianSignFlips
public import FourPapersCommon.LocalEvenRadialTransform

@[expose] public section

/-! Signed-amplitude smoothness and the genuine variance-zero boundary
for simultaneous increasing root and decreasing path clocks. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff BigOperators
namespace FourPapersCommon
open QuantitativePaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ ι

def gaussianSignedAmplitudeScale (pR pP : ι→Bool) (d alpha h : ℝ) : E→L[ℝ]E:=
  ∑i,(PiLp.proj 2 (fun _ : ι=>ℝ) i).smulRight
    ((if pR i then h else if pP i then Real.sqrt (d-alpha*h^2) else 1)•
      EuclideanSpace.basisFun ι ℝ i)

@[simp] theorem gaussianSignedAmplitudeScale_coordinate (pR pP : ι→Bool)
    (d alpha h : ℝ) (z:E) (i:ι) :
    gaussianSignedAmplitudeScale pR pP d alpha h z i=
      (if pR i then h else if pP i then Real.sqrt (d-alpha*h^2) else 1)*z i := by
  simp only [gaussianSignedAmplitudeScale,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply,PiLp.proj_apply,smul_smul,
    WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,
    EuclideanSpace.basisFun_apply,PiLp.single_apply]
  simp only [mul_ite,mul_zero,mul_one,ite_mul,zero_mul,one_mul]
  rw [Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

theorem gaussianSignedAmplitudeScale_sqrt (pR pP : ι→Bool) (d alpha u : ℝ)
    (hu:0≤u) : gaussianSignedAmplitudeScale pR pP d alpha (Real.sqrt u)=
      gaussianTwoMaskScale pR pP d alpha u := by
  unfold gaussianSignedAmplitudeScale gaussianTwoMaskScale gaussianTwoMaskCoefficient
  rw [Real.sq_sqrt hu]

def gaussianSignedAmplitudeIntegral (pR pP : ι→Bool) (d alpha : ℝ)
    (F:ℝ×E→ℝ) (h:ℝ) : ℝ:=
  ∫z:E,F (d-alpha*h^2,gaussianSignedAmplitudeScale pR pP d alpha h z)∂stdGaussian E

/-- Gaussian reflection proves evenness of the actual signed integral;
no symmetry of the observable is assumed. -/
theorem gaussianSignedAmplitudeIntegral_even (pR pP : ι→Bool) (d alpha : ℝ)
    (F:ℝ×E→ℝ) (h:ℝ) (hF:Measurable (fun y:E=>F (d-alpha*h^2,y))) :
    gaussianSignedAmplitudeIntegral pR pP d alpha F (-h)=
      gaussianSignedAmplitudeIntegral pR pP d alpha F h := by
  let ε : ι→ℝ:=fun i=>if pR i then -1 else 1
  have hε:∀i,|ε i|=1:=by intro i;dsimp [ε];split <;> norm_num
  let L:=coordinateSignCLM ε hε
  have hmap : (stdGaussian E).map L=stdGaussian E:=
    stdGaussian_map (coordinateSignEquiv ε hε)
  have hmeas : Measurable (fun z:E=>F (d-alpha*h^2,gaussianSignedAmplitudeScale pR pP d alpha h z)):=
    hF.comp (gaussianSignedAmplitudeScale pR pP d alpha h).measurable
  have he (z:E) : gaussianSignedAmplitudeScale pR pP d alpha (-h) z=
      gaussianSignedAmplitudeScale pR pP d alpha h (L z) := by
    ext i
    simp only [gaussianSignedAmplitudeScale_coordinate,coordinateSignCLM_apply,L,ε,neg_sq]
    cases hp:pR i <;> simp [hp] <;> ring
  unfold gaussianSignedAmplitudeIntegral
  simp_rw [neg_sq,he]
  rw [←integral_map L.measurable.aemeasurable hmeas.aestronglyMeasurable,hmap]

theorem exists_signed_amplitude_radius (d alpha:ℝ) (ha:0≤alpha) (hd:0<d-alpha) :
    ∃R:ℝ,1<R ∧ 0<d-alpha*R^2 := by
  let c:=d-alpha
  let e:=min 1 (c/(4*(alpha+1)))
  have hc:0<c:=hd
  have he:0<e:=lt_min zero_lt_one (div_pos hc (by positivity))
  have he1:e≤1:=min_le_left _ _
  have hem:alpha*e≤c/4:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) (c/(4*(alpha+1)))) ha
    have hh':alpha*(c/(4*(alpha+1)))≤c/4:=by
      rw [←mul_div_assoc,div_le_iff₀ (by positivity : 0<4*(alpha+1))]
      nlinarith
    exact hh.trans hh'
  refine ⟨1+e,by linarith,?_⟩
  have he2:e^2≤e:=by nlinarith
  have hh:=mul_le_mul_of_nonneg_left he2 ha
  dsimp only [c] at *
  nlinarith

private theorem common_compact_jet_bound {G:Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g:ℝ→G) (U:Set ℝ) (hU:IsOpen U) (hg:ContDiffOn ℝ ∞ g U)
    (S:Set ℝ) (hS:IsCompact S) (hSU:S⊆U) (N:ℕ) :
    ∃K:ℝ,1≤K ∧ ∀j,j≤N→∀x∈S,‖iteratedFDeriv ℝ j g x‖≤K := by
  classical
  have hb (j:Fin (N+1)) : ∃K:ℝ,∀x∈S,‖iteratedFDeriv ℝ j.1 g x‖≤K :=
    hS.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hg hU (by simp)).mono hSU)
  choose K hK using hb
  let B:=1+∑j:Fin (N+1),max 0 (K j)
  have hsum:0≤∑j:Fin (N+1),max 0 (K j):=Finset.sum_nonneg (fun _ _=>le_max_left _ _)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro j hj x hx
  let i:Fin (N+1):=⟨j,by omega⟩
  have hs:=Finset.single_le_sum (fun i _=>le_max_left (0:ℝ) (K i)) (Finset.mem_univ i)
  exact (hK i x hx).trans ((le_max_right _ _).trans (by dsimp [B];linarith))

/-- Local full smoothness in signed amplitude, including amplitude zero. -/
theorem contDiffOn_gaussianSignedAmplitudeIntegral (pR pP : ι→Bool) (d alpha R : ℝ)
    (ha:0≤alpha) (hR:0<R) (hb:0<d-alpha*R^2)
    (F:ℝ×E→ℝ)
    (hF:ExponentialSmoothOn F ((Ioo ((d-alpha*R^2)/2) (d+1))×ˢ(univ:Set E))) :
    ContDiffOn ℝ ∞ (gaussianSignedAmplitudeIntegral pR pP d alpha F) (Ioo (-R) R) := by
  let b:ℝ→ℝ:=fun h=>d-alpha*h^2
  let A:ℝ→E→L[ℝ]E:=gaussianSignedAmplitudeScale pR pP d alpha
  let g:ℝ→ℝ×(E→L[ℝ]E):=fun h=>(b h,A h)
  let W:=b⁻¹' Ioi 0
  have hW:IsOpen W:=isOpen_Ioi.preimage (by fun_prop)
  have hbs:ContDiffOn ℝ ∞ b W:=by fun_prop
  have hA:ContDiffOn ℝ ∞ A W:=by
    unfold A gaussianSignedAmplitudeScale
    apply ContDiffOn.sum
    intro i _
    have hc:ContDiffOn ℝ ∞ (fun h:ℝ=>if pR i then h else if pP i then Real.sqrt (b h) else 1) W:=by
      split
      · exact contDiffOn_id
      · split
        · exact hbs.sqrt (fun h hh=>(show 0<b h from hh).ne')
        · exact contDiffOn_const
    exact contDiffOn_const.smulRight (hc.smul contDiffOn_const)
  have hg:ContDiffOn ℝ ∞ g W:=hbs.prodMk hA
  have hclosed:Icc (-R) R⊆W:=by
    intro h hh
    have hh2:h^2≤R^2:=by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg h) hR.le).mpr (abs_le.mpr hh)
    have hmul:=mul_le_mul_of_nonneg_left hh2 ha
    change 0<b h
    dsimp only [b]
    linarith
  have hgu:ContDiffOn ℝ ∞ g (Ioo (-R) R):=hg.mono (Ioo_subset_Icc_self.trans hclosed)
  apply contDiffOn_gaussian_operator_parameter F ((d-alpha*R^2)/2) (d+1) hF g
    (Ioo (-R) R) isOpen_Ioo hgu
  · intro h hh
    have hp:=hclosed (Ioo_subset_Icc_self hh)
    have hm:=mul_le_mul_of_nonneg_left (show h^2≤R^2 by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg h) hR.le).mpr
        (abs_le.mpr (Ioo_subset_Icc_self hh))) ha
    change d-alpha*h^2∈Ioo ((d-alpha*R^2)/2) (d+1)
    constructor
    · linarith
    · nlinarith [sq_nonneg h]
  · intro N
    obtain ⟨K,hK,hb⟩:=common_compact_jet_bound g W hW hg (Icc (-R) R) isCompact_Icc hclosed N
    exact ⟨K,hK,fun j hj x hx=>hb j hj x (Ioo_subset_Icc_self hx)⟩

/-- The simultaneous two-clock expectation is genuinely smooth on the
closed physical interval, including zero root variance. -/
theorem contDiffOn_gaussianTwoMask_integral_closed (pR pP : ι→Bool) (d alpha : ℝ)
    (ha:0≤alpha) (hd:0<d-alpha) (F:ℝ×E→ℝ)
    (hF:∀l u:ℝ,0<l→ExponentialSmoothOn F ((Ioo l u)×ˢ(univ:Set E))) :
    ContDiffOn ℝ ∞ (fun u=>∫z:E,F (d-alpha*u,gaussianTwoMaskScale pR pP d alpha u z)
      ∂stdGaussian E) (Icc (0:ℝ) 1) := by
  obtain ⟨R,hR,hb⟩:=exists_signed_amplitude_radius d alpha ha hd
  have hs:=contDiffOn_gaussianSignedAmplitudeIntegral pR pP d alpha R ha
    (zero_lt_one.trans hR) hb F (hF _ _ (by linarith))
  have he:∀h∈Ioo (-R) R,gaussianSignedAmplitudeIntegral pR pP d alpha F (-h)=
      gaussianSignedAmplitudeIntegral pR pP d alpha F h := by
    intro h hh
    have hh2:h^2≤R^2:=by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg h) (zero_lt_one.trans hR).le).mpr
        (abs_le.mpr (Ioo_subset_Icc_self hh))
    have hb':0<d-alpha*h^2:=by nlinarith [mul_le_mul_of_nonneg_left hh2 ha]
    have hFs:=hF ((d-alpha*h^2)/2) (d-alpha*h^2+1) (by linarith)
    have hm:Measurable (fun y:E=>F (d-alpha*h^2,y)):=by
      apply Continuous.measurable
      apply continuous_iff_continuousAt.mpr
      intro y
      exact (hFs.smooth _ ⟨⟨by linarith,by linarith⟩,mem_univ _⟩).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt
    exact gaussianSignedAmplitudeIntegral_even pR pP d alpha F h hm
  have hc:=contDiffOn_evenRadialTransform_local
    (gaussianSignedAmplitudeIntegral pR pP d alpha F) R hR hs he
  apply hc.congr
  intro u hu
  simp only [gaussianSignedAmplitudeIntegral,Real.sq_sqrt hu.1,
    gaussianSignedAmplitudeScale_sqrt pR pP d alpha u hu.1]

end FourPapersCommon
