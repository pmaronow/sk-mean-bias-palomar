module
public import QuantitativeFollowup.FollowupCavityNodeBConvolution
public import QuantitativeFollowup.FollowupCavityNodeBResponse
public import FourPapersCommon.FiniteStateRankOneResponse

@[expose] public section

/-! Actual differentiation of a single spatial diagonal variance. The
threefold Gaussian schedule is identified with the original finite model
before its normalized response is evaluated. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1800000
variable {n k : ℕ}

private theorem binaryGeneratorObservable_eq_response (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (j : ℕ) (H : FiniteStateField (Configuration n)) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade
      (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j)) H
        (cavityCoordinateFeature i) (cavityCoordinateFeature i)+
      anisotropicSchemeMass s j*(fderiv ℝ (finiteStateGaussianTerminalCascade
        (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s) j) H
          (cavityCoordinateFeature i))^2=
      finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput D s) j 0 H (cavityCoordinateEnergyMap i) := by
  have he:=finiteStateCascadeCovarianceResponse_rank_one
    (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D s)
    j 0 H (cavityCoordinateFeature i) i 1
  simpa only [one_smul,one_pow,one_mul,OverlapPaper.sourceKernelExpectation,
    cavityCoordinateEnergyMap] using he.symm

theorem cavityNodeBResponse_eq_original (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1)
    (j J : ℕ) (hj : j<J) (H : FiniteStateField (Configuration n)) :
    finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0) (cavityNodeBScheduleMass s)
      (cavityNodeBCurrentInput D s i M t) (3*j+2) (3*J-(3*j+2)) H
      (cavityCoordinateEnergyInput s i j M)=
      M*(s.q (k+2-j)-s.q (k+1-j))*
        cavityFiniteBinaryGenerator (anisotropicReplaceVariance D i (M*t)) s j J H
          (cavityCoordinateFeature i) := by
  let a:=cavityNodeBScheduleMass s
  let L:=cavityNodeBCurrentInput D s i M t
  let A:=cavityCoordinateEnergyInput s i j M
  have hm1 : a (3*j+1+1)=a (3*j+1) := by
    dsimp [a];simp only [show 3*j+1+1=3*j+2 by omega,
      cavityNodeBScheduleMass_three_one,cavityNodeBScheduleMass_three_two]
  have hm0 : a (3*j+1)=a (3*j) := by dsimp [a];simp
  have he1:=finiteStateCascadeCovarianceResponse_same_mass
    (fun _ : Configuration n=>0) a (cavityNodeBScheduleMass_nonneg s) L
    (3*j+1) (3*J-(3*j+2)) hm1 H A
  have he0:=finiteStateCascadeCovarianceResponse_same_mass
    (fun _ : Configuration n=>0) a (cavityNodeBScheduleMass_nonneg s) L
    (3*j) (3*J-(3*j+2)+1) hm0 H A
  have hidx : 3*J-(3*j+2)+1+1=3*(J-j) := by omega
  change finiteStateCascadeCovarianceResponse _ a L (3*j+1+1) _ H A=_
  rw [he1,he0,hidx]
  change finiteStateCascadeCovarianceResponse _ a L (3*j) (3*(J-j)) H
    (Real.sqrt (M*(s.q (k+2-j)-s.q (k+1-j))) •
      (EuclideanSpace.proj i : Field n→L[ℝ]ℝ).smulRight (cavityCoordinateFeature i))=_
  rw [finiteStateCascadeCovarianceResponse_rank_one,
    Real.sq_sqrt (mul_nonneg hM.le (cavityCellVariance_nonneg s j))]
  have hU : finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) a L (3*j)=
      finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0) (anisotropicSchemeMass s)
        (cavityFiniteEnergyInput (anisotropicReplaceVariance D i (M*t)) s) j :=
    cavityNodeBCascade_three_eq_original D s i M t hM ht j
  have ha3 : a (3*j)=anisotropicSchemeMass s j := cavityNodeBScheduleMass_three s j
  rw [hU,ha3]
  let D':=anisotropicReplaceVariance D i (M*t)
  let G:=fun y : FiniteStateField (Configuration n)=>
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade
      (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D' s) j)) y
        (cavityCoordinateFeature i) (cavityCoordinateFeature i)+
      anisotropicSchemeMass s j*(fderiv ℝ (finiteStateGaussianTerminalCascade
        (fun _ : Configuration n=>0) (anisotropicSchemeMass s) (cavityFiniteEnergyInput D' s) j) y
          (cavityCoordinateFeature i))^2
  have hG : Measurable G := by
    have he : G=fun y=>finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0)
        (anisotropicSchemeMass s) (cavityFiniteEnergyInput D' s) j 0 y (cavityCoordinateEnergyMap i) := by
      funext y;exact binaryGeneratorObservable_eq_response D' s i j y
    rw [he]
    exact finiteStateCascadeCovarianceResponse_measurable _ _ (anisotropicSchemeMass_nonneg s) _ j 0 _
  let C:=2*(finiteStateGaussianGeneratorBound (anisotropicSchemeMass s j)
    (cavityCoordinateEnergyMap i) 1 (finiteStateCascadeHessianBound (anisotropicSchemeMass s) j) : ℝ)
  have hb (y) : |G y|≤C := by
    dsimp [G]
    rw [binaryGeneratorObservable_eq_response D' s i j y]
    exact finiteStateCascadeCovarianceResponse_abs_le _ _ (anisotropicSchemeMass_nonneg s) _ j 0 _ y
  have he:=cavityNodeBRefinedFuture_eq_original D s i M t hM ht j (J-j) G hG C hb H
  change M*(s.q (k+2-j)-s.q (k+1-j))*
    OverlapPaper.sourceKernelExpectation (fun p=>cavityNodeBRefinedKernel D s i M t (3*j+p))
      (3*(J-j)) G H=_
  rw [he]
  rfl

theorem hasDerivAt_cavityNodeBSchedule_response (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (M t : ℝ) (hM : 0<M) (ht : t∈Ioo 0 1)
    (J : ℕ) (H : FiniteStateField (Configuration n)) :
    HasDerivAt (fun u=>finiteStateGaussianScheduledTerminalCascade
      (fun _ : Configuration n=>0) (cavityNodeBScheduleMass s)
      (cavityNodeBScheduleDirection D s i M) cavityNodeBScheduleUp (3*J) u H)
      (M*cavityFiniteNodeBResponse (anisotropicReplaceVariance D i (M*t)) s J H
        (cavityCoordinateFeature i)) t := by
  have hd:=hasDerivAt_cavityNodeBSchedule D s i M t ht J H
  have he : ((1/2 : ℝ)*∑j∈Finset.range J,finiteStateCascadeCovarianceResponse
      (fun _ : Configuration n=>0) (cavityNodeBScheduleMass s)
      (cavityNodeBCurrentInput D s i M t) (3*j+2) (3*J-(3*j+2)) H
      (cavityCoordinateEnergyInput s i j M))=
      M*cavityFiniteNodeBResponse (anisotropicReplaceVariance D i (M*t)) s J H
        (cavityCoordinateFeature i) := by
    unfold cavityFiniteNodeBResponse
    have hs : (∑j∈Finset.range J,finiteStateCascadeCovarianceResponse
        (fun _ : Configuration n=>0) (cavityNodeBScheduleMass s)
        (cavityNodeBCurrentInput D s i M t) (3*j+2) (3*J-(3*j+2)) H
        (cavityCoordinateEnergyInput s i j M))=
        M*∑j∈Finset.range J,(s.q (k+2-j)-s.q (k+1-j))*
          cavityFiniteBinaryGenerator (anisotropicReplaceVariance D i (M*t)) s j J H
            (cavityCoordinateFeature i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [cavityNodeBResponse_eq_original D s i M t hM ht j J (Finset.mem_range.mp hj) H]
      ring
    rw [hs];ring
  rw [he] at hd
  exact hd

/-- Ordinary differentiation in the genuine positive diagonal covariance,
with every incident coupling and the starting history held fixed. -/
theorem hasDerivAt_anisotropicFinitePotential_variance (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (b : ℝ) (hb : 0<b) (J : ℕ)
    (P : AnisotropicParameter n) :
    HasDerivAt (fun u=>anisotropicFinitePotential (anisotropicReplaceVariance D i u) s J P)
      (cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s J (anisotropicEnergyMap D P)
        (cavityCoordinateFeature i)) b := by
  let M:=2*b
  have hM : 0<M := by dsimp [M];linarith
  have ht : b/M∈Ioo (0:ℝ) 1 := by
    have he : b/M=(1/2:ℝ) := by dsimp [M];field_simp
    rw [he];constructor <;> norm_num
  have hMb : M*(b/M)=b := mul_div_cancel₀ b hM.ne'
  have hd:=(hasDerivAt_cavityNodeBSchedule_response D s i M (b/M) hM ht J
    (anisotropicEnergyMap D P)).comp b ((hasDerivAt_id b).div_const M)
  have he : (M*cavityFiniteNodeBResponse (anisotropicReplaceVariance D i (M*(b/M))) s J
      (anisotropicEnergyMap D P) (cavityCoordinateFeature i))*(1/M)=
      cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s J (anisotropicEnergyMap D P)
        (cavityCoordinateFeature i) := by
    rw [hMb];field_simp
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  have hn : Ioo (0:ℝ) M∈nhds b := Ioo_mem_nhds hb (by dsimp [M];linarith)
  filter_upwards [hn] with u hu
  have hut : u/M∈Ioo (0:ℝ) 1 := ⟨div_pos hu.1 hM,(div_lt_one hM).mpr hu.2⟩
  dsimp only [Function.comp_def,id]
  rw [finiteStateGaussianScheduledTerminalCascade_eq_current]
  change anisotropicFinitePotential (anisotropicReplaceVariance D i u) s J P=
    cavityNodeBCascade D s i M (u/M) (3*J) (anisotropicEnergyMap D P)
  rw [cavityNodeBCascade_three_eq_original D s i M (u/M) hM hut J]
  have hMu : M*(u/M)=u := mul_div_cancel₀ u hM.ne'
  simp only [cavityNodeBOriginalCascade,hMu,anisotropicFinitePotential,
    anisotropicReplaceVariance_energyMap]
  unfold cavityFiniteEnergyInput
  rw [anisotropicReplaceVariance_energyMap]

theorem hasDerivAt_anisotropicFinitePotential_variance_self (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (J : ℕ) (P : AnisotropicParameter n) :
    HasDerivAt (fun u=>anisotropicFinitePotential (anisotropicReplaceVariance D i u) s J P)
      (cavityFiniteNodeBResponse D s J (anisotropicEnergyMap D P) (cavityCoordinateFeature i))
      (D.variance i) := by
  simpa only [anisotropicReplaceVariance_self] using
    hasDerivAt_anisotropicFinitePotential_variance D s i (D.variance i) (D.variance_pos i) J P

end QuantitativeFollowup
