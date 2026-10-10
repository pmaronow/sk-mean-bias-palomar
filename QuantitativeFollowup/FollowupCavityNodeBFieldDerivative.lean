module
public import QuantitativeFollowup.FollowupCavityNodeBDerivative
public import QuantitativeFollowup.FollowupCavityPathVarianceSmooth

@[expose] public section

/-! The literal diagonal covariance derivative at every starting field,
before any disorder-coordinate parametrization. -/
noncomputable section
open Set Filter
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2000000
variable {n k : ℕ}

theorem hasDerivAt_cavityFinitePotential_variance_field (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : Fin n) (b : ℝ) (hb : 0<b) (J : ℕ)
    (H : FiniteStateField (Configuration n)) :
    HasDerivAt (fun u=>finiteStateGaussianTerminalCascade (fun _ : Configuration n=>0)
      (anisotropicSchemeMass s) (cavityFiniteEnergyInput (anisotropicReplaceVariance D i u) s) J H)
      (cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s J H (cavityCoordinateFeature i)) b := by
  let M:=2*b
  have hM : 0<M := by dsimp [M];linarith
  have ht : b/M∈Ioo (0:ℝ) 1 := by
    have he : b/M=(1/2:ℝ) := by dsimp [M];field_simp
    rw [he];constructor <;> norm_num
  have hMb : M*(b/M)=b := mul_div_cancel₀ b hM.ne'
  have hd:=(hasDerivAt_cavityNodeBSchedule_response D s i M (b/M) hM ht J H).comp b
    ((hasDerivAt_id b).div_const M)
  have he : (M*cavityFiniteNodeBResponse (anisotropicReplaceVariance D i (M*(b/M))) s J H
      (cavityCoordinateFeature i))*(1/M)=
      cavityFiniteNodeBResponse (anisotropicReplaceVariance D i b) s J H (cavityCoordinateFeature i) := by
    rw [hMb];field_simp
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  have hn : Ioo (0:ℝ) M∈𝓝 b := Ioo_mem_nhds hb (by dsimp [M];linarith)
  filter_upwards [hn] with u hu
  have hut : u/M∈Ioo (0:ℝ) 1 := ⟨div_pos hu.1 hM,(div_lt_one hM).mpr hu.2⟩
  dsimp only [Function.comp_def,id]
  rw [finiteStateGaussianScheduledTerminalCascade_eq_current]
  change finiteStateGaussianTerminalCascade _ _ _ J H=cavityNodeBCascade D s i M (u/M) (3*J) H
  rw [cavityNodeBCascade_three_eq_original D s i M (u/M) hM hut J]
  have hMu : M*(u/M)=u := mul_div_cancel₀ u hM.ne'
  simp only [cavityNodeBOriginalCascade,hMu]

end QuantitativeFollowup
