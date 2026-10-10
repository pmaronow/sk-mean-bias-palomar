module
public import QuantitativeFollowup.ScalarTwoTransport
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-! Actual joint smoothness of two independent finite-profile transports.
Repeated overlap levels retain zero amplitudes identically; every other
Gaussian variance is strictly positive at the base point. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators ContDiff
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

def scalarTwoTransportAmplitude (s : RSBScheme k) (β : ℝ)
    (φ ψ : C(Paper.Overlap,ℝ)) (z : ℝ×ℝ) : QuantitativePaper.Field (k+2) :=
  WithLp.toLp 2 (fun i : Fin (k+2)=>Real.sqrt (β^2*(s.q (i+1)-s.q i+
    z.1*(φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i))+
    z.2*(ψ (scalarSchemeTransportNode s (i+1))-ψ (scalarSchemeTransportNode s i)))))

theorem scalarTwoTransportAmplitude_eq_single (s : RSBScheme k) (β : ℝ)
    (φ ψ : C(Paper.Overlap,ℝ)) (z : ℝ×ℝ) :
    scalarTwoTransportAmplitude s β φ ψ z=
      scalarTransportAmplitude s β (scalarTwoDirection φ ψ z) 1 := by
  ext i
  change Real.sqrt _=Real.sqrt _
  congr 1
  simp only [scalarTwoDirection_apply]
  ring

theorem contDiffAt_scalarTwoTransportAmplitude_zero (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (φ ψ : C(Paper.Overlap,ℝ)) :
    ContDiffAt ℝ ∞ (scalarTwoTransportAmplitude s β φ ψ) (0,0) := by
  have hc (i : Fin (k+2)) : ContDiffAt ℝ ∞
      (fun z : ℝ×ℝ=>Real.sqrt (β^2*(s.q (i+1)-s.q i+
        z.1*(φ (scalarSchemeTransportNode s (i+1))-φ (scalarSchemeTransportNode s i))+
        z.2*(ψ (scalarSchemeTransportNode s (i+1))-ψ (scalarSchemeTransportNode s i))))) (0,0) := by
    by_cases he : s.q i=s.q (i+1)
    · have hn : scalarSchemeTransportNode s i=scalarSchemeTransportNode s (i+1) := by
        unfold scalarSchemeTransportNode;rw [he]
      simp only [he,hn,sub_self,mul_zero,add_zero,Real.sqrt_zero]
      exact contDiffAt_const
    · have hlt : s.q i<s.q (i+1) := lt_of_le_of_ne (s.q_mono i (by omega)) he
      have hp : β^2*(s.q (i+1)-s.q i)>0 := mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hlt)
      apply ContDiffAt.sqrt (by fun_prop)
      simpa only [zero_mul,add_zero] using hp.ne'
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (k+2)=>ℝ)).symm.contDiff.contDiffAt.comp
    (0,0) (contDiffAt_pi.mpr hc)

def scalarTwoTransportSmoothFunctional (s : RSBScheme k) (β : ℝ)
    (φ ψ : C(Paper.Overlap,ℝ)) (z : ℝ×ℝ) : ℝ :=
  Real.log 2+scalarAmplitudeRecursion s (k+2)
    (scalarTwoTransportAmplitude s β φ ψ z,0,0)-β^2/4+
    β^2/4*(∫q : Paper.Overlap,((q:ℝ)+z.1*φ q+z.2*ψ q)^2
      ∂(parisiSchemeMeasure s:Measure Paper.Overlap))

theorem contDiffAt_scalarAmplitudeRecursion (s : RSBScheme k) (j : ℕ)
    (w : ScalarAmplitudeState (k+2)) : ContDiffAt ℝ ∞ (scalarAmplitudeRecursion s j) w := by
  let R : ℝ≥0 := ⟨‖w.1‖+1,by positivity⟩
  have hw : w∈scalarAmplitudeDomain (k+2) R := by change ‖w.1‖<‖w.1‖+1;linarith
  exact (exponentialSmoothOn_scalarAmplitudeRecursion s R j).smooth w hw

theorem contDiffAt_scalarTwoTransportSmoothFunctional_zero (s : RSBScheme k)
    (β : ℝ) (hβ : β≠0) (φ ψ : C(Paper.Overlap,ℝ)) :
    ContDiffAt ℝ ∞ (scalarTwoTransportSmoothFunctional s β φ ψ) (0,0) := by
  have hcurve : ContDiffAt ℝ ∞
      (fun z : ℝ×ℝ=>((scalarTwoTransportAmplitude s β φ ψ z,0,0):ScalarAmplitudeState (k+2))) (0,0) :=
    (contDiffAt_scalarTwoTransportAmplitude_zero s β hβ φ ψ).prodMk
      ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ×ℝ=>(0:QuantitativePaper.Field (k+2))) (0,0)).prodMk
        (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ×ℝ=>(0:ℝ)) (0,0)))
  have hP : ContDiffAt ℝ ∞ (fun z : ℝ×ℝ=>scalarAmplitudeRecursion s (k+2)
      (scalarTwoTransportAmplitude s β φ ψ z,0,0)) (0,0) :=
    ContDiffAt.comp (f:=fun z : ℝ×ℝ=>((scalarTwoTransportAmplitude s β φ ψ z,0,0):ScalarAmplitudeState (k+2)))
      (g:=scalarAmplitudeRecursion s (k+2)) (0,0)
      (contDiffAt_scalarAmplitudeRecursion s (k+2)
        (scalarTwoTransportAmplitude s β φ ψ (0,0),0,0)) hcurve
  have hQ : ContDiffAt ℝ ∞ (fun z : ℝ×ℝ=>∫q : Paper.Overlap,
      ((q:ℝ)+z.1*φ q+z.2*ψ q)^2 ∂(parisiSchemeMeasure s:Measure Paper.Overlap)) (0,0) := by
    simp only [integral_scalarScheme_nodes]
    apply ContDiffAt.sum
    intro i _
    fun_prop
  change ContDiffAt ℝ ∞ (fun z : ℝ×ℝ=>Real.log 2+scalarAmplitudeRecursion s (k+2)
    (scalarTwoTransportAmplitude s β φ ψ z,0,0)-β^2/4+β^2/4*(∫q : Paper.Overlap,
      ((q:ℝ)+z.1*φ q+z.2*ψ q)^2 ∂(parisiSchemeMeasure s:Measure Paper.Overlap))) (0,0)
  exact ((contDiffAt_const.add hP).sub contDiffAt_const).add (contDiffAt_const.mul hQ)

theorem scalarTwoTransportSmoothFunctional_eq_actual (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ ψ : C(Paper.Overlap,ℝ)) (Lφ Lψ : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hψ : LipschitzWith Lψ ψ)
    (hφ0 : φ 0=0) (hφ1 : φ 1=0) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0)
    (z : ℝ×ℝ) (hz : |z.1| *Lφ+|z.2| *Lψ<1) :
    scalarTwoTransportSmoothFunctional s β φ ψ z=
      scalarTwoTransportFunctional β (parisiSchemeMeasure s) φ ψ z := by
  let χ := scalarTwoDirection φ ψ z
  let L : ℝ≥0 := ‖z.1‖₊*Lφ+‖z.2‖₊*Lψ
  have hχ : LipschitzWith L χ := lipschitzWith_scalarTwoDirection φ ψ Lφ Lψ hφ hψ z
  obtain ⟨hχ0,hχ1⟩ := scalarTwoDirection_endpoints φ ψ hφ0 hφ1 hψ0 hψ1 z
  have hL : |(1:ℝ)| *L<1 := by simpa only [L,NNReal.coe_add,NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,abs_one,one_mul] using hz
  let r := scalarTransportScheme s χ L hχ hχ0 hχ1 1 hL
  have hp := scalarAmplitudeRecursion_eq_potential s r β hβ (fun _=>rfl)
    (scalarTransportAmplitude s β χ 1)
    (scalarTransportAmplitude_square s β χ L hχ hχ0 hχ1 1 hL) (k+2) le_rfl 0 0
  have hzroot : r.q 0=0 := r.q_zero
  simp only [Nat.sub_self,hzroot,scalarAmplitudeField,inner_zero_right,add_zero] at hp
  dsimp only [r] at hp
  rw [scalarTransportScheme_measure] at hp
  change scalarTwoTransportSmoothFunctional s β φ ψ z=scalarTransportFunctional β (parisiSchemeMeasure s) χ 1
  rw [scalarTransportFunctional_eq_second_moment,scalarTwoTransportSmoothFunctional,
    scalarTwoTransportAmplitude_eq_single,hp]
  congr 1
  congr 1
  apply integral_congr_ae
  exact .of_forall fun q=>by
    change ((q:ℝ)+z.1*φ q+z.2*ψ q)^2=(scalarLevelTransport χ 1 q:ℝ)^2
    rw [scalarLevelTransport_eq_affine χ L hχ hχ0 hχ1 1 hL.le]
    simp only [χ,scalarTwoDirection_apply,one_mul]
    ring

theorem contDiffAt_scalarTwoTransportFunctional_zero (s : RSBScheme k) (β : ℝ)
    (hβ : β≠0) (φ ψ : C(Paper.Overlap,ℝ)) (Lφ Lψ : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hψ : LipschitzWith Lψ ψ)
    (hφ0 : φ 0=0) (hφ1 : φ 1=0) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0) :
    ContDiffAt ℝ ∞ (scalarTwoTransportFunctional β (parisiSchemeMeasure s) φ ψ) (0,0) := by
  apply (contDiffAt_scalarTwoTransportSmoothFunctional_zero s β hβ φ ψ).congr_of_eventuallyEq
  have hn : {z : ℝ×ℝ | |z.1| *Lφ+|z.2| *Lψ<1}∈𝓝 (0,0) :=
    (isOpen_lt ((continuous_abs.comp continuous_fst).mul continuous_const |>.add
      ((continuous_abs.comp continuous_snd).mul continuous_const)) continuous_const).mem_nhds
        (by simp)
  filter_upwards [hn] with z hz
  exact (scalarTwoTransportSmoothFunctional_eq_actual s β hβ φ ψ Lφ Lψ hφ hψ hφ0 hφ1 hψ0 hψ1 z hz).symm

end QuantitativeFollowup
