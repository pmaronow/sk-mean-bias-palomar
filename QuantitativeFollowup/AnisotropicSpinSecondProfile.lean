module
public import QuantitativeFollowup.AnisotropicSpinSecondGrid

@[expose] public section

/-! The actual binary terminal-feature Hessian at arbitrary time/profile.
The genuine finite Wiener identities pass through the upward grids with
uniform posterior bounds and atom-exact strict-future dominated convergence. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem anisotropic_spin_second_wholePast_stieltjes_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (e : Fin n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] Z)
    (hZi : Integrable Z (vectorDisorderBrownianMeasure n)) :
    (∫p,Z p*anisotropicProcessSpinSecond D μ q e (g,p.2) ∂vectorDisorderBrownianMeasure n)+
      Paper.parisiCDF μ q*anisotropicSpinSquareMoment D μ g e Z q+
      anisotropicFutureSpinSquareMoment D μ g q e Z=
      ∫p,Z p ∂vectorDisorderBrownianMeasure n := by
  let sj:=fun j=>Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let qj:=fun j=>Paper.parisiGridRound (vectorDyadicIndex j) q
  let Hj:=fun j=>∫p,Z p*anisotropicFiniteTailSpinSecond D (sj j) (qj j)
    (anisotropicFiniteProcessParameter D (sj j) (qj j) (g,p.2)) e ∂vectorDisorderBrownianMeasure n
  have hZm:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hq:= (Paper.tendsto_parisiGridRound q).comp tendsto_vectorDyadicIndex
  have hH : Tendsto Hj atTop (𝓝 (∫p,Z p*anisotropicProcessSpinSecond D μ q e (g,p.2)
      ∂vectorDisorderBrownianMeasure n)) := by
    apply tendsto_integral_of_dominated_convergence (fun p=>anisotropicSpinSecondBound D e*‖Z p‖)
    · intro j
      have hP : Measurable (fun p : VectorDisorderBrownianSample n=>
          anisotropicFiniteProcessParameter D (sj j) (qj j) (g,p.2)) :=
        (measurable_uncurry_anisotropicFiniteProcessParameter D (sj j)).comp
          ((measurable_const (a:=qj j)).prodMk ((measurable_const (a:=g)).prodMk measurable_snd))
      exact (hZm.mul ((continuous_anisotropicFiniteTailSpinSecond_joint D (sj j) e).measurable.comp
        ((measurable_const (a:=qj j)).prodMk hP))).aestronglyMeasurable
    · exact hZi.norm.const_mul _
    · intro j
      exact .of_forall fun p=>by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (norm_anisotropicFiniteTailSpinSecond_le D (sj j) (qj j) _ e)
          (norm_nonneg (Z p))).trans_eq (mul_comm _ _)
    · exact .of_forall fun p=>(tendsto_const_nhds (x:=Z p)).mul
        (tendsto_anisotropicProcessSpinSecond_moving D μ (g,p.2) e hq)
  have hC:=(tendsto_parisiCDF_grid_at_round μ q).comp tendsto_vectorDyadicIndex
  have hM:=tendsto_anisotropicSpinSquareMoment_grid D μ g e Z hZm hZi q
  have hF:=tendsto_anisotropicGridFutureSpinSquare D μ g q e Z hZm hZi
  have hlim := (hH.add (hC.mul hM)).add hF
  have he (j : ℕ) := anisotropicGrid_spin_second_stieltjes_pairing D μ g q j e Z hZ hZi
  exact tendsto_nhds_unique hlim ((tendsto_const_nhds (x:=∫p,Z p ∂vectorDisorderBrownianMeasure n)).congr
    fun j=>(he j).symm)

end QuantitativeFollowup
