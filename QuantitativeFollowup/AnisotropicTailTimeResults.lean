module
public import QuantitativeFollowup.AnisotropicTailTimeLimit
public import QuantitativeFollowup.AnisotropicTailTimeCoordinates
public import FourPapersCommon.AffineLineDerivatives

@[expose] public section

/-! The actual all-profile anisotropic Parisi PDE. The integral equation
retains arbitrary atoms; classical time derivatives are asserted at CDF
continuity points, hence almost everywhere. Field derivatives and the
terminal value refer to the genuine physical potential. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal ContDiff BigOperators
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def anisotropicMeasureTailFieldFirst (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) : ℝ :=
  fderiv ℝ (anisotropicMeasureTailPotential D μ q) P (anisotropicCoordinateDirection n i)

def anisotropicMeasureTailFieldSecond (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q)) P
    (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n i)

theorem hasDerivAt_anisotropicMeasureTail_field_coordinate (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    HasDerivAt (fun z : ℝ => anisotropicMeasureTailPotential D μ q
      (P+z • anisotropicCoordinateDirection n i))
      (anisotropicMeasureTailFieldFirst D μ q P i) 0 := by
  simpa only [zero_smul,add_zero,anisotropicMeasureTailFieldFirst] using
    hasDerivAt_affine_line _ ((anisotropicMeasureTailPotential_hessian_limit D μ q).2.differentiable (by norm_num))
      P (anisotropicCoordinateDirection n i) 0

theorem hasDerivAt_anisotropicMeasureTail_first_coordinate (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) :
    HasDerivAt (fun z : ℝ => anisotropicMeasureTailFieldFirst D μ q
      (P+z • anisotropicCoordinateDirection n i) i)
      (anisotropicMeasureTailFieldSecond D μ q P i) 0 := by
  simpa only [zero_smul,add_zero,anisotropicMeasureTailFieldFirst,anisotropicMeasureTailFieldSecond] using
    hasDerivAt_fderiv_affine_line _ (anisotropicMeasureTailPotential_hessian_limit D μ q).2
      P (anisotropicCoordinateDirection n i) 0

theorem anisotropicMeasureTailTimeSource_coordinates (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℝ) (P : AnisotropicParameter n) :
    anisotropicMeasureTailTimeSource D μ q P = -(1/2:ℝ)*
      ∑i : Fin n,D.variance i *
        (anisotropicMeasureTailFieldSecond D μ (projIcc 0 1 zero_le_one q) P i+
          Paper.parisiCDF μ q*(anisotropicMeasureTailFieldFirst D μ (projIcc 0 1 zero_le_one q) P i)^2) := by
  rw [anisotropicMeasureTailTimeSource,anisotropicTailTimeGenerator_coordinates]
  simp only [anisotropicMeasureTailFieldFirst,anisotropicMeasureTailFieldSecond]
  ring

theorem anisotropicMeasureTail_time_interval_equation (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (a b : Paper.Overlap) (hab : a≤b) :
    anisotropicMeasureTailPotential D μ b P-anisotropicMeasureTailPotential D μ a P =
      ∫t in (a:ℝ)..(b:ℝ), -(1/2:ℝ)*∑i : Fin n,D.variance i *
        (anisotropicMeasureTailFieldSecond D μ (projIcc 0 1 zero_le_one t) P i+
          Paper.parisiCDF μ t*(anisotropicMeasureTailFieldFirst D μ (projIcc 0 1 zero_le_one t) P i)^2) := by
  simpa only [anisotropicMeasureTailTimeSource_coordinates] using
    anisotropicMeasureTail_time_integral D μ P a b hab

theorem hasDerivAt_anisotropicMeasureTail_time_pde (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) (q : ℝ)
    (hq : q∈Ioo (0:ℝ) 1) (hCDF : ContinuousAt (Paper.parisiCDF μ) q) :
    HasDerivAt (fun t => anisotropicMeasureTailPotential D μ (projIcc 0 1 zero_le_one t) P)
      (-(1/2:ℝ)*∑i : Fin n,D.variance i *
        (anisotropicMeasureTailFieldSecond D μ ⟨q,hq.1.le,hq.2.le⟩ P i+
          Paper.parisiCDF μ q*(anisotropicMeasureTailFieldFirst D μ ⟨q,hq.1.le,hq.2.le⟩ P i)^2)) q := by
  simpa only [anisotropicMeasureTailTimeSource_coordinates,
    projIcc_of_mem zero_le_one ⟨hq.1.le,hq.2.le⟩] using
    hasDerivAt_anisotropicMeasureTail_time D μ P q hq hCDF

theorem ae_hasDerivAt_anisotropicMeasureTail_time_pde (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (P : AnisotropicParameter n) :
    ∀ᵐ q ∂volume, q∈Ioo (0:ℝ) 1 →
      HasDerivAt (fun t => anisotropicMeasureTailPotential D μ (projIcc 0 1 zero_le_one t) P)
        (-(1/2:ℝ)*∑i : Fin n,D.variance i *
          (anisotropicMeasureTailFieldSecond D μ (projIcc 0 1 zero_le_one q) P i+
            Paper.parisiCDF μ q*(anisotropicMeasureTailFieldFirst D μ (projIcc 0 1 zero_le_one q) P i)^2)) q := by
  simpa only [anisotropicMeasureTailTimeSource_coordinates] using
    ae_hasDerivAt_anisotropicMeasureTail_time D μ P

theorem anisotropicMeasureTail_terminal_field (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : AnisotropicDisorder n) (x : Field n) :
    anisotropicMeasureTailPotential D μ 1 (anisotropicParameterPoint w x) =
      Real.log (∑σ : Configuration n,Real.exp (anisotropicHamiltonian D w x σ)) := by
  have h1 : (1 : Paper.Overlap)=⟨1,by norm_num⟩ := by ext; norm_num
  rw [h1,anisotropicMeasureTailPotential_one]
  rw [anisotropicGridTerminalPotential,←anisotropicFinitePotential_terminal_softmax D (Paper.parisiGridRSBScheme μ 0)]
  exact anisotropicFinitePotential_terminal D (Paper.parisiGridRSBScheme μ 0) w x

end QuantitativeFollowup
