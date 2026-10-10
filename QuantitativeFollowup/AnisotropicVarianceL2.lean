module
public import QuantitativeFollowup.AnisotropicVarianceBounded

@[expose] public section

/-! The actual anisotropic posterior Hessian-energy variance estimate for
every signed L2 free-measure kernel. Symmetric truncation preserves signs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def anisotropicSignedKernelTruncation (j : ℕ) (x : ℝ) : ℝ := max (-(j:ℝ)) (min x (j:ℝ))

theorem anisotropicSignedKernelTruncation_bound (j : ℕ) (x : ℝ) :
    |anisotropicSignedKernelTruncation j x|≤(j:ℝ) := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α:=ℝ) j]) (min_le_right _ _)⟩

theorem anisotropicSignedKernelTruncation_abs_le (j : ℕ) (x : ℝ) :
    |anisotropicSignedKernelTruncation j x|≤|x| := by
  apply abs_le.mpr
  constructor
  · exact (le_min (neg_abs_le x) (by linarith [abs_nonneg x,Nat.cast_nonneg (α:=ℝ) j])).trans (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg x,Nat.cast_nonneg (α:=ℝ) j])
      ((min_le_left _ _).trans (le_abs_self x))

theorem tendsto_anisotropicSignedKernelTruncation (x : ℝ) :
    Tendsto (fun j=>anisotropicSignedKernelTruncation j x) atTop (𝓝 x) := by
  have he : ∀ᶠj : ℕ in atTop,|x|≤(j:ℝ):=tendsto_natCast_atTop_atTop.eventually_ge_atTop |x|
  apply tendsto_const_nhds.congr'
  exact he.mono fun j hj=>by
    unfold anisotropicSignedKernelTruncation
    dsimp only
    rw [min_eq_left (abs_le.mp hj).2,max_eq_right (abs_le.mp hj).1]

theorem anisotropic_weighted_selfOverlap_variance_L2 (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a)≤
      ∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a := by
  let κj : ℕ→Paper.Overlap→ℝ:=fun j q=>anisotropicSignedKernelTruncation j (κ q)
  have hm (j : ℕ) : Measurable (κj j):=measurable_const.max (hκ.min measurable_const)
  have hb (j : ℕ) (q : Paper.Overlap) : |κj j q|≤|κ q|:=anisotropicSignedKernelTruncation_abs_le j (κ q)
  have hiA : Integrable (fun q=>|κ q|) (parisiFreeMeasure μ a):=(hL.integrable one_le_two).abs
  have hiA2 : Integrable (fun q=>|κ q|^2) (parisiFreeMeasure μ a):=by
    simpa only [sq_abs] using hL.integrable_sq
  have hlim : ∀ᵐq ∂parisiFreeMeasure μ a,Tendsto (fun j=>κj j q) atTop (𝓝 (κ q)):=
    .of_forall fun q=>tendsto_anisotropicSignedKernelTruncation (κ q)
  have hV:=tendsto_variance_anisotropicWeightedSelfOverlap_kernel D μ a κj κ (fun q=>|κ q|)
    hm hκ hiA (fun q=>abs_nonneg _) hb (fun _=>le_rfl) hlim J
  have hE:=tendsto_integral_anisotropicWeightedProcessHessianEnergy_kernel D μ a κj κ (fun q=>|κ q|)
    hm hiA2 hb hlim J
  apply le_of_tendsto_of_tendsto hV hE
  exact .of_forall fun j=>anisotropic_weighted_selfOverlap_variance_bounded D μ a ha hμ
    (κj j) (hm j) J hJ (j:ℝ) (Nat.cast_nonneg j)
    (fun q=>anisotropicSignedKernelTruncation_bound j (κ q))

end QuantitativeFollowup
