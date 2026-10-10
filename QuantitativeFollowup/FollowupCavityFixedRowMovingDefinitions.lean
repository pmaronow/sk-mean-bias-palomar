module
public import QuantitativeFollowup.FollowupCavityFixedRowExpectations
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastVariance
public import QuantitativeFollowup.FollowupCavityNodeBModel

@[expose] public section

/-! Unconditional actual last-variance families. On the positive band they
are exactly the independent-last-variance model, with fixed rest disorder.
These functions provide the concrete moving-heat inputs. -/
noncomputable section
open Set QuantitativePaper FourPapersCommon SpinGlass.Targets
namespace QuantitativeFollowup
variable {n k : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def cavityFixedRowPositiveVarianceModel (n : ℕ) (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (b : ℝ) : AnisotropicSpinModel (n+1) :=
  anisotropicReplaceVariance (followupCavitySpinModel n beta rho hbeta hrho 0
    ⟨le_rfl,zero_le_one⟩) (Fin.last n) b

theorem cavityFixedRowPositiveVarianceModel_eq (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (b : ℝ) (hb : 0<b) :
    cavityFixedRowPositiveVarianceModel n beta rho hbeta hrho b=
      cavityLastVarianceModel n beta rho hbeta hrho b hb := by
  unfold cavityFixedRowPositiveVarianceModel anisotropicReplaceVariance cavityLastVarianceModel
  simp only [hb,and_true]

@[simp] theorem cavityFixedRowPositiveVarianceModel_at_physical (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) :
    cavityFixedRowPositiveVarianceModel n beta rho hbeta hrho (followupCavityD n beta rho)=
      followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩ := by
  let D0:=followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩
  have hv : D0.variance (Fin.last n)=followupCavityD n beta rho := by
    rw [followupCavitySpinModel_variance_last,followupCavityB_zero]
  unfold cavityFixedRowPositiveVarianceModel
  rw [←hv,anisotropicReplaceVariance_self]

def cavityFixedRowMovingNormalizer (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (z : ℝ×Field n) : ℝ :=
  cavityFixedRowNormalizer (cavityFixedRowPositiveVarianceModel n beta rho hbeta hrho z.1) s a z.2

def cavityFixedRowMovingLastMean (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (z : ℝ×Field n) : ℝ :=
  cavityFixedRowLastMean (cavityFixedRowPositiveVarianceModel n beta rho hbeta hrho z.1) s a d z.2

def cavityFixedRowMovingRestMean (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (z : ℝ×Field n) : ℝ :=
  cavityFixedRowRestMean (cavityFixedRowPositiveVarianceModel n beta rho hbeta hrho z.1) s a d z.2

def cavityFixedRowMovingProductMean (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (z : ℝ×Field n) : ℝ :=
  cavityFixedRowProductMean (cavityFixedRowPositiveVarianceModel n beta rho hbeta hrho z.1) s a d z.2

end QuantitativeFollowup
