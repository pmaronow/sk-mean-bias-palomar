module
public import QuantitativePaper.VectorRootCovarianceGap
public import QuantitativePaper.VectorInterpolationKernelTransport

@[expose] public section

/-! The genuine derivative of the zero-cell-reduced physical interpolation,
with the outer fractional Gaussian average retained in the full telescope. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal Topology
namespace QuantitativePaper
open FourPapersCommon OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 2000000
variable {n k : ℕ}

def finiteVectorRootInterpolationTime (s : RSBScheme k) (β a : ℝ)
    (ha : 0≤a) (t : ℝ) : ℝ :=
  finiteStateGaussianScheduledTerminalTime (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha)
    (vectorRootInterpolationDirection (n:=n) s β) (vectorRootInterpolationIncreasing s) (k+2) t 0/(n:ℝ)+
    β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q

theorem hasDerivAt_finiteVectorFunctional_root_interpolation (s : RSBScheme k)
    (β a : ℝ) (ha : 0<a) (hq : s.q 1=0) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u=>finiteVectorFunctional n s β u a)
      (finiteVectorRootInterpolationTime (n:=n) s β a ha.le t) t := by
  have hd:=hasDerivAt_finiteStateGaussianScheduledTerminal_time
    (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a) (vectorRootInterpolationMass_nonneg s a ha.le)
    (vectorRootInterpolationDirection (n:=n) s β) (vectorRootInterpolationIncreasing s) (k+2) t ht 0
  let C:=β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q
  have hc:=((hasDerivAt_id t).const_sub 1).mul_const C
  simp only [neg_mul,one_mul] at hc
  have hf:=hd.div_const (n:ℝ) |>.sub hc
  have he : (fun u=>finiteVectorFunctional n s β u a)=ᶠ[𝓝 t]
      fun u=>finiteStateGaussianScheduledTerminalCascade (fun _ : Configuration n=>0)
        (vectorRootInterpolationMass s a) (vectorRootInterpolationDirection (n:=n) s β)
        (vectorRootInterpolationIncreasing s) (k+2) u 0/(n:ℝ)-(1-u)*C := by
    filter_upwards [isOpen_Iio.mem_nhds ht.2] with u hu
    exact finiteVectorFunctional_eq_root_interpolation_schedule s β u a hu.le ha.ne' hq
  convert hf.congr_of_eventuallyEq he using 1 <;> simp only [finiteVectorRootInterpolationTime,C] <;> ring

theorem finiteVectorRootInterpolationTime_eq_signed_responses (s : RSBScheme k)
    (β a : ℝ) (ha : 0≤a) (t : ℝ) (ht : t∈Ioo (0:ℝ) 1) :
    finiteVectorRootInterpolationTime (n:=n) s β a ha t=
      ((1/2:ℝ)*(finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0)
        (vectorRootInterpolationMass s a) (vectorRootInterpolationScaledDirection (n:=n) s β t)
        (k+1) 1 0 (vectorInterpolationDisorderDirection n β)-
        ∑j∈Finset.range (k+1),finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0)
          (vectorRootInterpolationMass s a) (vectorRootInterpolationScaledDirection (n:=n) s β t)
          j (k+2-j) 0 (vectorRootInterpolationDirection (n:=n) s β j)))/(n:ℝ)+
      β^2/2*∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q := by
  let L:=vectorRootInterpolationScaledDirection (n:=n) s β t
  let R:=fun j=>finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0)
    (vectorRootInterpolationMass s a) L j (k+2-j) 0 (vectorRootInterpolationDirection (n:=n) s β j)
  have hs : (∑j∈Finset.range (k+2),(if vectorRootInterpolationIncreasing s j then (1:ℝ) else -1)*R j)=
      finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0)
        (vectorRootInterpolationMass s a) L (k+1) 1 0 (vectorInterpolationDisorderDirection n β)-
        ∑j∈Finset.range (k+1),R j := by
    rw [show k+2=(k+1)+1 by omega,Finset.sum_range_succ]
    have hup : vectorRootInterpolationIncreasing s (k+1)=true:=by
      simp [vectorRootInterpolationIncreasing]
    rw [hup]
    simp only [ite_true,one_mul]
    have he : (∑j∈Finset.range (k+1),(if vectorRootInterpolationIncreasing s j then (1:ℝ) else -1)*R j)=
        -(∑j∈Finset.range (k+1),R j) := by
      rw [←Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hdown : vectorRootInterpolationIncreasing s j=false:=by
        have hlt:=Finset.mem_range.mp hj
        simp [vectorRootInterpolationIncreasing,show ¬k+1≤j by omega]
      rw [hdown]
      simp only [Bool.false_eq_true,ite_false,neg_one_mul]
    rw [he]
    have hlast : R (k+1)=finiteStateCascadeCovarianceResponse (fun _ : Configuration n=>0)
        (vectorRootInterpolationMass s a) L (k+1) 1 0 (vectorInterpolationDisorderDirection n β) := by
      dsimp only [R]
      rw [show k+2-(k+1)=1 by omega,vectorRootInterpolationDirection,if_neg (lt_irrefl _)]
    rw [hlast]
    ring
  rw [finiteVectorRootInterpolationTime,finiteStateGaussianScheduledTerminal_time_eq_responses
    (fun _ : Configuration n=>0) (vectorRootInterpolationMass s a)
    (vectorRootInterpolationMass_nonneg s a ha) _ _ _ t ht]
  change ((1/2:ℝ)*(∑j∈Finset.range (k+2),(if vectorRootInterpolationIncreasing s j then (1:ℝ) else -1)*R j))/(n:ℝ)+
    β^2/2*(∫q in (0:ℝ)..1,q*Paper.parisiCDF (Paper.parisiSchemeMeasure s) q)=_
  rw [hs]

end QuantitativePaper
