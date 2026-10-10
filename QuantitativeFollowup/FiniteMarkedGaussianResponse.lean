module
public import QuantitativeFollowup.GaussianCenteredParameterResponse

@[expose] public section

/-! Finite marks are summed before normalization. Component centered
Gaussian responses are genuine derivatives from the preceding module;
constant total normalization then yields the derivative of the joint mean. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace QuantitativeFollowup

/-- Calculus of a genuinely normalized finite marked density. Its component
responses can be instantiated by Gaussian integration by parts; separate
spin-slice normalization is unnecessary. -/
theorem hasDerivAt_finiteMarkedMean_of_centered
    {ι : Type*} [Fintype ι] (N H : ι→ℝ→ℝ) (D : ι→ℝ)
    (a c Z : ℝ) (hZ : Z≠0)
    (hd : ∀i,HasDerivAt (fun u=>N i u-c*H i u) (D i) a)
    (hnorm : ∀ᶠu in 𝓝 a,(∑i,H i u)=Z) :
    HasDerivAt (fun u=>(∑i,N i u)/(∑i,H i u)) ((∑i,D i)/Z) a := by
  have hh := (HasDerivAt.fun_sum (u:=Finset.univ) fun i _=>hd i).div_const Z
  have hf := hh.add_const c
  apply hf.congr_of_eventuallyEq
  filter_upwards [hnorm] with u hu
  change (∑i,N i u)/(∑i,H i u)=(∑ i, (N i u - c*H i u))/Z+c
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,hu]
  field_simp [hZ]
  ring

end QuantitativeFollowup
