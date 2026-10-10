module
public import QuantitativeFollowup.FollowupCavityCppNativeJets
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-! The actual native Cpp Taylor remainder is its weighted second-derivative
integral. Both endpoint derivatives are within the physical closed interval. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace QuantitativeFollowup
open FourPapersCommon FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def followupCavityCppTaylorRemainder (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) : ℝ :=
  ∫u in (0:ℝ)..1,(1-u)*withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 2 u

theorem intervalIntegrable_followupCavityCppTaylorRemainder (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap) :
    IntervalIntegrable (fun u=>(1-u)*withinJet
      (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 2 u) volume 0 1 := by
  have hc:ContinuousOn (withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p)
      (Icc 0 1) 2) (Icc (0:ℝ) 1):=
    (contDiffOn_followupCavityCppFunction_withinJet hn β ρ hβ hρ μ a ha hfloor p 2).continuousOn
  exact (continuousOn_const.sub continuousOn_id |>.mul hc).intervalIntegrable_of_Icc (by norm_num)

theorem followupCavityCppFunction_taylor (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap) :
    followupCavityCppFunction n β ρ hβ hρ μ a p 1 =
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0+
        followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p := by
  let f:=followupCavityCppFunction n β ρ hβ hρ μ a p
  let D:=withinJet f (Icc (0:ℝ) 1) 1
  let E:=withinJet f (Icc (0:ℝ) 1) 2
  have hf:ContinuousOn f (Icc (0:ℝ) 1):=
    (contDiffOn_followupCavityCppFunction hn β ρ hβ hρ μ a ha hfloor p).continuousOn
  have hD:ContinuousOn D (Icc (0:ℝ) 1):=
    (contDiffOn_followupCavityCppFunction_withinJet hn β ρ hβ hρ μ a ha hfloor p 1).continuousOn
  have hw:ContinuousOn (fun u=>f u+(1-u)*D u) (Icc (0:ℝ) 1):=
    hf.add ((continuousOn_const.sub continuousOn_id).mul hD)
  have hd (u : ℝ) (hu:u∈Ioo (0:ℝ) 1):
      HasDerivAt (fun u=>f u+(1-u)*D u) ((1-u)*E u) u := by
    have hu':u∈Icc (0:ℝ) 1:=⟨hu.1.le,hu.2.le⟩
    have h0:HasDerivAt f (D u) u:=
      (hasDerivWithinAt_followupCavityCppFunction_withinJet hn β ρ hβ hρ μ a ha hfloor p
        0 u hu').hasDerivAt (Icc_mem_nhds hu.1 hu.2)
    have h1:HasDerivAt D (E u) u:=
      (hasDerivWithinAt_followupCavityCppFunction_withinJet hn β ρ hβ hρ μ a ha hfloor p
        1 u hu').hasDerivAt (Icc_mem_nhds hu.1 hu.2)
    convert! h0.fun_add (((hasDerivAt_const u (1:ℝ)).fun_sub (hasDerivAt_id u)).fun_mul h1) using 1 <;> simp only [id_eq] <;> ring
  have hh:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1)
    hw hd (intervalIntegrable_followupCavityCppTaylorRemainder hn β ρ hβ hρ μ a ha hfloor p)
  have hz:f 0=0:=followupCavityCppFunction_zero β ρ hβ hρ μ a p
  change followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p=
    (f 1+(1-1)*D 1)-(f 0+(1-0)*D 0) at hh
  simp only [sub_self,zero_mul,add_zero,sub_zero,one_mul,hz,zero_add] at hh
  change f 1=D 0+followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p
  linarith

theorem followupCavityCpp_taylor (hn : 0<n)
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap) :
    followupCavityCpp n β ρ hβ hρ μ a 1 ⟨zero_le_one,le_rfl⟩ p =
      withinJet (followupCavityCppFunction n β ρ hβ hρ μ a p) (Icc 0 1) 1 0+
        followupCavityCppTaylorRemainder n β ρ hβ hρ μ a p := by
  rw [←followupCavityCppFunction_eq_actual β ρ hβ hρ μ a p 1 ⟨zero_le_one,le_rfl⟩]
  exact followupCavityCppFunction_taylor hn β ρ hβ hρ μ a ha hfloor p

end QuantitativeFollowup
