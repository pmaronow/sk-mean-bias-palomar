module
public import FRSB.Comparison

@[expose] public section

/-! Compact parabolic comparison needs the supersolution inequality only
where the tested function is negative. Time jets are genuinely one-sided. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon

theorem compact_negative_supersolution_nonneg (T l r : ℝ) (hT : 0≤T) (hlr : l<r)
    (v vt b κ : ℝ×ℝ→ℝ) (hv : ContinuousOn v (Icc 0 T×ˢIcc l r))
    (ht : ∀t∈Ioc (0 : ℝ) T,∀x∈Ioo l r,
      HasDerivWithinAt (fun s=>v (s,x)) (vt (t,x)) (Icc 0 T) t)
    (hx : ∀t∈Ioc (0 : ℝ) T,∀x∈Ioo l r,DifferentiableAt ℝ (fun y=>v (t,y)) x)
    (hκ : ∀t∈Ioc (0 : ℝ) T,∀x∈Ioo l r,κ (t,x)<0)
    (hPDE : ∀t∈Ioc (0 : ℝ) T,∀x∈Ioo l r,v (t,x)<0→
      0≤vt (t,x)-(1/2 : ℝ)*deriv (deriv (fun y=>v (t,y))) x-
        b (t,x)*deriv (fun y=>v (t,y)) x-κ (t,x)*v (t,x))
    (hinitial : ∀x∈Icc l r,0≤v (0,x))
    (hleft : ∀t∈Icc (0 : ℝ) T,0≤v (t,l))
    (hright : ∀t∈Icc (0 : ℝ) T,0≤v (t,r)) :
    ∀p∈Icc 0 T×ˢIcc l r,0≤v p := by
  intro p hp
  by_contra hn
  have hpneg : v p<0:=lt_of_not_ge hn
  obtain ⟨z,hz,hmin⟩:=(isCompact_Icc.prod isCompact_Icc).exists_isMinOn ⟨p,hp⟩ hv
  have hzneg : v z<0:=(hmin hp).trans_lt hpneg
  have hzt : 0<z.1:=by
    apply lt_of_le_of_ne hz.1.1
    intro he
    have hh : 0≤v z:=by
      change 0≤v (z.1,z.2)
      rw [←he]
      exact hinitial z.2 hz.2
    exact (not_le_of_gt hzneg) hh
  have hzL : l<z.2:=by
    apply lt_of_le_of_ne hz.2.1
    intro he
    have hh:=hleft z.1 hz.1
    rw [he] at hh
    exact (not_le_of_gt hzneg) hh
  have hzR : z.2<r:=by
    apply lt_of_le_of_ne hz.2.2
    intro he
    have hh:=hright z.1 hz.1
    rw [←he] at hh
    exact (not_le_of_gt hzneg) hh
  have ht0 : z.1∈Ioc (0 : ℝ) T:=⟨hzt,hz.1.2⟩
  have hx0 : z.2∈Ioo l r:=⟨hzL,hzR⟩
  have htm : IsMinOn (fun s=>v (s,z.2)) (Icc 0 z.1) z.1:=by
    intro s hs
    exact hmin ⟨⟨hs.1,hs.2.trans hz.1.2⟩,hz.2⟩
  have htd : vt z≤0:=FRSB.minOn_Icc_timeDeriv_nonpos hzt hz.1.2 htm (ht z.1 ht0 z.2 hx0)
  have hxm : IsLocalMin (fun y=>v (z.1,y)) z.2:=by
    filter_upwards [Ioo_mem_nhds hzL hzR] with y hy
    exact hmin ⟨hz.1,⟨hy.1.le,hy.2.le⟩⟩
  have hxd : deriv (fun y=>v (z.1,y)) z.2=0:=hxm.deriv_eq_zero
  have hxxd:=FRSB.localMin_second_deriv_nonneg hxm (hx z.1 ht0 z.2 hx0).continuousAt
  have hreaction : 0<κ z*v z:=mul_pos_of_neg_of_neg (hκ z.1 ht0 z.2 hx0) hzneg
  have hh:=hPDE z.1 ht0 z.2 hx0 hzneg
  rw [hxd,mul_zero] at hh
  linarith

end FourPapersCommon
