module
public import QuantitativeFollowup.AnisotropicNoiseProfileStability
public import QuantitativePaper.VectorNoisePathTrajectoryStability
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-! Moving restart levels of the actual anisotropic diffusion. The CDF
may jump: its shifted discontinuities form a genuine Lebesgue-null set,
and bounded drift permits dominated time integration. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 250000
set_option synthInstance.maxHeartbeats 60000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

def anisotropicExtendedRestartNoiseStatePath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (W : VectorWienerPath n) : ℝ→Field n :=
  vectorNoiseStatePath (vectorTimeShiftDriftData (anisotropicWhitenedDriftData D μ g)
    (q:ℝ).toNNReal) 1 1 ((0,x),W)

theorem anisotropicRestartNoiseStatePath_eq_extended (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x : Field n) (W : VectorWienerPath n) (r : ℝ) (hr : r∈Icc (0:ℝ) (1-(q:ℝ))) :
    anisotropicRestartNoiseStatePath D μ q ((g,x),W) r=
      anisotropicExtendedRestartNoiseStatePath D μ g q x W r := by
  have hH : ((vectorRestartHorizon q:ℝ≥0):ℝ)=1-(q:ℝ) :=
    Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)
  have hH1 : vectorRestartHorizon q≤1 := by
    rw [←NNReal.coe_le_coe,hH]
    simp only [NNReal.coe_one]
    linarith [q.property.1]
  exact vectorNoiseStatePath_horizon_eq _ 1 (vectorRestartHorizon q) 1 hH1 _ r
    (by simpa only [hH] using hr)

theorem ae_continuousAt_parisiCDF_shift (μ : Paper.ParisiMeasure) (q : ℝ) :
    ∀ᵐs∂volume,ContinuousAt (Paper.parisiCDF μ) (q+s) := by
  have hc:=(Paper.parisiCDF_monotone μ).countable_not_continuousAt
  have hp:=hc.preimage (show Function.Injective (fun s : ℝ=>q+s) from add_right_injective q)
  filter_upwards [hp.ae_notMem volume] with s hs
  exact not_not.mp hs

theorem tendsto_anisotropicWhitenedDrift_shift {L : Type*} {l : Filter L}
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    {q : L→Paper.Overlap} {v : Paper.Overlap} (hq : Tendsto q l (𝓝 v))
    (s : ℝ≥0) (y : Field n) (hs : ContinuousAt (Paper.parisiCDF μ) ((v:ℝ)+s)) :
    Tendsto (fun j=>anisotropicWhitenedDrift D μ g ((q j:ℝ).toNNReal+s) (0 : Couplings n×ℝ) y) l
      (𝓝 (anisotropicWhitenedDrift D μ g ((v:ℝ).toNNReal+s) (0 : Couplings n×ℝ) y)) := by
  have ht : Tendsto (fun j=>(q j:ℝ)+(s:ℝ)) l (𝓝 ((v:ℝ)+(s:ℝ))) :=
    (continuous_subtype_val.tendsto _ |>.comp hq).add_const (s:ℝ)
  have hC := hs.tendsto.comp ht
  have hP : Tendsto (fun j : L=>projIcc (0:ℝ) 1 zero_le_one ((q j:ℝ)+(s:ℝ))) l
      (𝓝 (projIcc (0:ℝ) 1 zero_le_one ((v:ℝ)+(s:ℝ)))) :=
    (continuous_projIcc (h:=zero_le_one)).tendsto _ |>.comp ht
  have hM := (continuous_anisotropicMeasureTailMagnetization_joint D μ).tendsto _ |>.comp
    (hP.prodMk_nhds (tendsto_const_nhds (x:=anisotropicDisorderInjection n g+
      anisotropicFieldInjection n (anisotropicNoiseMap D y))))
  have hN : Tendsto (fun j : L => anisotropicNoiseMap D
      (anisotropicMeasureTailMagnetization D μ (projIcc (0:ℝ) 1 zero_le_one ((q j:ℝ)+s))
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D y)))) l
      (𝓝 (anisotropicNoiseMap D (anisotropicMeasureTailMagnetization D μ
        (projIcc (0:ℝ) 1 zero_le_one ((v:ℝ)+s))
        (anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D y))))) :=
    (anisotropicNoiseMap D).continuous.tendsto _ |>.comp hM
  haveI : ContinuousSMul ℝ (Field n) := IsBoundedSMul.continuousSMul
  have hh := hC.smul hN
  simpa only [anisotropicWhitenedDrift,NNReal.coe_add,
    Real.coe_toNNReal _ (q _).property.1,Real.coe_toNNReal _ v.property.1, Function.comp_def] using hh

theorem tendsto_anisotropicRestartLevelForcing {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) {q : L→Paper.Overlap} {v : Paper.Overlap}
    (hq : Tendsto q l (𝓝 v)) (Y : ℝ→Field n) (hY : Continuous Y) :
    Tendsto (fun j=>∫s in (0:ℝ)..1,
      ‖anisotropicWhitenedDrift D μ g ((q j:ℝ).toNNReal+s.toNNReal) 0 (Y s)-
        anisotropicWhitenedDrift D μ g ((v:ℝ).toNNReal+s.toNNReal) 0 (Y s)‖) l (𝓝 0) := by
  let A:=fun (j : L) (s : ℝ)=>‖anisotropicWhitenedDrift D μ g ((q j:ℝ).toNNReal+s.toNNReal) 0 (Y s)-
        anisotropicWhitenedDrift D μ g ((v:ℝ).toNNReal+s.toNNReal) 0 (Y s)‖
  have hm (w : Paper.Overlap) : Measurable (fun s : ℝ=>
      anisotropicWhitenedDrift D μ g ((w:ℝ).toNNReal+s.toNNReal) 0 (Y s)) :=
    by
      have harg : Measurable (fun s : ℝ=>(((w:ℝ).toNNReal+s.toNNReal),
          ((0 : Couplings n×ℝ),Y s))) := by fun_prop
      have hh := (measurable_anisotropicWhitenedDrift D μ g).comp harg
      simpa only [Function.comp_def] using hh
  have hAm (j : L) : AEStronglyMeasurable (A j) (volume.restrict (Ioc (0:ℝ) 1)) :=
    ((hm (q j)).sub (hm v)).norm.aestronglyMeasurable
  have hb (j : L) (s : ℝ) : ‖A j s‖≤2*(anisotropicWhitenedDriftBound D:ℝ) := by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by
      linarith [norm_anisotropicWhitenedDrift_le D μ g ((q j:ℝ).toNNReal+s.toNNReal) 0 (Y s),
        norm_anisotropicWhitenedDrift_le D μ g ((v:ℝ).toNNReal+s.toNNReal) 0 (Y s)])
  have hp : ∀ᵐs∂volume.restrict (Ioc (0:ℝ) 1),Tendsto (fun j=>A j s) l (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae (ae_continuousAt_parisiCDF_shift μ (v:ℝ)),
      ae_restrict_mem measurableSet_Ioc] with s hs hsm
    have ht:=tendsto_anisotropicWhitenedDrift_shift D μ g hq s.toNNReal (Y s)
      (by simpa only [Real.coe_toNNReal _ hsm.1.le] using hs)
    simpa only [sub_self,norm_zero,A] using (ht.sub (tendsto_const_nhds (x:=anisotropicWhitenedDrift D μ g
      ((v:ℝ).toNNReal+s.toNNReal) 0 (Y s)))).norm
  have ht:=tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ=>2*(anisotropicWhitenedDriftBound D:ℝ)) (.of_forall hAm)
    (.of_forall fun j=>.of_forall (hb j)) (integrable_const _) hp
  simpa only [intervalIntegral.integral_of_le zero_le_one,integral_zero] using ht

theorem tendsto_anisotropicExtendedRestartNoiseStatePath {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) {q : L→Paper.Overlap} {v : Paper.Overlap}
    (hq : Tendsto q l (𝓝 v)) {x : L→Field n} {y : Field n} (hx : Tendsto x l (𝓝 y))
    (W : VectorWienerPath n) {r : L→ℝ} {t : ℝ} (hr : Tendsto r l (𝓝 t))
    (hr01 : ∀j,r j∈Icc (0:ℝ) 1) :
    Tendsto (fun j=>anisotropicExtendedRestartNoiseStatePath D μ g (q j) (x j) W (r j)) l
      (𝓝 (anisotropicExtendedRestartNoiseStatePath D μ g v y W t)) := by
  let d:=fun w : Paper.Overlap=>vectorTimeShiftDriftData (anisotropicWhitenedDriftData D μ g) (w:ℝ).toNNReal
  let Y:=vectorNoiseStatePath (d v) 1 1 ((0,y),W)
  have hY : Continuous Y:=continuous_vectorNoiseStatePath _ _ _ _
  let A:=fun (j : L) (s : ℝ)=>‖(d (q j)).drift s.toNNReal 0 (Y s)-(d v).drift s.toNNReal 0 (Y s)‖
  have hAi (j : L) : IntervalIntegrable (A j) volume 0 1 := by
    have hm (w : Paper.Overlap) : Measurable (fun s : ℝ=>(d w).drift s.toNNReal 0 (Y s)) :=
      by
        have harg : Measurable (fun s : ℝ=>(s.toNNReal,((0 : Couplings n×ℝ),Y s))) := by fun_prop
        have hh := (d w).measurable.comp harg
        simpa only [Function.comp_def] using hh
    apply (intervalIntegrable_const (c:=2*(anisotropicWhitenedDriftBound D:ℝ))).mono_fun'
      (((hm (q j)).sub (hm v)).norm.aestronglyMeasurable)
    exact .of_forall fun s=>by
      change ‖‖(d (q j)).drift s.toNNReal 0 (Y s)-(d v).drift s.toNNReal 0 (Y s)‖‖≤_
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      have h1 : ‖(d (q j)).drift s.toNNReal 0 (Y s)‖≤(anisotropicWhitenedDriftBound D:ℝ) :=
        (d (q j)).norm_le s.toNNReal 0 (Y s)
      have h2 : ‖(d v).drift s.toNNReal 0 (Y s)‖≤(anisotropicWhitenedDriftBound D:ℝ) :=
        (d v).norm_le s.toNNReal 0 (Y s)
      exact (norm_sub_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
  have hA : Tendsto (fun j=>∫s in (0:ℝ)..1,A j s) l (𝓝 0) :=
    tendsto_anisotropicRestartLevelForcing D μ g hq Y hY
  have hx0 : Tendsto (fun j=>‖x j-y‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hx.sub (tendsto_const_nhds (x:=y))).norm
  have hbound : Tendsto (fun j=>(‖x j-y‖+∫s in (0:ℝ)..1,A j s)*
      Real.exp (anisotropicWhitenedDriftLip D)) l (𝓝 0) := by
    simpa only [zero_add,zero_mul] using (hx0.add hA).mul_const (Real.exp (anisotropicWhitenedDriftLip D))
  have hi (j : L) : ‖anisotropicExtendedRestartNoiseStatePath D μ g (q j) (x j) W (r j)-Y (r j)‖≤
      (‖x j-y‖+∫s in (0:ℝ)..1,A j s)*Real.exp (anisotropicWhitenedDriftLip D) := by
    have hh:=norm_vectorNoiseStatePath_sub_le_of_trajectory_forcing (d (q j)) (d v) 1 1 0 0
      (x j) y W (A j) (hAi j) (fun s _=>norm_nonneg _) (fun u _=>by
        simp only [A,Real.toNNReal_coe,Y]
        exact le_rfl) (r j) (hr01 j)
    apply hh.trans
    apply mul_le_mul le_rfl ?_ (Real.exp_pos _).le
      (add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg zero_le_one (fun s _=>norm_nonneg _)))
    apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right (anisotropicWhitenedDriftLip D).coe_nonneg (hr01 j).2
  have hd:=squeeze_zero (fun j=>norm_nonneg _) hi hbound
  exact tendsto_of_tendsto_of_dist (hY.tendsto t |>.comp hr) (by
    simpa only [dist_eq_norm,norm_sub_rev,Function.comp_def] using hd)

theorem tendsto_anisotropicRestartNoiseStatePath_level {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) {q : L→Paper.Overlap} {v : Paper.Overlap}
    (hq : Tendsto q l (𝓝 v)) {x : L→Field n} {y : Field n} (hx : Tendsto x l (𝓝 y))
    (W : VectorWienerPath n) {r : L→ℝ} {t : ℝ} (hr : Tendsto r l (𝓝 t))
    (hri : ∀j,r j∈Icc (0:ℝ) (1-(q j:ℝ))) (hti : t∈Icc (0:ℝ) (1-(v:ℝ))) :
    Tendsto (fun j=>anisotropicRestartNoiseStatePath D μ (q j) ((g,x j),W) (r j)) l
      (𝓝 (anisotropicRestartNoiseStatePath D μ v ((g,y),W) t)) := by
  have he : (fun j=>anisotropicRestartNoiseStatePath D μ (q j) ((g,x j),W) (r j))=
      (fun j=>anisotropicExtendedRestartNoiseStatePath D μ g (q j) (x j) W (r j)) :=
    funext fun j=>anisotropicRestartNoiseStatePath_eq_extended D μ g (q j) (x j) W (r j) (hri j)
  rw [he,anisotropicRestartNoiseStatePath_eq_extended D μ g v y W t hti]
  exact tendsto_anisotropicExtendedRestartNoiseStatePath D μ g hq hx W hr
    (fun j=>⟨(hri j).1,(hri j).2.trans (by linarith [(q j).property.1])⟩)

theorem tendsto_anisotropicRestartNoiseStatePath_profile_level {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν))
    (g : AnisotropicDisorder n) {q : L→Paper.Overlap} {v : Paper.Overlap}
    (hq : Tendsto q l (𝓝 v)) {x : L→Field n} {y : Field n} (hx : Tendsto x l (𝓝 y))
    (W : VectorWienerPath n) {r : L→ℝ} {t : ℝ} (hr : Tendsto r l (𝓝 t))
    (hri : ∀j,r j∈Icc (0:ℝ) (1-(q j:ℝ))) (hti : t∈Icc (0:ℝ) (1-(v:ℝ))) :
    Tendsto (fun j=>anisotropicRestartNoiseStatePath D (μ j) (q j) ((g,x j),W) (r j)) l
      (𝓝 (anisotropicRestartNoiseStatePath D ν v ((g,y),W) t)) := by
  have hb : Tendsto (fun j=>anisotropicNoiseProfileError D (μ j) ν*
      Real.exp (anisotropicWhitenedDriftLip D)) l (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_anisotropicNoiseProfileError D μ ν
      (FRSB.tendsto_parisiCDFDistance_of_tendsto hμ)).mul_const (Real.exp (anisotropicWhitenedDriftLip D))
  have hd : Tendsto (fun j=>‖anisotropicRestartNoiseStatePath D (μ j) (q j) ((g,x j),W) (r j)-
      anisotropicRestartNoiseStatePath D ν (q j) ((g,x j),W) (r j)‖) l (𝓝 0) := by
    apply squeeze_zero (fun j=>norm_nonneg _) (fun j=>?_) hb
    simpa only [sub_self,norm_zero,zero_add] using
      norm_anisotropicRestartNoiseStatePath_profile_sub_le D (μ j) ν g (q j) (x j) (x j) W (r j) (hri j)
  exact tendsto_of_tendsto_of_dist
    (tendsto_anisotropicRestartNoiseStatePath_level D ν g hq hx W hr hri hti) (by
      simpa only [dist_eq_norm,norm_sub_rev,Function.comp_def] using hd)

end QuantitativeFollowup
