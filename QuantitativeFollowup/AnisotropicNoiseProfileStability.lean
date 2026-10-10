module
public import QuantitativeFollowup.AnisotropicProfileGradientStability
public import QuantitativeFollowup.AnisotropicVarianceNoiseRestart
public import QuantitativePaper.VectorNoisePathDriftStability
public import FRSB.ParisiMeasureTopology

@[expose] public section

/-! Weak-profile stability of genuine anisotropic restarted Picard states,
on a common continuous Wiener path. The estimate is uniform in disorder
and in the complete driving path; endpoint atoms are retained by CDF-L1. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128

theorem anisotropicWhitenedDrift_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (r : ℝ≥0) (p : Couplings n×ℝ) (y : Field n) :
    ‖anisotropicWhitenedDrift D μ g r p y-anisotropicWhitenedDrift D ν g r p y‖≤
      ‖anisotropicNoiseMap D‖*Real.sqrt (n:ℝ)*|Paper.parisiCDF μ r-Paper.parisiCDF ν r|+
        ‖anisotropicNoiseMap D‖*anisotropicProfileGradientError D μ ν := by
  let q : Paper.Overlap:=projIcc (0:ℝ) 1 zero_le_one r
  let P:=anisotropicDisorderInjection n g+anisotropicFieldInjection n (anisotropicNoiseMap D y)
  let x:=anisotropicMeasureTailMagnetization D μ q P
  let z:=anisotropicMeasureTailMagnetization D ν q P
  let a:=Paper.parisiCDF μ r
  let b:=Paper.parisiCDF ν r
  have heq : a • anisotropicNoiseMap D x-b • anisotropicNoiseMap D z=
      (a-b) • anisotropicNoiseMap D x+b • anisotropicNoiseMap D (x-z) := by
    rw [map_sub,sub_smul,smul_sub]
    abel
  change ‖a • anisotropicNoiseMap D x-b • anisotropicNoiseMap D z‖≤_
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_of_nonneg (Paper.parisiCDF_nonneg ν r)]
  have hx : ‖anisotropicNoiseMap D x‖≤‖anisotropicNoiseMap D‖*Real.sqrt (n:ℝ) :=
    ((anisotropicNoiseMap D).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_anisotropicMeasureTailMagnetization_le D μ q P) (norm_nonneg _))
  have hz : ‖anisotropicNoiseMap D (x-z)‖≤‖anisotropicNoiseMap D‖*anisotropicProfileGradientError D μ ν :=
    ((anisotropicNoiseMap D).le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_anisotropicMeasureTailMagnetization_profile_sub_le D μ ν q P) (norm_nonneg _))
  calc
    _≤|a-b| *(‖anisotropicNoiseMap D‖*Real.sqrt (n:ℝ))+
        b*(‖anisotropicNoiseMap D‖*anisotropicProfileGradientError D μ ν) :=
      add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hz (Paper.parisiCDF_nonneg ν r))
    _≤_ := by
      have hh:=mul_le_of_le_one_left (mul_nonneg (norm_nonneg (anisotropicNoiseMap D))
        (anisotropicProfileGradientError_nonneg D μ ν)) (Paper.parisiCDF_le_one ν r)
      dsimp only [a,b]
      nlinarith

def anisotropicNoiseProfileError (D : AnisotropicSpinModel n) (μ ν : Paper.ParisiMeasure) : ℝ :=
  ‖anisotropicNoiseMap D‖*Real.sqrt (n:ℝ)*Paper.parisiCDFDistance μ ν+
    ‖anisotropicNoiseMap D‖*anisotropicProfileGradientError D μ ν

theorem anisotropicNoiseProfileError_nonneg (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) : 0≤anisotropicNoiseProfileError D μ ν :=
  add_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
    (Paper.parisiCDFDistance_nonneg μ ν))
      (mul_nonneg (norm_nonneg _) (anisotropicProfileGradientError_nonneg D μ ν))

theorem norm_anisotropicRestartNoiseStatePath_profile_sub_le (D : AnisotropicSpinModel n)
    (μ ν : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (x y : Field n) (W : VectorWienerPath n) (r : ℝ)
    (hr : r∈Icc (0:ℝ) (1-(q:ℝ))) :
    ‖anisotropicRestartNoiseStatePath D μ q ((g,x),W) r-
      anisotropicRestartNoiseStatePath D ν q ((g,y),W) r‖≤
      (‖x-y‖+anisotropicNoiseProfileError D μ ν)*Real.exp (anisotropicWhitenedDriftLip D) := by
  let H:=vectorRestartHorizon q
  have hH : (H:ℝ)=1-(q:ℝ):=Real.coe_toNNReal _ (sub_nonneg.mpr q.property.2)
  let A:=‖anisotropicNoiseMap D‖*Real.sqrt (n:ℝ)
  let B:=‖anisotropicNoiseMap D‖*anisotropicProfileGradientError D μ ν
  let f:=fun s:ℝ=>|Paper.parisiCDF μ s-Paper.parisiCDF ν s|
  let e:=fun s:ℝ=>A*f ((q:ℝ)+s)+B
  have hfi : IntervalIntegrable f volume (q:ℝ) 1:=Paper.parisiCDF_abs_diff_intervalIntegrable μ ν _ _
  have hshift : IntervalIntegrable (fun s=>f ((q:ℝ)+s)) volume 0 H := by
    simpa only [sub_self,hH] using hfi.comp_add_left (q:ℝ)
  have hei : IntervalIntegrable e volume 0 H:=(hshift.const_mul A).add intervalIntegrable_const
  have he0 : ∀s∈Icc (0:ℝ) H,0≤e s:=by
    intro s hs
    exact add_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (abs_nonneg _))
      (mul_nonneg (norm_nonneg _) (anisotropicProfileGradientError_nonneg D μ ν))
  have hde (s : ℝ≥0) (_hs : s≤H) (z : Field n) :
      ‖(vectorTimeShiftDriftData (anisotropicWhitenedDriftData D μ g) (q:ℝ).toNNReal).drift s 0 z-
        (vectorTimeShiftDriftData (anisotropicWhitenedDriftData D ν g) (q:ℝ).toNNReal).drift s 0 z‖≤e s := by
    simpa only [vectorTimeShiftDriftData,anisotropicWhitenedDriftData,e,A,B,f,
      NNReal.coe_add,Real.coe_toNNReal _ q.property.1] using
      anisotropicWhitenedDrift_profile_sub_le D μ ν g ((q:ℝ).toNNReal+s) 0 z
  have hb:=norm_vectorNoiseStatePath_sub_le_of_L1Drift
    (vectorTimeShiftDriftData (anisotropicWhitenedDriftData D μ g) (q:ℝ).toNNReal)
    (vectorTimeShiftDriftData (anisotropicWhitenedDriftData D ν g) (q:ℝ).toNNReal)
    1 H 0 0 x y W e hei he0 hde r (by simpa only [hH] using hr)
  have hi : (∫s in (0:ℝ)..(H:ℝ),e s)≤anisotropicNoiseProfileError D μ ν := by
    rw [intervalIntegral.integral_add (hshift.const_mul A) intervalIntegrable_const,
      intervalIntegral.integral_const_mul]
    have hs : (∫s in (0:ℝ)..(H:ℝ),f ((q:ℝ)+s))=∫s in (q:ℝ)..1,f s := by
      simpa only [add_zero,hH,add_sub_cancel] using
        intervalIntegral.integral_comp_add_left (a:=(0:ℝ)) (b:=(H:ℝ)) f (q:ℝ)
    rw [hs,intervalIntegral.integral_const,sub_zero,smul_eq_mul,hH]
    have hm : (∫s in (q:ℝ)..1,f s)≤Paper.parisiCDFDistance μ ν := by
      exact intervalIntegral.integral_mono_interval q.property.1 q.property.2 le_rfl
        (.of_forall fun s=>abs_nonneg _) (Paper.parisiCDF_abs_diff_intervalIntegrable μ ν 0 1)
    have hB : 0≤B:=mul_nonneg (norm_nonneg _) (anisotropicProfileGradientError_nonneg D μ ν)
    have hA : 0≤A:=mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    change A*(∫s in (q:ℝ)..1,f s)+(1-(q:ℝ))*B≤A*Paper.parisiCDFDistance μ ν+B
    exact add_le_add (mul_le_mul_of_nonneg_left hm hA)
      (mul_le_of_le_one_left hB (by linarith [q.property.1]))
  change ‖anisotropicRestartNoiseStatePath D μ q ((g,x),W) r-
    anisotropicRestartNoiseStatePath D ν q ((g,y),W) r‖≤_ at hb
  apply hb.trans
  apply mul_le_mul (add_le_add le_rfl hi) ?_ (Real.exp_pos _).le
    (add_nonneg (norm_nonneg _) (anisotropicNoiseProfileError_nonneg D μ ν))
  apply Real.exp_le_exp.mpr
  change (anisotropicWhitenedDriftLip D:ℝ)*r≤anisotropicWhitenedDriftLip D
  exact mul_le_of_le_one_right (anisotropicWhitenedDriftLip D).coe_nonneg
    (by linarith [q.property.1,hr.2])

theorem tendsto_anisotropicNoiseProfileError {L : Type*} {l : Filter L}
    (D : AnisotropicSpinModel n) (μ : L→Paper.ParisiMeasure) (ν : Paper.ParisiMeasure)
    (hμ : Tendsto (fun j=>Paper.parisiCDFDistance (μ j) ν) l (𝓝 0)) :
    Tendsto (fun j=>anisotropicNoiseProfileError D (μ j) ν) l (𝓝 0) := by
  simpa only [anisotropicNoiseProfileError,mul_zero,zero_add] using
    (hμ.const_mul (‖anisotropicNoiseMap D‖*Real.sqrt (n:ℝ))).add
      ((tendsto_anisotropicProfileGradientError D μ ν hμ).const_mul ‖anisotropicNoiseMap D‖)

theorem tendsto_anisotropicRestartNoiseStatePath_profile {L : Type*} {l : Filter L}
    [l.IsCountablyGenerated] (D : AnisotropicSpinModel n)
    {μ : L→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure} (hμ : Tendsto μ l (𝓝 ν))
    (g : AnisotropicDisorder n) (q : Paper.Overlap) {x : L→Field n} {y : Field n}
    (hx : Tendsto x l (𝓝 y)) (W : VectorWienerPath n) (r : ℝ)
    (hr : r∈Icc (0:ℝ) (1-(q:ℝ))) :
    Tendsto (fun j=>anisotropicRestartNoiseStatePath D (μ j) q ((g,x j),W) r) l
      (𝓝 (anisotropicRestartNoiseStatePath D ν q ((g,y),W) r)) := by
  have hd:=FRSB.tendsto_parisiCDFDistance_of_tendsto hμ
  have he:=tendsto_anisotropicNoiseProfileError D μ ν hd
  have hnorm : Tendsto (fun j=>‖x j-y‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hx.sub (tendsto_const_nhds (x:=y))).norm
  have hb : Tendsto (fun j=>(‖x j-y‖+anisotropicNoiseProfileError D (μ j) ν)*
      Real.exp (anisotropicWhitenedDriftLip D)) l (𝓝 0) := by
    simpa only [zero_add,zero_mul] using (hnorm.add he).mul_const (Real.exp (anisotropicWhitenedDriftLip D))
  have hh : Tendsto (fun j=>‖anisotropicRestartNoiseStatePath D (μ j) q ((g,x j),W) r-
      anisotropicRestartNoiseStatePath D ν q ((g,y),W) r‖) l (𝓝 0) :=
    squeeze_zero (fun _=>norm_nonneg _) (fun j=>
      norm_anisotropicRestartNoiseStatePath_profile_sub_le D (μ j) ν g q (x j) y W r hr) hb
  exact tendsto_of_tendsto_of_dist tendsto_const_nhds (by
    simpa only [dist_eq_norm,norm_sub_rev,Function.comp_def] using hh)

end QuantitativeFollowup
