module
public import QuantitativePaper.VectorFixedStateHessianClosedCells
public import QuantitativePaper.VectorGradientSquareGrid
public import QuantitativePaper.VectorDyadicHessianReactionSource
public import QuantitativePaper.VectorFixedStateCellEnergyIdentification
public import QuantitativePaper.VectorDyadicFixedEnergyLimit
public import Paper.ParisiGradientMesh
public import FRSB.GammaIdentity

@[expose] public section

/-! Genuine normalized finite-grid Hessian expectations on the
fixed μ diffusion, with the actual fractional disorder law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets QuantitativeFollowup Paper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorDyadicFixedHessianMean (μ : ParisiMeasure) (β t outer : ℝ) (ht : t ≤ 1)
    (j : ℕ) (r : ℝ) : ℝ :=
  (∑l : Fin n,∫sample,(vectorFiniteTailHessian (parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
    (projIcc 0 1 zero_le_one r) sample.1 (vectorMeasureState μ β t ht r.toNNReal sample) (EuclideanSpace.single l 1)) l
      ∂vectorMeasureDisorderTilt μ β t outer)/(n:ℝ)

theorem vectorDyadicFixedHessianMean_eq_cell (μ : ParisiMeasure) (β t outer : ℝ)
    (ht : t ≤ 1) (j i : ℕ) (hi : i ≤ vectorDyadicIndex j+1) {r : ℝ}
    (hr : r∈Icc ((parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))) :
    vectorDyadicFixedHessianMean (n:=n) μ β t outer ht j r=
      (∑l : Fin n,vectorFixedStateCellHessianMean
        (parisiGridRSBScheme μ (vectorDyadicIndex j)) μ β t outer ht i l r)/(n:ℝ) := by
  let s:=parisiGridRSBScheme μ (vectorDyadicIndex j)
  have hr01:r∈Icc (0:ℝ) 1:=⟨(s.q_nonneg (by omega)).trans hr.1,hr.2.trans (s.q_le_one (by omega))⟩
  unfold vectorDyadicFixedHessianMean
  rw [projIcc_of_mem zero_le_one hr01]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  unfold vectorFixedStateCellHessianMean
  apply integral_congr_ae
  exact .of_forall fun sample=>by
    unfold vectorFiniteTailHessian vectorFiniteCellHessianDiagonal
    dsimp only
    rw [Real.coe_toNNReal _ hr01.1]
    rw [vectorTailRecursion_eq_finiteCell s β t r sample.1 i (by omega) hr]

theorem vectorDyadicFixedHessianSource_eq_cell (μ : ParisiMeasure) (β t outer : ℝ)
    (ht : t ≤ 1) (j i : ℕ) (hi0 : 1 ≤ i) (hi : i ≤ vectorDyadicIndex j+1) {r : ℝ}
    (hr : r∈Ico ((parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))) :
    vectorDyadicFixedHessianSource (n:=n) μ β t outer ht j r=
      (∑l : Fin n,(-(((1-t)*β^2)*(parisiGridRSBScheme μ (vectorDyadicIndex j)).m i))*vectorFixedStateCellEnergyMean
        (parisiGridRSBScheme μ (vectorDyadicIndex j)) μ β t outer ht i l r)/(n:ℝ) := by
  let s:=parisiGridRSBScheme μ (vectorDyadicIndex j)
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t outer
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t outer ht
  have hr01:r∈Icc (0:ℝ) 1:=⟨(s.q_nonneg (by omega)).trans hr.1,hr.2.le.trans (s.q_le_one (by omega))⟩
  have hie (l : Fin n) : Integrable (fun sample=>vectorFixedStateCellGradientEnergy s μ β t ht i r.toNNReal sample l) P :=
    (integrable_const ((n:ℝ)*(vectorFiniteCellGradientDerivativeBound s β t i l:ℝ)^2)).mono'
      (measurable_vectorFixedStateCellGradientEnergy s μ β t ht i l _).aestronglyMeasurable
      (.of_forall fun sample=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (vectorFixedStateCellGradientEnergy_nonneg_le s μ β t ht i l _ sample).1]
        exact (vectorFixedStateCellGradientEnergy_nonneg_le s μ β t ht i l _ sample).2)
  have he : vectorDyadicFixedEnergyExpectation (n:=n) μ β t outer ht ⟨r,hr01⟩ j=
      ∑l : Fin n,vectorFixedStateCellEnergyMean s μ β t outer ht i l r := by
    unfold vectorDyadicFixedEnergyExpectation vectorDyadicFixedHessianEnergy vectorFixedStateCellEnergyMean
    rw [←integral_finsetSum _ (fun l _=>hie l)]
    apply integral_congr_ae
    exact .of_forall fun sample=>(sum_vectorFixedStateCellGradientEnergy_eq_tailHessian s μ β t ht i (by omega)
      ⟨r,hr01⟩ ⟨hr.1,hr.2.le⟩ sample).symm
  unfold vectorDyadicFixedHessianSource
  rw [projIcc_of_mem zero_le_one hr01,parisiCDF_grid_eq_scheme_mass μ (vectorDyadicIndex j) i hi0 hi hr,he,Finset.mul_sum]
  rw [Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem vectorDyadicFixedHessian_cell_bound (hn : 0 < n) (μ : ParisiMeasure)
    (β t outer : ℝ) (hβ : β≠0) (ht : t < 1) (j i : ℕ)
    (hi0 : 1 ≤ i) (hi : i ≤ vectorDyadicIndex j+1)
    (hq : (parisiGridRSBScheme μ (vectorDyadicIndex j)).q i < 
      (parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))
    {a b : ℝ} (ha : (parisiGridRSBScheme μ (vectorDyadicIndex j)).q i ≤ a)
    (hab : a ≤ b) (hb : b ≤  (parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))
    (D : ℝ) (hD : 0 ≤ D)
    (hgrad : ∀q p x,‖vectorMeasureGradient (n:=n) μ β t q p x-
      vectorDyadicTailGradient μ β t q j p x‖ ≤ D) :
    ‖vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j b-
      vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j a-
      ∫r in a..b,vectorDyadicFixedHessianSource (n:=n) μ β t outer ht.le j r‖ ≤ 
      ∫r in a..b,vectorCellHessianError (n:=n) μ β t
        ((parisiGridRSBScheme μ (vectorDyadicIndex j)).m i) D r := by
  let s:=parisiGridRSBScheme μ (vectorDyadicIndex j)
  let F:=fun l : Fin n=>vectorFixedStateCellHessianMean s μ β t outer ht.le i l
  let E:=fun l : Fin n=>fun r=>(-(((1-t)*β^2)*(s.m i)))*vectorFixedStateCellEnergyMean s μ β t outer ht.le i l r
  have hsource : (∫r in a..b,vectorDyadicFixedHessianSource (n:=n) μ β t outer ht.le j r)=
      (∑l : Fin n,∫r in a..b,E l r)/(n:ℝ) := by
    have he : (∫r in a..b,vectorDyadicFixedHessianSource (n:=n) μ β t outer ht.le j r)=
        ∫r in a..b,(∑l : Fin n,E l r)/(n:ℝ) := by
      apply intervalIntegral.integral_congr_uIoo
      rw [uIoo_of_le hab]
      intro r hr
      exact vectorDyadicFixedHessianSource_eq_cell μ β t outer ht.le j i hi0 hi
        ⟨ha.trans hr.1.le,hr.2.trans_le hb⟩
    rw [he,intervalIntegral.integral_div,intervalIntegral.integral_finsetSum]
    intro l _
    exact ((continuous_vectorFixedStateCellEnergyMean s μ β t outer ht.le i l).intervalIntegrable a b).const_mul _
  rw [vectorDyadicFixedHessianMean_eq_cell μ β t outer ht.le j i hi ⟨ha.trans hab,hb⟩,
    vectorDyadicFixedHessianMean_eq_cell μ β t outer ht.le j i hi ⟨ha,hab.trans hb⟩,hsource]
  have hnpos:0 < (n:ℝ):=Nat.cast_pos.mpr hn
  have hsum : (∑l : Fin n,F l b)/(n:ℝ)-(∑l : Fin n,F l a)/(n:ℝ)-
      (∑l : Fin n,∫r in a..b,E l r)/(n:ℝ)=
      (∑l : Fin n,(F l b-F l a-∫r in a..b,E l r))/(n:ℝ) := by
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib]
    ring
  rw [hsum,norm_div,Real.norm_of_nonneg hnpos.le]
  apply (div_le_iff₀ hnpos).mpr
  calc
    _ ≤ ∑l : Fin n,‖F l b-F l a-∫r in a..b,E l r‖:=norm_sum_le _ _
    _ ≤ ∑_l : Fin n,∫r in a..b,vectorCellHessianError (n:=n) μ β t (s.m i) D r := by
      apply Finset.sum_le_sum
      intro l _
      exact vectorFixedState_hessian_cell_bound s μ β t outer hβ ht i (by omega) l hq ha hab hb D hD hgrad
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

def vectorDyadicFixedHessianError (μ : ParisiMeasure) (β t : ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  ((1-t)*β^2)*vectorSpatialJetBound n 3*(Real.sqrt n*|parisiCDF μ r-
    parisiCDF (parisiGridMeasure μ (vectorDyadicIndex j)) r|+vectorDyadicFixedGradientError (n:=n) β t j)

theorem vectorDyadicFixedHessianError_intervalIntegrable (μ : ParisiMeasure)
    (β t : ℝ) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (vectorDyadicFixedHessianError (n:=n) μ β t j) volume a b :=
  ((((((parisiCDF_monotone μ).intervalIntegrable).sub
    ((parisiCDF_monotone (parisiGridMeasure μ (vectorDyadicIndex j))).intervalIntegrable)).norm.const_mul
      (Real.sqrt n)).add intervalIntegrable_const).const_mul (((1-t)*β^2)*vectorSpatialJetBound n 3))

theorem vectorDyadicFixedHessian_tail_bound (hn : 0 < n) (μ : ParisiMeasure)
    (β t outer : ℝ) (hβ : β≠0) (ht : t < 1) (j : ℕ) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    ‖vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j 1-
      vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j r-
      ∫x in r..1,vectorDyadicFixedHessianSource (n:=n) μ β t outer ht.le j x‖ ≤ 
      ((1-t)*β^2)*vectorSpatialJetBound n 3*(Real.sqrt n*parisiCDFDistance μ
        (parisiGridMeasure μ (vectorDyadicIndex j))+vectorDyadicFixedGradientError (n:=n) β t j) := by
  let N:=vectorDyadicIndex j
  let T:=parisiGradientMeshTime N r
  let S:=vectorDyadicFixedHessianSource (n:=n) μ β t outer ht.le j
  let E:=vectorDyadicFixedHessianError (n:=n) μ β t j
  let F:=fun i=>vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j (T i)-∫x in r..T i,S x
  have hc:0 ≤ (1-t)*β^2:=mul_nonneg (sub_nonneg.mpr ht.le) (sq_nonneg _)
  have hD:0 ≤ vectorDyadicFixedGradientError (n:=n) β t j:=vectorDyadicFixedGradientError_nonneg β t ht.le j
  have hSi (a b : ℝ) : IntervalIntegrable S volume a b:=
    vectorDyadicFixedHessianSource_intervalIntegrable μ β t outer ht.le j a b
  have heqcell (i : ℕ) (hi : i < N+1) (a b : ℝ) (hab : a < b)
      (ha : a∈Icc (hjbGridTime N i) (hjbGridTime N (i+1))) (hb : b=hjbGridTime N (i+1)) :
      ‖vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j b-
        vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j a-
        ∫x in a..b,S x‖ ≤ ∫x in a..b,E x := by
    let s:=parisiGridRSBScheme μ N
    obtain ⟨hq0,hq1⟩:=hjbGrid_cell_q μ N i hi
    have hq:s.q (i+1) < s.q (i+1+1):=by
      simpa only [s,hq0,show i+1+1=i+2 by omega,hq1] using hjbGridTime_step_lt N i
    have hha:s.q (i+1) ≤ a:=by simpa only [s,hq0] using ha.1
    have hhb:b ≤  s.q (i+1+1):=by simpa only [s,show i+1+1=i+2 by omega,hq1] using hb.le
    have hh:=vectorDyadicFixedHessian_cell_bound hn μ β t outer hβ ht j (i+1) (by omega) (by dsimp [N] at hi;omega)
      hq hha hab.le hhb (vectorDyadicFixedGradientError (n:=n) β t j)
      (vectorDyadicFixedGradientError_nonneg β t ht.le j) (vectorDyadicFixedGradientError_bound μ β t ht.le j)
    have herr : (∫x in a..b,vectorCellHessianError (n:=n) μ β t (s.m (i+1))
        (vectorDyadicFixedGradientError (n:=n) β t j) x)=∫x in a..b,E x := by
      apply intervalIntegral.integral_congr_uIoo
      rw [uIoo_of_le hab.le]
      intro x hx
      have hxcell:x∈Ico (s.q (i+1)) (s.q (i+1+1)):=by
        simpa only [s,hq0,show i+1+1=i+2 by omega,hq1] using
          (show x∈Ico (hjbGridTime N i) (hjbGridTime N (i+1)) from
            ⟨ha.1.trans hx.1.le,hx.2.trans_eq hb⟩)
      unfold E vectorDyadicFixedHessianError vectorCellHessianError
      rw [parisiCDF_grid_eq_scheme_mass μ N (i+1) (by omega) (by dsimp [N] at hi; omega) hxcell]
    rw [herr] at hh
    exact hh
  have htel:=parisiGradientMesh_norm_telescope F E T (N+1)
    (fun i _=>vectorDyadicFixedHessianError_intervalIntegrable μ β t j (T i) (T (i+1))) (by
      intro i hi
      rcases parisiGradientMeshTime_step_cases N r i with heq|hlt
      · simp only [F,T,heq,sub_self,norm_zero,intervalIntegral.integral_same,le_refl]
      · have hcell:=parisiGradientMeshTime_cell_subset N r i hlt
        have hh:=heqcell i hi (T i) (T (i+1)) hlt (hcell ⟨le_rfl,hlt.le⟩)
          (parisiGradientMeshTime_step_lt_terminal N r i hlt)
        have heF:F (i+1)-F i=vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j (T (i+1))-
            vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j (T i)-∫x in T i..T (i+1),S x := by
          dsimp only [F]
          have hii:=intervalIntegral.integral_interval_sub_left (hSi r (T (i+1))) (hSi r (T i))
          linarith
        rw [heF]
        exact hh)
  have hfull:(∫x in r..1,E x) ≤ ((1-t)*β^2)*vectorSpatialJetBound n 3*(Real.sqrt n*parisiCDFDistance μ
      (parisiGridMeasure μ N)+vectorDyadicFixedGradientError (n:=n) β t j) := by
    apply (parisiGradientMesh_integral_le_full hr (vectorDyadicFixedHessianError_intervalIntegrable μ β t j 0 1)
      (fun x=>by
        dsimp [E,vectorDyadicFixedHessianError]
        exact mul_nonneg (mul_nonneg hc (vectorSpatialJetBound_nonneg n 3))
          (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) hD))).trans_eq
    unfold vectorDyadicFixedHessianError parisiCDFDistance
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul]
    · simp only [intervalIntegral.integral_const,sub_zero,one_smul,smul_eq_mul,one_mul]
      rfl
    · exact (((parisiCDF_monotone μ).intervalIntegrable).sub
        ((parisiCDF_monotone (parisiGridMeasure μ N)).intervalIntegrable)).norm.const_mul _
    · exact intervalIntegrable_const
  have htel':‖F (N+1)-F 0‖ ≤ ∫x in r..1,E x:=by
    simpa only [T,parisiGradientMeshTime_terminal N hr.2,parisiGradientMeshTime_zero N hr.1] using htel
  have hh:=htel'.trans hfull
  have hefinal:F (N+1)-F 0=vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j 1-
      vectorDyadicFixedHessianMean (n:=n) μ β t outer ht.le j r-
      ∫x in r..1,S x := by
    simp only [F,T,parisiGradientMeshTime_terminal N hr.2,parisiGradientMeshTime_zero N hr.1,
      intervalIntegral.integral_same,sub_zero]
    ring
  rw [hefinal] at hh
  exact hh

end QuantitativePaper
