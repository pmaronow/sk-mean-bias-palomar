module
public import QuantitativeFollowup.ScalarFiniteObservableDerivatives
public import QuantitativePaper.BoundedJets
public import QuantitativePaper.VectorExponentialHeatData

@[expose] public section

/-! Actual exponential Gaussian-integrability data for the finite scalar
marked density and the squared-gradient observable. All regularity and
positive-jet bounds are discharged for the physical PDE solution. -/
noncomputable section
open Set
open scoped NNReal BigOperators ContDiff
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem boundedPositiveJets_scalarPotential (β : ℝ) (μ : Paper.ParisiMeasure)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    BoundedPositiveJets (fun x : ℝ=>Paper.parisiPotential β μ (t,x)) := by
  refine ⟨Paper.contDiff_parisiPotential_spatial β μ t ht,?_⟩
  intro j hj
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j≠0)
  obtain ⟨K,hK,hb⟩ := FRSB.positive_order_spatial_derivatives_uniform β n
  refine ⟨K,hK.le,fun x=>?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hb μ ⟨t,ht⟩ x

theorem boundedPositiveJets_scalarFiniteEuclideanExponent (s : RSBScheme k)
    (β : ℝ) (e : Bool) : BoundedPositiveJets (scalarFiniteEuclideanExponent s β e) := by
  have ht (i : Fin (k+1)) : (FRSB.forwardSchemeTime s 1 (i+1):ℝ)∈Icc (0:ℝ) 1 :=
    ⟨(FRSB.forwardSchemeTime s 1 (i+1)).coe_nonneg,FRSB.forwardSchemeTime_le s 1 _⟩
  have hlin := (boundedPositiveJets_linear
    (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) (Fin.last (k+2)))).const_mul (Paper.spinSign e)
  have hsum := boundedPositiveJets_finite_sum Finset.univ
    (fun i : Fin (k+1)=>fun x : QuantitativePaper.Field (k+3)=>
      (s.m (i+1)-s.m i)*Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
        (FRSB.forwardSchemeTime s 1 (i+1),x ⟨i+1,by omega⟩))
    (fun i _=>((boundedPositiveJets_scalarPotential β (Paper.parisiSchemeMeasure s) _ (ht i)).comp_linear
      (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) ⟨i+1,by omega⟩)).const_mul _)
  exact hlin.add hsum.neg

theorem boundedJets_scalarFiniteHistoryGradient (s : RSBScheme k) (β : ℝ)
    (p : Fin (k+3)) :
    BoundedJets (fun x : QuantitativePaper.Field (k+3)=>Paper.parisiGradient β
      (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)) := by
  have ht : (FRSB.forwardSchemeTime s 1 p:ℝ)∈Icc (0:ℝ) 1 :=
    ⟨(FRSB.forwardSchemeTime s 1 p).coe_nonneg,FRSB.forwardSchemeTime_le s 1 _⟩
  have hh := (boundedPositiveJets_scalarPotential β (Paper.parisiSchemeMeasure s) _ ht).boundedJets_fderiv_apply (1:ℝ)
  have he : (fun x : ℝ=>fderiv ℝ (fun y=>Paper.parisiPotential β (Paper.parisiSchemeMeasure s)
      (FRSB.forwardSchemeTime s 1 p,y)) x 1)=
      (fun x=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x)) := by
    funext x
    rw [(Paper.hasDerivAt_parisiPotential_spatial_all β (Paper.parisiSchemeMeasure s) _ x ht).hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,one_mul]
  rw [he] at hh
  exact hh.comp_linear (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin (k+3)=>ℝ) p)

theorem boundedJets_scalarFiniteGradientSquare (s : RSBScheme k) (β : ℝ)
    (p : Fin (k+3)) : BoundedJets (scalarFiniteGradientSquare s β p) := by
  have h := boundedJets_scalarFiniteHistoryGradient s β p
  change BoundedJets (fun x : QuantitativePaper.Field (k+3)=>Paper.parisiGradient β
    (Paper.parisiSchemeMeasure s) (FRSB.forwardSchemeTime s 1 p,x p)^2)
  simpa only [pow_two] using h.mul h

/-- Bounded positive jets of the exponent and bounded observable jets imply
honest Gaussian exponential data. This obtains the integral envelopes from
actual jets, rather than introducing them as a response conclusion. -/
theorem vectorHeatDatum_of_boundedJets {m : ℕ} (V F : QuantitativePaper.Field m→ℝ)
    (hV : BoundedPositiveJets V) (hF : BoundedJets F) :
    Nonempty (VectorHeatDatum (fun x=>Real.exp (V x)*F x)) := by
  obtain ⟨B,hB,hb⟩ := hV.2 1 (by norm_num)
  obtain ⟨C,hC,hc⟩ := hV.2 2 (by norm_num)
  let K := max 1 (max B C)
  have hK1 : 1≤K := le_max_left _ _
  have hBK : B≤K := (le_max_left _ _).trans (le_max_right _ _)
  have hCK : C≤K := (le_max_right _ _).trans (le_max_right _ _)
  have hK : 0≤K := zero_le_one.trans hK1
  have hK2 : K≤K^2 := by nlinarith
  have hfirst (x : QuantitativePaper.Field m) : ‖fderiv ℝ V x‖≤K := by
    rw [←norm_iteratedFDeriv_one]
    exact (hb x).trans hBK
  let L : ℝ≥0 := ⟨K,hK⟩
  have hLip : LipschitzWith L V := lipschitzWith_of_nnnorm_fderiv_le
    (hV.1.differentiable (by simp)) (fun x=>NNReal.coe_le_coe.mp (hfirst x))
  choose G hG hg using hF.2
  have hh := vectorHeatDatum_exp_observable V F (hV.1.of_le (by simp))
    (hF.1.of_le (by simp)) L hLip 1 K hK G hG
    (fun j hj hj' x=>by
      interval_cases j
      · simpa only [pow_one] using (hb x).trans hBK
      · exact (hc x).trans (hCK.trans hK2))
    (fun j _ x=>hg j x)
  simpa only [one_mul] using hh

theorem scalarFiniteGaussianWeight_heatData (s : RSBScheme k) (β : ℝ) (e : Bool) :
    Nonempty (VectorHeatDatum (fun x=>Real.exp (scalarFiniteEuclideanExponent s β e x))) := by
  simpa only [mul_one] using vectorHeatDatum_of_boundedJets (scalarFiniteEuclideanExponent s β e)
    (fun _=>1) (boundedPositiveJets_scalarFiniteEuclideanExponent s β e) (boundedJets_const 1)

theorem scalarFiniteGaussianSquare_heatData (s : RSBScheme k) (β : ℝ)
    (e : Bool) (p : Fin (k+3)) :
    Nonempty (VectorHeatDatum (fun x=>Real.exp (scalarFiniteEuclideanExponent s β e x)*
      scalarFiniteGradientSquare s β p x)) :=
  vectorHeatDatum_of_boundedJets _ _ (boundedPositiveJets_scalarFiniteEuclideanExponent s β e)
    (boundedJets_scalarFiniteGradientSquare s β p)

end QuantitativeFollowup
