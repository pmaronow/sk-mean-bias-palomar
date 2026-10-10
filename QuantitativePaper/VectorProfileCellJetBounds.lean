module
public import QuantitativePaper.VectorProfileCellPartitionBounds
public import QuantitativePaper.VariableGaussianAverageJetBounds
public import QuantitativePaper.LogExponentialJetBounds
public import QuantitativePaper.CommonFiniteExponentialJetBounds
public import QuantitativePaper.ExponentialJetProducts
public import QuantitativePaper.BoundedFactorExponentialJets

@[expose] public section

/-! Genuine full joint jets of the actual strict affine-profile cell.
Every envelope is obtained from its Gaussian integral, actual positive
partition lower bound, and bounded inverse mass on the chosen profile crop. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorProfileCellGaussian_exp_jets (N : ℕ) (f : ℝ×VectorParameter n→ℝ)
    (c Q l u a b : ℝ) (hc : 0<c) (hu : u<Q)
    (hf : ∀y : ℝ×VectorParameter n,y.1∈Ioo a b → ContDiffAt ℝ ∞ f y)
    (K D : ℝ) (hK : 0≤K) (hD : 0≤D)
    (hjets : ∀r,r≤N→∀y : ℝ×VectorParameter n,y.1∈Ioo a b→
      ‖iteratedFDeriv ℝ r f y‖≤K*Real.exp (D*‖y‖)) :
    ∃C R : ℝ,1≤C ∧ 0≤R ∧ ∀r,r≤N→∀w∈vectorProfileCellCylinder l u a b,
      ‖iteratedFDeriv ℝ r (fun w : ℝ×(ℝ×VectorParameter n)=>
        ∫z,f (vectorProfileCellEvaluation c Q z w) ∂fieldGaussian n) w‖≤C*Real.exp (R*‖w‖) := by
  let U : Set (ℝ×VectorParameter n):={y|y.1∈Ioo a b}
  have hU : IsOpen U:=isOpen_Ioo.preimage continuous_fst
  have hv : Icc l u⊆Iio Q:=fun r hr=>hr.2.trans_lt hu
  have hl : ∀r∈Iio Q,ContDiffAt ℝ ∞ (fun q=>Real.sqrt (c*(Q-q))) r:=by
    intro r hr
    have hbase : ContDiffAt ℝ ∞ (fun q : ℝ=>c*(Q-q)) r:=by fun_prop
    exact hbase.sqrt (mul_pos hc (sub_pos.mpr hr)).ne'
  have hshift : ∀w∈vectorProfileCellCylinder (n:=n) l u a b,∀z,
    variableGaussianEvaluation (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n))
      (vectorProfileJointShift n 1) (fun r=>Real.sqrt (c*(Q-r))) z w∈U:=by
    intro w hw z
    change (vectorProfileCellEvaluation c Q z w).1∈Ioo a b
    rw [vectorProfileCellEvaluation_eq]
    exact hw.2
  have h:=variableGaussianAverage_iteratedFDeriv_bound N f U hU hf
    (ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n)) (vectorProfileJointShift n 1)
    (fun r=>Real.sqrt (c*(Q-r))) (Iio Q) isOpen_Iio hl
    (vectorProfileCellCylinder l u a b) (isOpen_vectorProfileCellCylinder l u a b) l u hv
    (fun w hw=>⟨hw.1.1.le,hw.1.2.le⟩) hshift K D hK hD hjets
  apply exists_common_finite_exponential_jet_bound N _ _
  intro r hr
  obtain ⟨C,R,hC,hR,hb⟩:=h r hr
  exact ⟨C,R,hC,hR,fun w hw=>(hb w hw).2⟩

theorem vectorProfileCellMass_inverse_exp_jets (s₀ s₁ : RSBScheme k)
    (i N : ℕ) (hpos : ∀θ∈Ioo (0:ℝ) 1,0<vectorProfileMass s₀ s₁ θ i)
    (l u a b : ℝ) (ha : 0<a) (hb : b<1) :
    ∃M : ℝ,1≤M ∧ ∀r,r≤N→∀w∈vectorProfileCellCylinder (n:=n) l u a b,
      ‖iteratedFDeriv ℝ r (fun w : ℝ×(ℝ×VectorParameter n)=>
        (vectorProfileMass s₀ s₁ w.2.1 i)⁻¹) w‖≤M := by
  obtain ⟨M,hM,hj⟩:=exists_vectorProfileMass_inverse_cylinder_bound (n:=n)
    s₀ s₁ i N hpos a b ha hb
  let f:=fun z : ℝ×VectorParameter n=>(vectorProfileMass s₀ s₁ z.1 i)⁻¹
  let U : Set (ℝ×VectorParameter n):={z|z.1∈Ioo (0:ℝ) 1}
  have hU : IsOpen U:=isOpen_Ioo.preimage continuous_fst
  have hf : ContDiffOn ℝ N f U:=by
    have hh : ContDiff ℝ N (fun z : ℝ×VectorParameter n=>vectorProfileMass s₀ s₁ z.1 i):=by
      unfold vectorProfileMass
      fun_prop
    exact hh.contDiffOn.inv (fun z hz=>(hpos z.1 hz).ne')
  let A : (ℝ×(ℝ×VectorParameter n))→L[ℝ](ℝ×VectorParameter n):=
    ContinuousLinearMap.snd ℝ ℝ (ℝ×VectorParameter n)
  have hA : ‖A‖≤1:=ContinuousLinearMap.norm_snd_le ℝ ℝ (ℝ×VectorParameter n)
  have hV : IsOpen (A⁻¹' U):=hU.preimage A.continuous
  refine ⟨M,hM,?_⟩
  intro r hr w hw
  have hx : A w∈U:=⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  have he:=A.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hV.uniqueDiffOn hx
    (by exact_mod_cast hr)
  rw [iteratedFDerivWithin_of_isOpen r hV hx,iteratedFDerivWithin_of_isOpen r hU hx] at he
  change ‖iteratedFDeriv ℝ r (f∘A) w‖≤M
  rw [he]
  have hn:=ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ r f (A w)) (fun _ : Fin r=>A)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hn
  apply hn.trans
  have hp : ‖A‖^r≤1:=by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg A) hA r
  exact (mul_le_mul (hj r hr w.2 ⟨hw.2.1.le,hw.2.2.le⟩) hp
    (pow_nonneg (norm_nonneg A) _) (zero_le_one.trans hM)).trans (by simp only [mul_one,le_refl])

theorem exists_vectorProfileCellFunction_common_exp_jets (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t≤1) (c Q l u a b : ℝ) (hc : 0<c) (hu : u<Q)
    (ha : 0<a) (hb : b<1) (N i j : ℕ) (hi : i≤k+1) :
    ∃C R : ℝ,1≤C ∧ 0≤R ∧ ∀r,r≤N→∀w∈vectorProfileCellCylinder (n:=n) l u a b,
      ‖iteratedFDeriv ℝ r (vectorProfileCellFunction s₀ s₁ β t c Q i j) w‖≤C*Real.exp (R*‖w‖) := by
  let W:=vectorProfileCellCylinder (n:=n) l u a b
  have hW : IsOpen W:=isOpen_vectorProfileCellCylinder l u a b
  have hθ (w : ℝ×(ℝ×VectorParameter n)) (hw : w∈W) : w.2.1∈Ioo (0:ℝ) 1:=
    ⟨ha.trans hw.2.1,hw.2.2.trans hb⟩
  rcases vectorProfileMass_zero_or_pos s₀ s₁ i hi with hm0|hmpos
  · obtain ⟨K,D,hK,hD,hj⟩:=exists_vectorProfileJointFunction_common_exp_jets
      (n:=n) s₀ s₁ β t ht N j a b ha hb
    obtain ⟨C,R,hC,hR,hbnd⟩:=vectorProfileCellGaussian_exp_jets N
      (vectorProfileJointFunction (n:=n) s₀ s₁ β t j) c Q l u a b hc hu
      (fun y hy=>contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht j y
        ⟨ha.trans hy.1,hy.2.trans hb⟩) K D (zero_le_one.trans hK) hD hj
    refine ⟨C,R,hC,hR,?_⟩
    intro r hr w hw
    have he : vectorProfileCellFunction s₀ s₁ β t c Q i j=ᶠ[𝓝 w]
        (fun w : ℝ×(ℝ×VectorParameter n)=>∫z,
          vectorProfileJointFunction s₀ s₁ β t j (vectorProfileCellEvaluation c Q z w) ∂fieldGaussian n):=by
      filter_upwards with y
      rw [vectorProfileCellFunction_eq_average_partition,if_pos (hm0 y.2.1)]
    rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]
    exact hbnd r hr w hw
  · let Z:=vectorProfileCellPartition (n:=n) s₀ s₁ β t c Q i j
    obtain ⟨K,D,hK,hD,hj⟩:=exists_vectorProfileCellExponent_exp_jets
      (n:=n) s₀ s₁ β t ht N i j hi a b ha hb
    have hf : ∀y : ℝ×VectorParameter n,y.1∈Ioo a b → ContDiffAt ℝ ∞
        (fun y=>Real.exp (vectorProfileCellExponent s₀ s₁ β t i j y)) y:=
      fun y hy=>(contDiffAt_vectorProfileCellExponent s₀ s₁ β t ht i j y
        ⟨ha.trans hy.1,hy.2.trans hb⟩).exp
    obtain ⟨C,R,hC,hR,hupper⟩:=vectorProfileCellGaussian_exp_jets N
      (fun y : ℝ×VectorParameter n=>Real.exp (vectorProfileCellExponent s₀ s₁ β t i j y))
      c Q l u a b hc hu hf K D hK hD hj
    have hZ : ContDiffOn ℝ N Z W:=vectorProfileCellGaussian_contDiffOn N
      (fun y : ℝ×VectorParameter n=>Real.exp (vectorProfileCellExponent s₀ s₁ β t i j y))
      c Q l u a b hc hu hf K D hK hD hj
    obtain ⟨d,T,hd,hT,hlower⟩:=exists_vectorProfileCellPartition_exponential_lower
      (n:=n) s₀ s₁ β t ht c Q l u a b hc hu ha hb i j hi
    have hlog:=log_iteratedFDeriv_exponential_bound Z W hW hZ C R d T
      (zero_le_one.trans hC) hR hd hT hupper hlower
    obtain ⟨B,L,hB,hL,hvalue⟩:=vectorProfileCellPartition_log_linear_growth
      (n:=n) s₀ s₁ β t ht c Q l u a b hc hu ha hb i j hi hmpos
    obtain ⟨A,S,hA,hS,hlogjets⟩:=exists_common_finite_exponential_jet_bound N
      (fun y=>Real.log (Z y)) W (by
        intro r hr
        by_cases hz : r=0
        · subst r
          refine ⟨B+L,1,add_nonneg hB hL,by norm_num,?_⟩
          intro w hw
          simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,one_mul]
          exact (hvalue w hw).trans (linear_growth_le_exponential B L ‖w‖ hB hL (norm_nonneg _))
        · exact hlog r (by omega) hr)
    obtain ⟨M,hM,hinvjets⟩:=vectorProfileCellMass_inverse_exp_jets (n:=n)
      s₀ s₁ i N hmpos l u a b ha hb
    let I:=fun w : ℝ×(ℝ×VectorParameter n)=>(vectorProfileMass s₀ s₁ w.2.1 i)⁻¹
    have hI : ContDiffOn ℝ N I W:=by
      have hm : ContDiff ℝ N (fun w : ℝ×(ℝ×VectorParameter n)=>vectorProfileMass s₀ s₁ w.2.1 i):=by
        unfold vectorProfileMass
        fun_prop
      exact hm.contDiffOn.inv (fun w hw=>(hmpos w.2.1 (hθ w hw)).ne')
    have hLog : ContDiffOn ℝ N (fun y=>Real.log (Z y)) W:=
      hZ.log (fun w hw=>(mul_pos hd (Real.exp_pos _)).trans_le (hlower w hw) |>.ne')
    have hprod:=bounded_factor_exponential_jets N (fun y=>Real.log (Z y)) I W hW hLog hI
      A S M (zero_le_one.trans hA) hS (zero_le_one.trans hM) hlogjets hinvjets
    apply exists_common_finite_exponential_jet_bound N _ W
    intro r hr
    refine ⟨(2:ℝ)^N*M*A,S,by positivity,hS,?_⟩
    intro w hw
    have he : vectorProfileCellFunction s₀ s₁ β t c Q i j=ᶠ[𝓝 w]
        (fun y=>I y*Real.log (Z y)):=by
      filter_upwards [hW.mem_nhds hw] with y hy
      rw [vectorProfileCellFunction_eq_average_partition,if_neg (hmpos y.2.1 (hθ y hy)).ne']
      rfl
    rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]
    exact hprod r hr w hw

end QuantitativePaper
