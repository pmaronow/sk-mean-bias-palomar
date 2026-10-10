module
public import HexagonPaper.CavityFixedRowJetsRest

@[expose] public section

/-! Exact actual native rest observable incident-row derivatives, for arbitrary profiles. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators NNReal ContDiff
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem cavityFixedRow_native_rest_magnetization (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (l : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    anisotropicMeasureTailMagnetization D μ q P l.castSucc=
      anisotropicMeasureTailMagnetization R μ q (cavityRestParameterProjection n P) l := by
  have hh:=congrArg (fun v : QuantitativePaper.Field n=>v l)
    (followupCavityMeasureGradient_rest_zero μ n β ρ hβ hρ q g x)
  simpa only [cavityRestFieldProjection_apply,cavityRestParameterProjection_point] using hh

theorem cavityFixedRow_native_pair_first_field (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n)
    (e : AnisotropicCouplingIndex n) (i : Fin n) :
    fderiv ℝ (fun Q=>fderiv ℝ (anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q)
      Q (anisotropicCouplingDirection e))
      (anisotropicCouplingRescaling D P) (anisotropicCoordinateDirection n i)=
    fderiv ℝ (fun Q=>anisotropicTailPairResponse D μ q Q e) P
      (anisotropicCoordinateDirection n i) := by
  rw [cavity_directional_second_symmetry _
    (cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1]
  exact cavityFixedRow_native_magnetization_row_first D μ q P e i

theorem cavityNativeSum_second {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type} [Fintype ι] (F : ι→E→ℝ) (hF : ∀i,ContDiff ℝ ∞ (F i)) (H K : E) (c : ℝ) :
    fderiv ℝ (fun Q=>fderiv ℝ (fun R=>c*∑i,F i R) Q K) H K=
      c*∑i,fderiv ℝ (fun Q=>fderiv ℝ (F i) Q K) H K := by
  have he:(fun Q=>fderiv ℝ (fun R=>c*∑i,F i R) Q K)=
      fun Q=>c*∑i,fderiv ℝ (F i) Q K := by
    funext Q
    rw [fderiv_const_mul (DifferentiableAt.fun_sum (fun i _=>(hF i).differentiable (by simp) Q)),
      ContinuousLinearMap.smul_apply,smul_eq_mul,
      fderiv_fun_sum (fun i _=>(hF i).differentiable (by simp) Q),ContinuousLinearMap.sum_apply]
  have hd (i : ι) : DifferentiableAt ℝ (fun Q=>fderiv ℝ (F i) Q K) H:=
    (((hF i).fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) H
  rw [he,fderiv_const_mul (DifferentiableAt.fun_sum (fun i _=>hd i)),
    ContinuousLinearMap.smul_apply,smul_eq_mul,fderiv_fun_sum (fun i _=>hd i),
    ContinuousLinearMap.sum_apply]

theorem cavityNativeSum_mul_middle {ι : Type} [Fintype ι] (A B : ι→ℝ) (m : ℝ) :
    (∑i,A i*(m*B i))=m*∑i,A i*B i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cavityFixedRow_native_restSquare_first (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    let Pr:=cavityRestParameterProjection n P
    let M:=anisotropicMeasureTailMagnetization R μ q Pr
    let m:=Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))
    deriv (cavityFixedRowNativeRestSquare D μ q P i) 0=
      2*m/(n:ℝ)*∑l : Fin n,M l*
        fderiv ℝ (fun Q=>anisotropicMeasureTailMagnetization R μ q Q i) Pr
          (anisotropicCoordinateDirection n l) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  let P:=anisotropicParameterPoint g x
  let H:=anisotropicCouplingRescaling D P
  let K:=anisotropicCouplingDirection (anisotropicCavityRowIndex n i)
  let F:=fun l : Fin n=>fun Q=>fderiv ℝ U Q (anisotropicCoordinateDirection (n+1) l.castSucc)
  have hU:ContDiff ℝ ∞ U:=(cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1
  have hF (l : Fin n):ContDiff ℝ ∞ (F l):=
    (hU.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hG:ContDiff ℝ ∞ (fun Q=>(n:ℝ)⁻¹*∑l : Fin n,(F l Q)^2):=
    contDiff_const.mul (ContDiff.sum (fun l _=>(hF l).pow 2))
  change deriv (fun θ=>(n:ℝ)⁻¹*∑l : Fin n,(F l (H+θ • K))^2) 0=_
  rw [(hasDerivAt_affine_line_of_differentiable _ (hG.differentiable (by simp)) H K 0).deriv]
  simp only [zero_smul,add_zero]
  rw [cavityNativeSumSquares_first F hF]
  dsimp only [F,U,H,K,P,D]
  simp_rw [cavityFixedRow_native_field_unitCouplings,
    cavityFixedRow_native_magnetization_row_first,
    cavityFixedRow_native_rest_magnetization μ n β ρ hβ hρ q g x,
    cavityFixedRow_native_pair_rest_derivative μ n β ρ hβ hρ q g x i]
  rw [cavityNativeSum_mul_middle]
  ring

theorem cavityFixedRow_native_restSquare_second (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    let Pr:=cavityRestParameterProjection n P
    let M:=anisotropicMeasureTailMagnetization R μ q Pr
    let m:=Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))
    let Wij:=fun l : Fin n=>fderiv ℝ
      (fun Q=>anisotropicTailPairSecond D μ q Q (anisotropicCavityRowIndex n i)) P
      (anisotropicCoordinateDirection (n+1) l.castSucc)
    deriv (deriv (cavityFixedRowNativeRestSquare D μ q P i)) 0=
      2/(n:ℝ)*(m^2*∑l : Fin n,
        (fderiv ℝ (fun Q=>anisotropicMeasureTailMagnetization R μ q Q i) Pr
          (anisotropicCoordinateDirection n l))^2+∑l : Fin n,M l*Wij l) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
  let U:=anisotropicMeasureTailPotential (anisotropicUnitCouplings D) μ q
  let P:=anisotropicParameterPoint g x
  let H:=anisotropicCouplingRescaling D P
  let K:=anisotropicCouplingDirection (anisotropicCavityRowIndex n i)
  let F:=fun l : Fin n=>fun Q=>(fderiv ℝ U Q (anisotropicCoordinateDirection (n+1) l.castSucc))^2
  let G:=fun Q=>(n:ℝ)⁻¹*∑l : Fin n,F l Q
  have hU:ContDiff ℝ ∞ U:=(cavityTree_native_tail_smooth_and_jets (anisotropicUnitCouplings D) μ q).1
  have hF (l : Fin n):ContDiff ℝ ∞ (F l):=
    ((hU.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const).pow 2
  have hG:ContDiff ℝ ∞ G:=contDiff_const.mul (ContDiff.sum (fun l _=>hF l))
  change deriv (deriv (fun θ=>G (H+θ • K))) 0=_
  rw [cavityPrintedFiniteRow_deriv_deriv_affine_line G hG H K]
  change fderiv ℝ (fderiv ℝ G) H K K=_
  rw [←show fderiv ℝ (fun Q=>fderiv ℝ G Q K) H K=fderiv ℝ (fderiv ℝ G) H K K by
    rw [(hasFDerivAt_exponential_directional_field G (hG.of_le (by simp)) H K).fderiv]
    rfl]
  rw [show (fun Q=>fderiv ℝ G Q K)=(fun Q=>fderiv ℝ (fun R=>(n:ℝ)⁻¹*∑l,F l R) Q K) from rfl,
    cavityNativeSum_second F hF]
  dsimp only [F]
  simp_rw [cavityNativeDirectionalSquare_second U hU]
  dsimp only [U,H,K,P,D]
  simp_rw [cavityFixedRow_native_field_unitCouplings,
    cavityFixedRow_native_pair_first_field,
    cavityFixedRow_native_rest_magnetization μ n β ρ hβ hρ q g x,
    cavityFixedRow_native_pair_rest_derivative μ n β ρ hβ hρ q g x i,
    cavityFixedRow_native_pair_second_field]
  have halg (m a b c : ℝ) : 2*(m*a)^2+2*b*c=2*(m^2*a^2+b*c) := by ring
  simp_rw [halg]
  rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum]
  ring

end HexagonPaper
