module
public import QuantitativeFollowup.FollowupCavityFixedRowMixtureCheckpoint
public import QuantitativeFollowup.FollowupCavityMixtureCovariance

@[expose] public section

/-! Actual retained-node means and covariance of the deterministic row,
and their equality to the correctly normalized Gaussian row mixture. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped ContDiff
namespace QuantitativeFollowup
open SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

private theorem measurable_row_field_selector {E S : Type} [MeasurableSpace E]
    [MeasurableSpace S] (j d : ℕ) :
    Measurable (fun z : E×Records E S (observationLinearTree j)=>
      cavityFixedRowLineField j d z.1 z.2) := by
  induction j with
  | zero => exact measurable_fst
  | succ j ih =>
    by_cases hd:d=j+1
    · simpa only [cavityFixedRowLineField,hd,ite_true] using
        (measurable_fst : Measurable (fun z : E×(E×Records E S (observationLinearTree j))=>z.1))
    · simpa only [cavityFixedRowLineField,hd,ite_false,Function.comp_def] using ih.comp measurable_snd

theorem measurable_cavityFixedRowLastSquare_from_factory (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) : Measurable (cavityFixedRowLastSquare D s d) :=
  (boundedJets_cavityFixedRowLastFieldSquare D s d).1.continuous.measurable.comp
    (measurable_row_field_selector (k+2) d)

theorem measurable_cavityFixedRowRestSquare_from_factory (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (d : ℕ) : Measurable (cavityFixedRowRestSquare D s d) :=
  (boundedJets_cavityFixedRowRestFieldSquare D s d).1.continuous.measurable.comp
    (measurable_row_field_selector (k+2) d)

def cavityFixedRowLastMean (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (theta : Field n) : ℝ :=
  ∫z,cavityFixedRowLastSquare D s d z∂cavityFixedRowLaw D s a theta

def cavityFixedRowRestMean (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (theta : Field n) : ℝ :=
  ∫z,cavityFixedRowRestSquare D s d z∂cavityFixedRowLaw D s a theta

def cavityFixedRowProductMean (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (theta : Field n) : ℝ :=
  ∫z,cavityFixedRowLastSquare D s d z*cavityFixedRowRestSquare D s d z∂cavityFixedRowLaw D s a theta

def cavityFixedRowCovariance (D : AnisotropicSpinModel (n+1)) (s : RSBScheme k)
    (a : ℝ) (d : ℕ) (theta : Field n) : ℝ :=
  cavityFixedRowProductMean D s a d theta-
    cavityFixedRowLastMean D s a d theta*cavityFixedRowRestMean D s a d theta

def cavityFixedRowVarianceCovariance (beta rho : ℝ) (hbeta : 0<beta)
    (hrho : rho∈Ioc (0:ℝ) 1) (s : RSBScheme k) (a : ℝ) (d : ℕ) (v : ℝ) : ℝ :=
  let D0:=followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩
  let P:=anisotropicFiniteRecordedTreeLaw (cavityFixedRowVarianceModel n beta rho hbeta hrho v)
    s a (observationLinearTree (k+2))
  (∫z,cavityFixedRowLastSquare D0 s d z*cavityFixedRowRestSquare D0 s d z∂P)-
    (∫z,cavityFixedRowLastSquare D0 s d z∂P)*(∫z,cavityFixedRowRestSquare D0 s d z∂P)

theorem cavityFixedRowVarianceCovariance_eq_weighted
    (beta rho : ℝ) (hbeta : 0<beta) (hrho : rho∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (d : ℕ) (v : ℝ) (hv : 0≤v) :
    let D0:=followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩
    cavityFixedRowVarianceCovariance (n:=n) beta rho hbeta hrho s a d v=
      cavityRowWeightedAverage (cavityFixedRowNormalizer D0 s a) (cavityFixedRowProductMean D0 s a d) v-
      cavityRowWeightedAverage (cavityFixedRowNormalizer D0 s a) (cavityFixedRowLastMean D0 s a d) v*
      cavityRowWeightedAverage (cavityFixedRowNormalizer D0 s a) (cavityFixedRowRestMean D0 s a d) v := by
  dsimp only
  let D0:=followupCavitySpinModel n beta rho hbeta hrho 0 ⟨le_rfl,zero_le_one⟩
  obtain ⟨B,hB,hb⟩:=exists_cavityFixedRowObservable_bounds D0 s d
  have hmF:=measurable_cavityFixedRowLastSquare_from_factory D0 s d
  have hmG:=measurable_cavityFixedRowRestSquare_from_factory D0 s d
  have hF:=cavityFixedRow_weighted_mixture beta rho hbeta hrho v hv s a
    (cavityFixedRowLastSquare D0 s d) hmF B hB (fun z=>(hb z).1)
  have hG:=cavityFixedRow_weighted_mixture beta rho hbeta hrho v hv s a
    (cavityFixedRowRestSquare D0 s d) hmG B hB (fun z=>(hb z).2.1)
  have hFG:=cavityFixedRow_weighted_mixture beta rho hbeta hrho v hv s a
    (fun z=>cavityFixedRowLastSquare D0 s d z*cavityFixedRowRestSquare D0 s d z)
    (hmF.mul hmG) B hB (fun z=>(hb z).2.2)
  dsimp only [cavityFixedRowVarianceCovariance]
  change (∫z,cavityFixedRowLastSquare D0 s d z*cavityFixedRowRestSquare D0 s d z
    ∂anisotropicFiniteRecordedTreeLaw (cavityFixedRowVarianceModel n beta rho hbeta hrho v) s a
      (observationLinearTree (k+2)))-
    (∫z,cavityFixedRowLastSquare D0 s d z
      ∂anisotropicFiniteRecordedTreeLaw (cavityFixedRowVarianceModel n beta rho hbeta hrho v) s a
        (observationLinearTree (k+2)))*
    (∫z,cavityFixedRowRestSquare D0 s d z
      ∂anisotropicFiniteRecordedTreeLaw (cavityFixedRowVarianceModel n beta rho hbeta hrho v) s a
        (observationLinearTree (k+2))) = _
  rw [hF,hG,hFG]
  rfl

end QuantitativeFollowup
