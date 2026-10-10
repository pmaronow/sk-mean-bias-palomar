module
public import HexagonPaper.CavityFixedRowJetsRestObservables

@[expose] public section

/-! The literal Hessian-matrix and spatial-gradient notation in the native
arbitrary-profile incident-row observable identities. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology BigOperators NNReal ContDiff
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def cavityFixedRowNativeFieldHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i l=>fderiv ℝ (fun Q=>anisotropicMeasureTailMagnetization D μ q Q i) P
    (anisotropicCoordinateDirection n l)

theorem cavityFixedRowNativeFieldHessian_symmetric (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (i l : Fin n) :
    cavityFixedRowNativeFieldHessian D μ q P i l=cavityFixedRowNativeFieldHessian D μ q P l i := by
  exact cavity_directional_second_symmetry (anisotropicMeasureTailPotential D μ q)
    (cavityTree_native_tail_smooth_and_jets D μ q).1 P
    (anisotropicCoordinateDirection n i) (anisotropicCoordinateDirection n l)

def cavityFixedRowNativeHessianColumn (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter n) (i : Fin n) : QuantitativePaper.Field n :=
  WithLp.toLp 2 (fun l=>cavityFixedRowNativeFieldHessian D μ q P l i)

def cavityFixedRowNativeRestWiGradient (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (P : AnisotropicParameter (n+1)) (i : Fin n) : QuantitativePaper.Field n :=
  WithLp.toLp 2 (fun l=>fderiv ℝ
    (fun Q=>anisotropicTailPairSecond D μ q Q (anisotropicCavityRowIndex n i)) P
      (anisotropicCoordinateDirection (n+1) l.castSucc))

theorem cavityFixedRow_native_restSquare_first_matrix (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    let Pr:=cavityRestParameterProjection n P
    let M:=anisotropicMeasureTailMagnetization R μ q Pr
    let H:=cavityFixedRowNativeFieldHessian R μ q Pr
    let m:=Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))
    deriv (cavityFixedRowNativeRestSquare D μ q P i) 0=2*m/(n:ℝ)*(H.mulVec M.ofLp) i := by
  dsimp only
  rw [cavityFixedRow_native_restSquare_first]
  congr 1
  unfold Matrix.mulVec dotProduct cavityFixedRowNativeFieldHessian
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem cavityFixedRow_native_restSquare_second_matrix (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (g : AnisotropicDisorder (n+1)) (x : QuantitativePaper.Field (n+1)) (i : Fin n) :
    let D:=followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩
    let R:=followupCavityRestSpinModel n β ρ hβ hρ
    let P:=anisotropicParameterPoint g x
    let Pr:=cavityRestParameterProjection n P
    let M:=anisotropicMeasureTailMagnetization R μ q Pr
    let m:=Paper.parisiGradient (followupCavityScalarBeta n β ρ) μ (q,x (Fin.last n))
    deriv (deriv (cavityFixedRowNativeRestSquare D μ q P i)) 0=
      2/(n:ℝ)*(m^2*‖cavityFixedRowNativeHessianColumn R μ q Pr i‖^2+
        inner ℝ M (cavityFixedRowNativeRestWiGradient D μ q P i)) := by
  dsimp only
  rw [cavityFixedRow_native_restSquare_second,EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.inner_eq_star_dotProduct]
  simp only [cavityFixedRowNativeHessianColumn,cavityFixedRowNativeRestWiGradient,
    WithLp.ofLp_toLp,Pi.star_apply,star_trivial,dotProduct]
  simp_rw [cavityFixedRowNativeFieldHessian_symmetric _ _ _ _ _ i]
  simp only [cavityFixedRowNativeFieldHessian]
  congr 2
  apply Finset.sum_congr rfl
  intro l _
  ring

end HexagonPaper
