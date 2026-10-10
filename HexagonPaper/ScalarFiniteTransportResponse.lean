module
public import HexagonPaper.ScalarTransportCylinder
public import QuantitativeFollowup.ScalarTransportSevenTermDerivative

@[expose] public section

/-! The exact finite-profile response at every small base parameter. The
transported profile and the test are relabelled by the same homeomorphism;
this is an equality of literal probability pushforwards. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace HexagonPaper
open Paper FRSB QuantitativePaper FourPapersCommon SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

 theorem scalarTwoTransport_same_direction (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (u v : ℝ) :
    scalarTwoTransportMeasure μ φ φ (v,u)=scalarTransportMeasure μ φ (u+v) := by
  unfold scalarTwoTransportMeasure scalarTransportMeasure
  congr 1
  funext q
  change projIcc 0 1 zero_le_one ((q:ℝ)+1*scalarTwoDirection φ φ (v,u) q)=
    projIcc 0 1 zero_le_one ((q:ℝ)+(u+v)*φ q)
  simp only [scalarTwoDirection_apply,one_mul]
  congr 1
  ring

 theorem scalarLevelTransport_at_shift (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ)
    (hu : |u| *L<1) (v : ℝ) (q : Paper.Overlap) :
    scalarLevelTransport φ (u+v) q=
      scalarLevelTransport (scalarRelabelledDirection φ φ L hφ h0 h1 u hu) v
        (scalarLevelTransport φ u q) := by
  rw [←scalarTwoLevelTransport_relabelled φ φ L hφ h0 h1 u hu v q]
  change projIcc 0 1 zero_le_one ((q:ℝ)+(u+v)*φ q)=
    projIcc 0 1 zero_le_one ((q:ℝ)+1*scalarTwoDirection φ φ (v,u) q)
  simp only [scalarTwoDirection_apply,one_mul]
  congr 1
  ring

 theorem scalarTransportMeasure_at_shift (μ : Paper.ParisiMeasure)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ) (hu : |u| *L<1) (v : ℝ) :
    scalarTransportMeasure μ φ (u+v)=
      scalarTransportMeasure (scalarTransportMeasure μ φ u)
        (scalarRelabelledDirection φ φ L hφ h0 h1 u hu) v := by
  rw [←scalarTwoTransport_same_direction μ φ u v,
    scalarTwoTransport_relabelled μ φ φ L hφ h0 h1 u hu v]

 theorem hasDerivAt_scalarTransportGamma_finite_at {k : ℕ} (r : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : parisiSchemeMeasure r∈scalarFloor a)
    (u : ℝ) (hu : |u| *L<1) (p : Paper.Overlap) :
    HasDerivAt (fun v=>Gamma β (scalarTransportMeasure (parisiSchemeMeasure r) φ v)
      (scalarLevelTransport φ v p))
      (scalarResponseOperator β hβ.ne' (scalarTransportMeasure (parisiSchemeMeasure r) φ u) a
        (scalarRelabelledDirection φ φ L hφ h0 h1 u hu) (scalarLevelTransport φ u p)) u := by
  let t := scalarTransportScheme r φ L hφ h0 h1 u hu
  let χ := scalarRelabelledDirection φ φ L hφ h0 h1 u hu
  let K : ℝ≥0 := L*Real.toNNReal ((1-|u| *L)⁻¹)
  have hχ : LipschitzWith K χ := lipschitzWith_scalarRelabelledDirection φ φ L L hφ hφ h0 h1 u hu
  obtain ⟨hχ0,hχ1⟩ := scalarRelabelledDirection_endpoints φ φ L hφ h0 h1 h0 h1 u hu
  let δ : ℝ := 1/(2*((K:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  have hsmall : δ*K<1 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_lt_iff₀ (by positivity : 0<2*((K:ℝ)+1))).mpr
    linarith [K.coe_nonneg]
  have ht : parisiSchemeMeasure t∈scalarFloor a := by
    rw [scalarTransportScheme_measure]
    exact scalarTransportMeasure_mem_scalarFloor _ φ L hφ h0 h1 u hu a hμ
  have hd := hasDerivAt_scalarTransportGamma_seven_terms t β hβ χ K hχ hχ0 hχ1
    δ hδ hsmall a ha ht (scalarLevelTransport φ u p)
  rw [scalarTransportScheme_measure] at hd
  have hd0 : HasDerivAt (fun v=>Gamma β
      (scalarTransportMeasure (scalarTransportMeasure (parisiSchemeMeasure r) φ u) χ v)
      (scalarLevelTransport χ v (scalarLevelTransport φ u p)))
      (scalarResponseOperator β hβ.ne' (scalarTransportMeasure (parisiSchemeMeasure r) φ u) a
        χ (scalarLevelTransport φ u p)) (u-u) := by simpa only [sub_self] using hd
  have hdc := hd0.comp (h := fun v : ℝ => v-u) u ((hasDerivAt_id u).sub_const u)
  simp only [mul_one] at hdc
  apply hdc.congr_of_eventuallyEq
  exact .of_forall fun v=>by
    dsimp only [Function.comp_def,χ]
    rw [←scalarTransportMeasure_at_shift (parisiSchemeMeasure r) φ L hφ h0 h1 u hu (v-u),
      ←scalarLevelTransport_at_shift φ L hφ h0 h1 u hu (v-u) p]
    simp only [add_sub_cancel]

end HexagonPaper
