module
public import HexagonPaper.ScalarResponseParameterContinuity
public import HexagonPaper.ScalarFiniteTransportResponse
public import QuantitativeFollowup.ScalarStepResponse
public import QuantitativeFollowup.ParisiFreeGrid
public import FRSB.ParisiGridTopology
public import FRSB.GridMeasureIdentification
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! The scalar response identity for arbitrary probability profiles.
Finite-profile responses converge uniformly on a genuine fixed transport
neighborhood; the uniform derivative limit theorem differentiates the
literal transported mean-square function of the original measure. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ContDiff
namespace HexagonPaper
open Paper FRSB QuantitativePaper FourPapersCommon SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

 def scalarCylinderResponse (β : ℝ) (hβ : β≠0) (s : ℝ)
    (μ : ScalarFloorMeasure s) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) (p : Paper.Overlap)
    (u : ScalarTransportParameter δ) : ℝ :=
  scalarResponseOperator β hβ (scalarTransportMeasure μ.val φ u) s
    (scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall u)
    (scalarLevelTransport φ u p)

 theorem continuous_scalarCylinderResponse (β : ℝ) (hβ : β≠0) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) (p : Paper.Overlap) :
    Continuous (fun z : ScalarFloorMeasure s×ScalarTransportParameter δ =>
      scalarCylinderResponse β hβ s z.1 φ L hφ h0 h1 δ hsmall p z.2) := by
  let A := ScalarFloorMeasure s×ScalarTransportParameter δ
  have hm : Continuous (fun z : A => scalarTransportMeasure z.1.val φ z.2) :=
    (continuous_scalarTransportMeasure φ).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  have hm' : Continuous (fun z : A =>
      (⟨scalarTransportMeasure z.1.val φ z.2,
        scalarTransportMeasure_mem_scalarFloor z.1.val φ L hφ h0 h1 z.2
          (scalarTransportParameter_small δ L hsmall z.2) s z.1.property⟩ : ScalarFloorMeasure s)) :=
    hm.subtype_mk _
  have ht : Continuous (fun z : A => scalarLevelTransport φ z.2 p) :=
    (continuous_scalarLevelTransport φ).comp
      ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const)
  have hdir : Continuous (fun z : A =>
      scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall z.2) :=
    (continuous_scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall).comp continuous_snd
  convert! (continuous_scalarResponseOperator_joint_test β hβ s hs).comp ((hm'.prodMk hdir).prodMk ht) using 1


 theorem continuous_scalarCylinderResponse_joint_level (β : ℝ) (hβ : β≠0) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) :
    Continuous (fun z : (ScalarFloorMeasure s×ScalarTransportParameter δ)×Paper.Overlap =>
      scalarCylinderResponse β hβ s z.1.1 φ L hφ h0 h1 δ hsmall z.2 z.1.2) := by
  let A := (ScalarFloorMeasure s×ScalarTransportParameter δ)×Paper.Overlap
  have hm : Continuous (fun z : A => scalarTransportMeasure z.1.1.val φ z.1.2) :=
    (continuous_scalarTransportMeasure φ).comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hm' : Continuous (fun z : A =>
      (⟨scalarTransportMeasure z.1.1.val φ z.1.2,
        scalarTransportMeasure_mem_scalarFloor z.1.1.val φ L hφ h0 h1 z.1.2
          (scalarTransportParameter_small δ L hsmall z.1.2) s z.1.1.property⟩ : ScalarFloorMeasure s)) :=
    hm.subtype_mk _
  have ht : Continuous (fun z : A => scalarLevelTransport φ z.1.2 z.2) :=
    (continuous_scalarLevelTransport φ).comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have hdir : Continuous (fun z : A =>
      scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall z.1.2) :=
    (continuous_scalarCylinderRelabelledDirection φ L hφ h0 h1 δ hsmall).comp
      (continuous_snd.comp continuous_fst)
  convert! (continuous_scalarResponseOperator_joint_test β hβ s hs).comp
    ((hm'.prodMk hdir).prodMk ht) using 1

 def scalarCylinderResponseMap (β : ℝ) (hβ : β≠0) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (μ : ScalarFloorMeasure s)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (h0 : φ 0=0) (h1 : φ 1=0) (δ : ℝ) (hsmall : δ*L<1) (p : Paper.Overlap) :
    C(ScalarTransportParameter δ,ℝ) :=
  ⟨scalarCylinderResponse β hβ s μ φ L hφ h0 h1 δ hsmall p,by
    convert! (continuous_scalarCylinderResponse β hβ s hs φ L hφ h0 h1 δ hsmall p).comp
      (continuous_const.prodMk continuous_id) using 1⟩

 theorem continuous_scalarCylinderResponseMap (β : ℝ) (hβ : β≠0) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hsmall : δ*L<1) (p : Paper.Overlap) :
    Continuous (fun μ : ScalarFloorMeasure s =>
      scalarCylinderResponseMap β hβ s hs μ φ L hφ h0 h1 δ hsmall p) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_scalarCylinderResponse β hβ s hs φ L hφ h0 h1 δ hsmall p)

 def scalarTransportResponseExtension (β : ℝ) (hβ : β≠0) (s : ℝ)
    (μ : ScalarFloorMeasure s) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (p : Paper.Overlap) (u : ℝ) : ℝ :=
  scalarCylinderResponse β hβ s μ φ L hφ h0 h1 δ hsmall p
    (projIcc (-δ) δ (by linarith) u)

 theorem continuous_scalarTransportResponseExtension (β : ℝ) (hβ : β≠0) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (μ : ScalarFloorMeasure s) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (p : Paper.Overlap) :
    Continuous (scalarTransportResponseExtension β hβ s μ φ L hφ h0 h1 δ hδ hsmall p) :=
  (scalarCylinderResponseMap β hβ s hs μ φ L hφ h0 h1 δ hsmall p).continuous.comp
    (continuous_projIcc (a := -δ) (b := δ) (h := by linarith))

 theorem scalarTransportResponseExtension_eq (β : ℝ) (hβ : β≠0) (s : ℝ)
    (μ : ScalarFloorMeasure s) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (p : Paper.Overlap)
    (u : ℝ) (hu : u∈Icc (-δ) δ) :
    scalarTransportResponseExtension β hβ s μ φ L hφ h0 h1 δ hδ hsmall p u=
      scalarResponseOperator β hβ (scalarTransportMeasure μ.val φ u) s
        (scalarRelabelledDirection φ φ L hφ h0 h1 u
          ((mul_le_mul_of_nonneg_right (abs_le.mpr hu) L.coe_nonneg).trans_lt hsmall))
        (scalarLevelTransport φ u p) := by
  unfold scalarTransportResponseExtension
  rw [projIcc_of_mem (by linarith) hu]
  unfold scalarCylinderResponse
  rw [scalarCylinderRelabelledDirection_eq]

 theorem tendstoUniformly_scalarTransportResponseExtension (β : ℝ) (hβ : β≠0) (s : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (μs : ℕ→ScalarFloorMeasure s) (μ : ScalarFloorMeasure s)
    (hweak : Tendsto μs atTop (𝓝 μ)) (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0)
    (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1) (p : Paper.Overlap) :
    TendstoUniformly (fun n => scalarTransportResponseExtension β hβ s (μs n)
      φ L hφ h0 h1 δ hδ hsmall p)
      (scalarTransportResponseExtension β hβ s μ φ L hφ h0 h1 δ hδ hsmall p) atTop := by
  have hmap := (continuous_scalarCylinderResponseMap β hβ s hs φ L hφ h0 h1 δ hsmall p).tendsto μ |>.comp hweak
  have hU := ContinuousMap.tendsto_iff_tendstoUniformly.mp hmap
  exact hU.comp (fun u : ℝ => projIcc (-δ) δ (by linarith) u)

 theorem hasDerivAt_scalarTransportGamma_general_at (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (h0 : φ 0=0) (h1 : φ 1=0) (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1)
    (p : Paper.Overlap) (u : ℝ) (hu : u∈Ioo (-δ) δ) :
    HasDerivAt (fun v=>Gamma β (scalarTransportMeasure μ φ v) (scalarLevelTransport φ v p))
      (scalarTransportResponseExtension β hβ.ne' s ⟨μ,hμ⟩ φ L hφ h0 h1 δ hδ hsmall p u) u := by
  let μn : ℕ→ScalarFloorMeasure s := fun n =>
    ⟨parisiGridMeasure μ n,parisiGridMeasure_mem_scalarFloor μ s hμ n⟩
  have hweak : Tendsto μn atTop (𝓝 (⟨μ,hμ⟩ : ScalarFloorMeasure s)) :=
    tendsto_subtype_rng.mpr (tendsto_parisiGridMeasure μ)
  have hD := tendstoUniformly_scalarTransportResponseExtension β hβ.ne' s hs μn ⟨μ,hμ⟩
    hweak φ L hφ h0 h1 δ hδ hsmall p
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hD.tendstoUniformlyOn
    (f := fun n v=>Gamma β (scalarTransportMeasure (parisiGridMeasure μ n) φ v)
      (scalarLevelTransport φ v p))
  · exact .of_forall fun n v hv => by
      rw [scalarTransportResponseExtension_eq β hβ.ne' s (μn n) φ L hφ h0 h1 δ hδ hsmall p v
        ⟨hv.1.le,hv.2.le⟩]
      have hd := hasDerivAt_scalarTransportGamma_finite_at (parisiGridRSBScheme μ n)
        β hβ φ L hφ h0 h1 s hs
        (by rw [parisiSchemeMeasure_grid_eq];exact parisiGridMeasure_mem_scalarFloor μ s hμ n)
        v ((mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hv.1.le,hv.2.le⟩) L.coe_nonneg).trans_lt hsmall) p
      simpa only [parisiSchemeMeasure_grid_eq,μn] using hd
  · intro v hv
    have hmap := ((continuous_scalarTransportMeasure φ).comp
      (continuous_id.prodMk (continuous_const (y:=v)))).tendsto μ |>.comp (tendsto_parisiGridMeasure μ)
    exact ((continuous_scalarGamma_parameter β hβ.ne').comp
      (continuous_id.prodMk (continuous_const (y:=scalarLevelTransport φ v p)))).tendsto (scalarTransportMeasure μ φ v) |>.comp hmap
  · exact hu

 theorem scalar_general_response_identity (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0) (hφ : LipschitzWith L φ)
    (h0 : φ 0=0) (h1 : φ 1=0) (δ : ℝ) (hδ : 0<δ) (hsmall : δ*L<1)
    (p : Paper.Overlap) :
    ContDiffOn ℝ 1 (fun v=>Gamma β (scalarTransportMeasure μ φ v)
      (scalarLevelTransport φ v p)) (Ioo (-δ) δ) ∧
    HasDerivAt (fun v=>Gamma β (scalarTransportMeasure μ φ v) (scalarLevelTransport φ v p))
      (scalarResponseOperator β hβ.ne' μ s φ p) 0 := by
  have hder := hasDerivAt_scalarTransportGamma_general_at β hβ μ s hs hμ φ L hφ h0 h1
    δ hδ hsmall p
  constructor
  · rw [show (1 : ℕ∞ω)=0+1 from rfl,contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun u hu => (hder u hu).differentiableAt.differentiableWithinAt,?_,?_⟩
    · simp
    · apply contDiffOn_zero.mpr
      apply (continuous_scalarTransportResponseExtension β hβ.ne' s hs ⟨μ,hμ⟩
        φ L hφ h0 h1 δ hδ hsmall p).continuousOn.congr
      intro u hu
      exact (hder u hu).deriv
  · have hz : (0:ℝ)∈Ioo (-δ) δ := ⟨by linarith,hδ⟩
    have hd := hder 0 hz
    apply hd.congr_deriv
    rw [scalarTransportResponseExtension_eq β hβ.ne' s ⟨μ,hμ⟩ φ L hφ h0 h1
      δ hδ hsmall p 0 ⟨hz.1.le,hz.2.le⟩,
      scalarTransportMeasure_zero,scalarLevelTransport_zero]
    congr 1
    ext q
    simpa only [scalarLevelTransport_zero] using
      scalarRelabelledDirection_transport φ φ L hφ h0 h1 0 (by simp) q

 theorem scalar_general_response_smooth_test (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (f : ℝ→ℝ) (hf : ContDiffOn ℝ ∞ f (Icc (0:ℝ) 1)) (h0 : f 0=0) (h1 : f 1=0) :
    ∃δ : ℝ,0<δ ∧ ∀p : Paper.Overlap,
      ContDiffOn ℝ 1 (fun v=>Gamma β
        (scalarTransportMeasure μ (scalarSmoothTransportTest f hf) v)
        (scalarLevelTransport (scalarSmoothTransportTest f hf) v p)) (Ioo (-δ) δ) ∧
      HasDerivAt (fun v=>Gamma β
        (scalarTransportMeasure μ (scalarSmoothTransportTest f hf) v)
        (scalarLevelTransport (scalarSmoothTransportTest f hf) v p))
        (scalarResponseOperator β hβ.ne' μ s (scalarSmoothTransportTest f hf) p) 0 := by
  obtain ⟨L,hL⟩ := hf.exists_lipschitzOnWith (by simp : (∞ : ℕ∞ω)≠0)
    (convex_Icc 0 1) isCompact_Icc
  have hφ : LipschitzWith L (scalarSmoothTransportTest f hf) := by
    apply LipschitzWith.of_dist_le_mul
    intro q r
    exact hL.dist_le_mul q q.property r r.property
  let δ : ℝ := 1/(2*((L:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  have hsmall : δ*L<1 := by
    dsimp [δ]
    rw [div_mul_eq_mul_div,one_mul]
    apply (div_lt_iff₀ (by positivity : 0<2*((L:ℝ)+1))).mpr
    linarith [L.coe_nonneg]
  refine ⟨δ,hδ,fun p => ?_⟩
  exact scalar_general_response_identity β hβ μ s hs hμ (scalarSmoothTransportTest f hf)
    L hφ h0 h1 δ hδ hsmall p

end HexagonPaper
