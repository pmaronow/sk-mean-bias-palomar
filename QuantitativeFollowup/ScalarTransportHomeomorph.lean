module
public import QuantitativeFollowup.ScalarTransportContinuity
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-! Small endpoint-fixed scalar level transports are genuine homeomorphisms.
Their inverse is Lipschitz, so a second transport direction can be relabelled
at a moved finite profile without changing its actual physical node values. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem scalarLevelTransport_one (φ : C(Paper.Overlap,ℝ)) (h1 : φ 1=0) (u : ℝ) :
    scalarLevelTransport φ u 1=1 := by
  apply Subtype.ext
  simp only [scalarLevelTransport,h1,mul_zero,add_zero]
  change (projIcc 0 1 zero_le_one (1:ℝ):ℝ)=1
  rw [projIcc_of_mem zero_le_one (by constructor <;> norm_num : (1:ℝ)∈Icc 0 1)]

theorem surjective_scalarLevelTransport (φ : C(Paper.Overlap,ℝ))
    (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ) :
    Function.Surjective (scalarLevelTransport φ u) := by
  intro q
  have hI := intermediate_value_Icc (a:=(0:Paper.Overlap)) (b:=1)
    (by norm_num : (0:Paper.Overlap)≤1)
    (continuous_scalarLevelTransport_parameter φ u).continuousOn
  rw [scalarLevelTransport_root φ h0 u,scalarLevelTransport_one φ h1 u] at hI
  obtain ⟨p,_,hp⟩ := hI ⟨q.property.1,q.property.2⟩
  exact ⟨p,hp⟩

def scalarLevelHomeomorph (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ)
    (hu : |u| *L<1) : Paper.Overlap ≃ₜ Paper.Overlap :=
  (Equiv.ofBijective (scalarLevelTransport φ u)
    ⟨(strictMono_scalarLevelTransport φ L hφ h0 h1 u hu).injective,
      surjective_scalarLevelTransport φ h0 h1 u⟩).toHomeomorphOfContinuousClosed
        (continuous_scalarLevelTransport_parameter φ u)
        (continuous_scalarLevelTransport_parameter φ u).isClosedMap

@[simp] theorem scalarLevelHomeomorph_apply (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ)
    (hu : |u| *L<1) (q : Paper.Overlap) :
    scalarLevelHomeomorph φ L hφ h0 h1 u hu q=scalarLevelTransport φ u q := rfl

theorem scalarLevelTransport_inverse_dist_bound (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ)
    (hu : |u| *L<1) (p q : Paper.Overlap) :
    (1-|u| *L)*dist p q≤dist (scalarLevelTransport φ u p) (scalarLevelTransport φ u q) := by
  have hd := hφ.dist_le_mul p q
  change |φ p-φ q|≤(L:ℝ)*|(p:ℝ)-q| at hd
  have he : |u*(φ p-φ q)|≤|u| *L*|(p:ℝ)-q| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hd (abs_nonneg u)).trans_eq (by ring)
  change (1-|u| *L)*|(p:ℝ)-q|≤
    |(scalarLevelTransport φ u p:ℝ)-scalarLevelTransport φ u q|
  rw [scalarLevelTransport_eq_affine φ L hφ h0 h1 u hu.le,
    scalarLevelTransport_eq_affine φ L hφ h0 h1 u hu.le]
  have ht := norm_sub_le ((p:ℝ)+u*φ p-((q:ℝ)+u*φ q)) (u*(φ p-φ q))
  simp only [Real.norm_eq_abs] at ht
  have hc : (p:ℝ)+u*φ p-((q:ℝ)+u*φ q)-u*(φ p-φ q)=(p:ℝ)-q := by ring
  rw [hc] at ht
  linarith

theorem lipschitzWith_scalarLevelHomeomorph_symm (φ : C(Paper.Overlap,ℝ)) (L : ℝ≥0)
    (hφ : LipschitzWith L φ) (h0 : φ 0=0) (h1 : φ 1=0) (u : ℝ)
    (hu : |u| *L<1) :
    LipschitzWith (⟨(1-|u| *L)⁻¹,inv_nonneg.mpr (by linarith)⟩ : ℝ≥0)
      (scalarLevelHomeomorph φ L hφ h0 h1 u hu).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hp := scalarLevelTransport_inverse_dist_bound φ L hφ h0 h1 u hu
    ((scalarLevelHomeomorph φ L hφ h0 h1 u hu).symm p)
    ((scalarLevelHomeomorph φ L hφ h0 h1 u hu).symm q)
  let e := scalarLevelHomeomorph φ L hφ h0 h1 u hu
  change (1-|u| *L)*dist (e.symm p) (e.symm q)≤dist (e (e.symm p)) (e (e.symm q)) at hp
  rw [e.apply_symm_apply,e.apply_symm_apply] at hp
  change dist _ _≤(1-|u| *L)⁻¹*dist p q
  have hpos : 0<1-|u| *L := by linarith
  calc
    _=((1-|u| *L)⁻¹*(1-|u| *L))*dist _ _ := by rw [inv_mul_cancel₀ (ne_of_gt hpos),one_mul]
    _≤(1-|u| *L)⁻¹*dist p q := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hpos.le)

def scalarRelabelledDirection (φ ψ : C(Paper.Overlap,ℝ)) (Lψ : ℝ≥0)
    (hψ : LipschitzWith Lψ ψ) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0)
    (u : ℝ) (hu : |u| *Lψ<1) : C(Paper.Overlap,ℝ) :=
  φ.comp ⟨(scalarLevelHomeomorph ψ Lψ hψ hψ0 hψ1 u hu).symm,
    (scalarLevelHomeomorph ψ Lψ hψ hψ0 hψ1 u hu).symm.continuous⟩

theorem lipschitzWith_scalarRelabelledDirection (φ ψ : C(Paper.Overlap,ℝ))
    (Lφ Lψ : ℝ≥0) (hφ : LipschitzWith Lφ φ) (hψ : LipschitzWith Lψ ψ)
    (hψ0 : ψ 0=0) (hψ1 : ψ 1=0) (u : ℝ) (hu : |u| *Lψ<1) :
    LipschitzWith (Lφ*Real.toNNReal ((1-|u| *Lψ)⁻¹))
      (scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu) := by
  have hi := lipschitzWith_scalarLevelHomeomorph_symm ψ Lψ hψ hψ0 hψ1 u hu
  have hnon : 0≤(1-|u| *Lψ)⁻¹ := inv_nonneg.mpr (by linarith)
  have he : (⟨(1-|u| *Lψ)⁻¹,hnon⟩ : ℝ≥0)=Real.toNNReal ((1-|u| *Lψ)⁻¹) := by
    exact Subtype.ext (Real.coe_toNNReal _ hnon).symm
  rw [he] at hi
  exact hφ.comp hi

@[simp] theorem scalarRelabelledDirection_transport (φ ψ : C(Paper.Overlap,ℝ)) (Lψ : ℝ≥0)
    (hψ : LipschitzWith Lψ ψ) (hψ0 : ψ 0=0) (hψ1 : ψ 1=0)
    (u : ℝ) (hu : |u| *Lψ<1) (q : Paper.Overlap) :
    scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu (scalarLevelTransport ψ u q)=φ q := by
  change φ ((scalarLevelHomeomorph ψ Lψ hψ hψ0 hψ1 u hu).symm
    ((scalarLevelHomeomorph ψ Lψ hψ hψ0 hψ1 u hu) q))=φ q
  rw [Homeomorph.symm_apply_apply]

theorem scalarRelabelledDirection_endpoints (φ ψ : C(Paper.Overlap,ℝ)) (Lψ : ℝ≥0)
    (hψ : LipschitzWith Lψ ψ) (hφ0 : φ 0=0) (hφ1 : φ 1=0)
    (hψ0 : ψ 0=0) (hψ1 : ψ 1=0) (u : ℝ) (hu : |u| *Lψ<1) :
    scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu 0=0 ∧
      scalarRelabelledDirection φ ψ Lψ hψ hψ0 hψ1 u hu 1=0 := by
  constructor
  · rw [←scalarLevelTransport_root ψ hψ0 u,scalarRelabelledDirection_transport,hφ0]
  · rw [←scalarLevelTransport_one ψ hψ1 u,scalarRelabelledDirection_transport,hφ1]

end QuantitativeFollowup
