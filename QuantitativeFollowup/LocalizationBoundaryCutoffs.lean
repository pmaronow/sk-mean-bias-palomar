module
public import QuantitativeFollowup.LocalizationLayercake
public import FourPapersCommon.SignedTrianglePairing
public import FourPapersCommon.OneSidedBoundaryCover

@[expose] public section

/-! Actual middle-half triangular cutoffs for the boundary level sets.
Their endpoints are extracted from the discrepancy, and their compact
support, sign, mass, and Dirichlet energy are proved for the explicit
functions. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

def middleHalfCutoff (a b : ℝ) : ℝ → ℝ :=
  FourPapersCommon.finiteTriangleCutoff {0} (fun _ => a+(b-a)/4) ((b-a)/2)

theorem middleHalfCutoff_properties (a b : ℝ) (hab : a<b) (ha : 0≤a) (hb : b≤1) :
    HasCompactSupport (middleHalfCutoff a b) ∧
      tsupport (middleHalfCutoff a b) ⊆ Ioo a b ∧
      (∀x, 0≤middleHalfCutoff a b x ∧ middleHalfCutoff a b x≤1) ∧
      (∫x in (0 : ℝ)..1, middleHalfCutoff a b x)=(b-a)/4 ∧
      (∫x in (0 : ℝ)..1, (deriv (middleHalfCutoff a b) x)^2)=8/(b-a) := by
  let S : Finset ℕ := {0}
  let start : ℕ → ℝ := fun _ => a+(b-a)/4
  let ell := (b-a)/2
  have hell : 0<ell := by dsimp only [ell]; linarith
  have hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (start i) (start i+ell)) := by
    simp only [S,Finset.coe_singleton]
    exact Set.pairwiseDisjoint_singleton _ _
  have hstart : ∀i∈S, 0≤start i := by intro i hi; dsimp only [start]; linarith
  have hend : ∀i∈S, start i+ell≤1 := by intro i hi; dsimp only [start,ell]; linarith
  have hmid : ∀i∈S, Icc (start i) (start i+ell)⊆Ioo a b := by
    intro i hi x hx
    dsimp only [start,ell] at hx
    constructor <;> linarith [hx.1,hx.2]
  refine ⟨FourPapersCommon.finiteTriangleCutoff_hasCompactSupport S start ell hell,
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp
      (FourPapersCommon.finiteTriangleCutoff_tsupport_subset S start ell hell hx)
    obtain ⟨his,hxi⟩ := mem_iUnion.mp hi
    exact hmid i his hxi
  · intro x
    exact ⟨FourPapersCommon.finiteTriangleCutoff_nonneg S start ell x,
      FourPapersCommon.finiteTriangleCutoff_le_one S start ell hell hdisj x⟩
  · have hh := FourPapersCommon.finiteTriangleCutoff_integral_unit S start ell hell hstart hend
    calc
      _ = (S.card : ℝ)*ell/2 := hh
      _ = (b-a)/4 := by simp only [S,Finset.card_singleton,Nat.cast_one,one_mul,ell]; ring
  · have hh := FourPapersCommon.finiteTriangleCutoff_energy_unit S start ell hell hstart hend hdisj
    calc
      _ = 4*(S.card : ℝ)/ell := hh
      _ = 8/(b-a) := by simp only [S,Finset.card_singleton,Nat.cast_one,ell]; field_simp; norm_num

theorem negative_boundary_cutoff (psi : ℝ → ℝ) (q L A : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1) (hL : 0<L) (hA : 0<A)
    (hslope : ∀z x : ℝ, 0≤z → z≤x → x<q → psi x-psi z≤L*(x-z))
    (hm : 0<localizationLevelMass psi q L A 2) :
    ∃a∈Ico (0 : ℝ) q,
      localizationLevelMass psi q L A 2≤q-a ∧ q-a≤A/(2*L) ∧
      HasCompactSupport (middleHalfCutoff a q) ∧
      tsupport (middleHalfCutoff a q)⊆Ioo (0 : ℝ) q ∧
      (∀x∈tsupport (middleHalfCutoff a q), psi x≤ -A/2) ∧
      (∫x in (0 : ℝ)..1, middleHalfCutoff a q x)=(q-a)/4 ∧
      (∫x in (0 : ℝ)..1, (deriv (middleHalfCutoff a q) x)^2)=8/(q-a) := by
  have hm' : 0<volume.real {x : ℝ | x∈Ioo (0 : ℝ) q ∧ q-A/(2*L)≤x ∧ psi x < -A} := by
    simpa [localizationLevelMass,localizationLevelSet] using hm
  have hne : {x : ℝ | x∈Ioo (0 : ℝ) q ∧ q-A/(2*L)≤x ∧ psi x < -A}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h,measureReal_empty] at hm'
    exact lt_irrefl _ hm'
  obtain ⟨a,ha,hsub,hwidth,hcap,hsign⟩ :=
    FourPapersCommon.one_sided_negative_boundary_interval psi q L A hL hA hslope hne
  have hp := middleHalfCutoff_properties a q ha.2 ha.1 hq.2.le
  have hsupport : tsupport (middleHalfCutoff a q)⊆Ioo (0 : ℝ) q :=
    fun x hx => ⟨ha.1.trans_lt (hp.2.1 hx).1,(hp.2.1 hx).2⟩
  refine ⟨a,ha,?_,hcap,hp.1,hsupport,?_,hp.2.2.2.1,hp.2.2.2.2⟩
  · simpa [localizationLevelMass,localizationLevelSet] using hwidth
  · intro x hx
    exact (hsign x (hp.2.1 hx)).le

theorem positive_boundary_cutoff (psi : ℝ → ℝ) (q L A : ℝ)
    (hq : q∈Ioo (0 : ℝ) 1)
    (hanti : AntitoneOn psi (Icc q 1))
    (hm : 0<localizationLevelMass psi q L A 3) :
    ∃b∈Ioc q 1,
      localizationLevelMass psi q L A 3=b-q ∧ b-q≤1 ∧
      HasCompactSupport (middleHalfCutoff q b) ∧
      tsupport (middleHalfCutoff q b)⊆Ioo q 1 ∧
      (∀x∈tsupport (middleHalfCutoff q b), A<psi x) ∧
      (∫x in (0 : ℝ)..1, middleHalfCutoff q b x)=(b-q)/4 ∧
      (∫x in (0 : ℝ)..1, (deriv (middleHalfCutoff q b) x)^2)=8/(b-q) := by
  have hm' : 0<volume.real {x : ℝ | x∈Icc q 1 ∧ A<psi x} := by
    simpa [localizationLevelMass,localizationLevelSet] using hm
  have hne : {x : ℝ | x∈Icc q 1 ∧ A<psi x}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h,measureReal_empty] at hm'
    exact lt_irrefl _ hm'
  obtain ⟨b,hb,hsub,hwidth,hsign⟩ :=
    FourPapersCommon.antitone_positive_boundary_interval psi q A hanti hne
  have hqb : q<b := by linarith
  have hp := middleHalfCutoff_properties q b hqb hq.1.le hb.2
  have hsupport : tsupport (middleHalfCutoff q b)⊆Ioo q 1 :=
    fun x hx => ⟨(hp.2.1 hx).1,(hp.2.1 hx).2.trans_le hb.2⟩
  refine ⟨b,⟨hqb,hb.2⟩,?_,by linarith [hb.2,hq.1],hp.1,hsupport,?_,hp.2.2.2.1,hp.2.2.2.2⟩
  · simpa [localizationLevelMass,localizationLevelSet] using hwidth
  · intro x hx
    exact hsign x (hp.2.1 hx)

end QuantitativeFollowup
