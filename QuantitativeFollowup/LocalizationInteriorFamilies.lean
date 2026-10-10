module
public import QuantitativeFollowup.LocalizationLayercake
public import FourPapersCommon.FiniteTriangleSupport

@[expose] public section

/-! The actual two interior families used in localization. The cells
are those meeting the actual level set; their shifted intervals have the
required sign, disjointness, support, and measure cover. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem positive_localization_family (psi : ℝ → ℝ) (q L A : ℝ)
    (hL : 0<L) (hA : 0<A) (hroot : psi 0≤0)
    (hslope : ∀z x : ℝ, 0≤z → z≤x → x<q → psi x-psi z≤L*(x-z)) :
    let ell := A/(4*L)
    let S := FourPapersCommon.gridCellsMeeting q ell (localizationLevelSet psi q L A 0)
    let start := fun i : ℕ => ((i : ℝ)-1)*ell
    localizationLevelMass psi q L A 0≤(S.card : ℝ)*ell ∧
      (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (start i) (start i+ell)) ∧
      (∀i∈S, Icc (start i) (start i+ell)⊆Ioo (0 : ℝ) q) ∧
      (∀i∈S, ∀x∈Icc (start i) (start i+ell), A/2≤psi x) ∧
      HasCompactSupport (FourPapersCommon.finiteTriangleCutoff S start ell) ∧
      tsupport (FourPapersCommon.finiteTriangleCutoff S start ell)⊆Ioo (0 : ℝ) q := by
  dsimp only
  let ell := A/(4*L)
  let D := localizationLevelSet psi q L A 0
  let S := FourPapersCommon.gridCellsMeeting q ell D
  let start := fun i : ℕ => ((i : ℝ)-1)*ell
  have hell : 0<ell := by dsimp only [ell]; positivity
  have he (i : ℕ) : start i+ell=(i : ℝ)*ell := by dsimp only [start]; ring
  have hD : D={x : ℝ | x∈Ioo (0 : ℝ) q ∧ A<psi x} := by simp only [D,localizationLevelSet,Fin.isValue,ite_true]
  have hinside : ∀i∈S, Icc (start i) (start i+ell)⊆Ioo (0 : ℝ) q := by
    intro i hi
    rw [he]
    apply (FourPapersCommon.one_sided_positive_predecessors psi q L A hL hA hroot hslope i ?_).2.1
    simpa only [S,hD] using hi
  have hsign : ∀i∈S, ∀x∈Icc (start i) (start i+ell), A/2≤psi x := by
    intro i hi x hx
    rw [he] at hx
    exact (FourPapersCommon.one_sided_positive_predecessors psi q L A hL hA hroot hslope i
      (by simpa only [S,hD] using hi)).2.2 x hx |>.le
  have hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (start i) (start i+ell)) := by
    intro i hi j hj hij
    have hh := FourPapersCommon.shifted_grid_intervals_pairwiseDisjoint ell (-1) hell hij
    have hright (z : ℕ) : (((z : ℝ)+(-1)+1)*ell)=(z : ℝ)*ell := by ring
    change Disjoint (Ioo (start i) (start i+ell)) (Ioo (start j) (start j+ell))
    rw [he,he]
    simpa only [start,hright,sub_eq_add_neg] using hh
  refine ⟨?_,hdisj,hinside,hsign,
    FourPapersCommon.finiteTriangleCutoff_hasCompactSupport S start ell hell,
    FourPapersCommon.finiteTriangleCutoff_tsupport_inside S start ell q hell hinside⟩
  exact FourPapersCommon.gridCellsMeeting_measure_bound q ell D hell
    (by intro x hx; rw [hD] at hx; exact ⟨hx.1.1.le,hx.1.2.le⟩)

theorem negative_localization_family (psi : ℝ → ℝ) (q L A : ℝ)
    (hL : 0<L) (hA : 0<A)
    (hslope : ∀z x : ℝ, 0≤z → z≤x → x<q → psi x-psi z≤L*(x-z)) :
    let ell := A/(4*L)
    let S := FourPapersCommon.gridCellsMeeting q ell (localizationLevelSet psi q L A 1)
    let start := fun i : ℕ => ((i : ℝ)+1)*ell
    localizationLevelMass psi q L A 1≤(S.card : ℝ)*ell ∧
      (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (start i) (start i+ell)) ∧
      (∀i∈S, Icc (start i) (start i+ell)⊆Ioo (0 : ℝ) q) ∧
      (∀i∈S, ∀x∈Icc (start i) (start i+ell), psi x≤ -A/2) ∧
      HasCompactSupport (FourPapersCommon.finiteTriangleCutoff S start ell) ∧
      tsupport (FourPapersCommon.finiteTriangleCutoff S start ell)⊆Ioo (0 : ℝ) q := by
  dsimp only
  let ell := A/(4*L)
  let D := localizationLevelSet psi q L A 1
  let S := FourPapersCommon.gridCellsMeeting q ell D
  let start := fun i : ℕ => ((i : ℝ)+1)*ell
  have hell : 0<ell := by dsimp only [ell]; positivity
  have he (i : ℕ) : start i+ell=((i : ℝ)+2)*ell := by dsimp only [start]; ring
  have hcut : q-A/(2*L)=q-2*ell := by dsimp only [ell]; ring
  have hD : D={x : ℝ | x∈Ioo (0 : ℝ) (q-2*ell) ∧ psi x < -A} := by
    simp [D,localizationLevelSet,hcut]
  have hinside : ∀i∈S, Icc (start i) (start i+ell)⊆Ioo (0 : ℝ) q := by
    intro i hi
    rw [he]
    apply (FourPapersCommon.one_sided_negative_successors psi q L A hL hA hslope i ?_).1
    simpa only [S,hD] using hi
  have hsign : ∀i∈S, ∀x∈Icc (start i) (start i+ell), psi x≤ -A/2 := by
    intro i hi x hx
    rw [he] at hx
    exact (FourPapersCommon.one_sided_negative_successors psi q L A hL hA hslope i
      (by simpa only [S,hD] using hi)).2 x hx |>.le
  have hdisj : (S : Set ℕ).PairwiseDisjoint (fun i => Ioo (start i) (start i+ell)) := by
    intro i hi j hj hij
    have hh := FourPapersCommon.shifted_grid_intervals_pairwiseDisjoint ell 1 hell hij
    have hright (z : ℕ) : (((z : ℝ)+1+1)*ell)=((z : ℝ)+2)*ell := by ring
    change Disjoint (Ioo (start i) (start i+ell)) (Ioo (start j) (start j+ell))
    rw [he,he]
    simpa only [start,hright] using hh
  refine ⟨?_,hdisj,hinside,hsign,
    FourPapersCommon.finiteTriangleCutoff_hasCompactSupport S start ell hell,
    FourPapersCommon.finiteTriangleCutoff_tsupport_inside S start ell q hell hinside⟩
  exact FourPapersCommon.gridCellsMeeting_measure_bound q ell D hell
    (by
      intro x hx
      rw [hD] at hx
      exact ⟨hx.1.1.le,by linarith [hx.1.2]⟩)

end QuantitativeFollowup
