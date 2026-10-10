module
public import QuantitativePaper.ResponseTentDerivative

@[expose] public section

/-! Genuine tent subdivision of an arbitrary closed cell. Clamping keeps
zero-length pieces, so repeated scheme nodes need no exceptions. -/
noncomputable section
open Set Filter
namespace QuantitativePaper
set_option maxHeartbeats 1200000

def responseCellClamp (a b x : ℝ) : ℝ:=max a (min b x)
def responseTentCellNode (ell a b : ℝ) (j : ℕ) : ℝ:=
  if j=0 then a else if j=1 then responseCellClamp a b (ell/4)
  else if j=2 then responseCellClamp a b (ell/2)
  else if j=3 then responseCellClamp a b (3*ell/4) else b
def responseTentCellAlpha (j : ℕ) : ℝ:=if j=1 then -1 else if j=2 then 3 else 0
def responseTentCellDelta (ell : ℝ) (j : ℕ) : ℝ:=
  if j=1 then 4/ell else if j=2 then -(4/ell) else 0

theorem responseCellClamp_mem (a b x : ℝ) (hab : a≤b) :
    responseCellClamp a b x∈Icc a b:=by
  exact ⟨le_max_left _ _,max_le hab (min_le_left _ _)⟩

theorem responseCellClamp_mono (a b : ℝ) : Monotone (responseCellClamp a b):=by
  intro x y hxy
  exact max_le_max_left _ (min_le_min_left _ hxy)

theorem responseCellClamp_le_argument {a b x : ℝ} (h : a<responseCellClamp a b x) :
    responseCellClamp a b x≤x:=by
  unfold responseCellClamp at *
  have hm : a≤min b x:=((lt_max_iff.mp h).resolve_left (lt_irrefl a)).le
  rw [max_eq_right hm]
  exact min_le_right _ _

theorem responseCellClamp_argument_le {a b x : ℝ} (hab : a≤b)
    (h : responseCellClamp a b x<b) : x≤responseCellClamp a b x:=by
  unfold responseCellClamp at *
  have hxb : x≤b:=by
    by_contra hx
    rw [min_eq_left (le_of_lt (lt_of_not_ge hx)),max_eq_right hab] at h
    exact lt_irrefl b h
  rw [min_eq_right hxb]
  exact le_max_right _ _

theorem responseTentCellNode_zero (ell a b : ℝ) : responseTentCellNode ell a b 0=a:=by
  simp [responseTentCellNode]
theorem responseTentCellNode_four (ell a b : ℝ) : responseTentCellNode ell a b 4=b:=by
  norm_num [responseTentCellNode]

theorem responseTentCellNode_mem (ell a b : ℝ) (hab : a≤b)
    (j : ℕ) (hj : j≤4) : responseTentCellNode ell a b j∈Icc a b:=by
  interval_cases j
  · simp [responseTentCellNode,hab]
  · simpa [responseTentCellNode] using responseCellClamp_mem a b (ell/4) hab
  · simpa [responseTentCellNode] using responseCellClamp_mem a b (ell/2) hab
  · simpa [responseTentCellNode] using responseCellClamp_mem a b (3*ell/4) hab
  · simp [responseTentCellNode,hab]

theorem responseTentCellNode_step (ell a b : ℝ) (hell : 0<ell) (hab : a≤b)
    (j : ℕ) (hj : j<4) : responseTentCellNode ell a b j≤responseTentCellNode ell a b (j+1):=by
  interval_cases j
  · simpa [responseTentCellNode] using (responseCellClamp_mem a b (ell/4) hab).1
  · simpa [responseTentCellNode] using responseCellClamp_mono a b (by linarith : ell/4≤ell/2)
  · simpa [responseTentCellNode] using responseCellClamp_mono a b (by linarith : ell/2≤3*ell/4)
  · simpa [responseTentCellNode] using (responseCellClamp_mem a b (3*ell/4) hab).2

theorem responseTentCell_piece (ell a b : ℝ) (hell : 0<ell) (hab : a≤b)
    (j : ℕ) (hj : j<4)
    (hlt : responseTentCellNode ell a b j<responseTentCellNode ell a b (j+1))
    (q : ℝ) (hq : q∈Icc (responseTentCellNode ell a b j) (responseTentCellNode ell a b (j+1))) :
    responseTent ell q=responseTentCellAlpha j+responseTentCellDelta ell j*q:=by
  interval_cases j
  · simp only [responseTentCellNode,if_pos,if_neg,show (1:ℕ)≠0 by decide] at hlt hq
    have hq1 : q≤ell/4:=hq.2.trans (responseCellClamp_le_argument hlt)
    simpa [responseTentCellAlpha,responseTentCellDelta] using responseTent_zero_left hell hq1
  · norm_num [responseTentCellNode] at hlt hq
    have hlow : ell/4≤responseCellClamp a b (ell/4):=responseCellClamp_argument_le hab
      (hlt.trans_le (responseCellClamp_mem a b (ell/2) hab).2)
    have hupp : responseCellClamp a b (ell/2)≤ell/2:=responseCellClamp_le_argument
      ((responseCellClamp_mem a b (ell/4) hab).1.trans_lt hlt)
    rw [responseTent_left_formula hell ⟨hlow.trans hq.1,hq.2.trans hupp⟩]
    simp only [responseTentCellAlpha,responseTentCellDelta,if_pos,show (1:ℕ)≠2 by decide,if_neg]
    ring
  · norm_num [responseTentCellNode] at hlt hq
    have hlow : ell/2≤responseCellClamp a b (ell/2):=responseCellClamp_argument_le hab
      (hlt.trans_le (responseCellClamp_mem a b (3*ell/4) hab).2)
    have hupp : responseCellClamp a b (3*ell/4)≤3*ell/4:=responseCellClamp_le_argument
      ((responseCellClamp_mem a b (ell/2) hab).1.trans_lt hlt)
    rw [responseTent_right_formula hell ⟨hlow.trans hq.1,hq.2.trans hupp⟩]
    norm_num [responseTentCellAlpha,responseTentCellDelta]
    ring
  · norm_num [responseTentCellNode] at hlt hq
    have hq1 : 3*ell/4≤q:=(responseCellClamp_argument_le hab hlt).trans hq.1
    simpa [responseTentCellAlpha,responseTentCellDelta] using responseTent_zero_right hell hq1

theorem hasDerivAt_responseTentCell_piece (ell a b : ℝ) (hell : 0<ell) (hab : a≤b)
    (j : ℕ) (hj : j<4) (q : ℝ)
    (hq : q∈Ioo (responseTentCellNode ell a b j) (responseTentCellNode ell a b (j+1))) :
    HasDerivAt (responseTent ell) (responseTentCellDelta ell j) q:=by
  have hh:=((hasDerivAt_id q).const_mul (responseTentCellDelta ell j)).const_add (responseTentCellAlpha j)
  simp only [mul_one] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hq.1,eventually_lt_nhds hq.2] with x hx hy
  exact responseTentCell_piece ell a b hell hab j hj (hq.1.trans hq.2) x ⟨hx.le,hy.le⟩

end QuantitativePaper
