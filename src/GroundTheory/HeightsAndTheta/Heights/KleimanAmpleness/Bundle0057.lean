module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsSumEqOneOfMulEqOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellLocSys
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def cellLocSys {S : Type} [CommRing S] {X : Type} {Ω : Type} [Field Ω] [Algebra S Ω] (G : X → Submodule S Ω)
    (f : Ω) : X → Submodule S Ω :=
  fun I => ⨆ n : ℕ, (G I).comap (LinearMap.mulLeft S (f ^ n))

def CellLocGlue.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (G : (∀ k, Finset (ι k)) → Submodule S Ω) (R : Subring Ω) (m : ℕ) (f u : Fin m → Ω),
    (∀ l, f l ∈ R) → (∀ l, u l ∈ R) → ∑ l, u l * f l = 1 →
    (∀ I, ∀ r ∈ R, ∀ a ∈ G I, r * a ∈ G I) →
    (∀ l, CellPosExact S y (cellLocSys G (f l))) →
    CellPosExact S y G

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeetsBaseCell
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

variable {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] [Algebra S Ω]

theorem cellSec_mono [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (γ : K → ℤ) {I I' : ∀ k, Finset (ι k)} (h : ∀ k, I k ⊆ I' k)
    (hI' : CellMeets y I') : cellSec S y γ I ≤ cellSec S y γ I' := by
  classical
  unfold cellSec
  rw [if_pos hI']
  split_ifs with hI
  · refine Submodule.span_mono ?_
    rintro z ⟨g, t, a, ht, hta, hγ, hg, rfl⟩
    refine ⟨g, t, a, ?_, hta, hγ, hg, rfl⟩
    refine Submonoid.closure_mono ?_ ht
    rintro f ⟨k, i, hi, rfl⟩
    exact ⟨k, i, h k hi, rfl⟩
  · exact bot_le

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem subset_baseCell (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (J : Finset (Fin (N + 1)))
    (I : ∀ k, Finset (ι k)) (k : K) : I k ⊆ baseCell k₀ e J I k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self]; exact Finset.subset_union_left
  · rw [Function.update_of_ne hk]

theorem baseCell_mono (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) {J J' : Finset (Fin (N + 1))}
    {I I' : ∀ k, Finset (ι k)} (hJ : J ⊆ J') (hI : ∀ k, I k ⊆ I' k) (k : K) :
    baseCell k₀ e J I k ⊆ baseCell k₀ e J' I' k := by
  unfold baseCell
  by_cases hk : k = k₀
  · subst hk; rw [Function.update_self, Function.update_self]
    exact Finset.union_subset_union (hI k) (Finset.map_subset_map.mpr hJ)
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]; exact hI k

theorem cellMeets_baseCell (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) :
    CellMeets y (baseCell k₀ e J.1 I) := by
  intro k i hi
  unfold baseCell at hi
  by_cases hk : k = k₀
  · subst hk
    rw [Function.update_self, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hI k i hi
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
      exact (Kleiman.mem_support _).mp (J.2.2 hj)
  · rw [Function.update_of_ne hk] at hi; exact hI k i hi

theorem ModelCechRefine.proof (hC : CechContract.Statement) (hR : ModelRowExact.Statement)
    (hD : DoubleCech.Statement) : ModelCechRefine.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ N e hM γ T hT n
  have hM0 : ∀ (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, ¬ CellMeets y I →
      cellSec F y γ (baseCell k₀ e J.1 I) = ⊥ := fun J I hI => by
    unfold cellSec
    rw [if_neg fun h => hI fun k i hi => h k i (subset_baseCell k₀ e J.1 I k hi)]
  have hMJ : ∀ (J J' : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) I, J.1 ⊆ J'.1 →
      cellSec F y γ (baseCell k₀ e J.1 I) ≤ cellSec F y γ (baseCell k₀ e J'.1 I) := fun J J' I h => by
    by_cases hI : CellMeets y I
    · exact cellSec_mono y γ (baseCell_mono k₀ e h fun _ => subset_rfl) (cellMeets_baseCell y k₀ e J' hI)
    · rw [hM0 J I hI]; exact bot_le
  refine (hD F K ι Ω y N _ T (cellSec F y γ) (fun J I => cellSec F y γ (baseCell k₀ e J.1 I)) hM.1 ?_
    (fun I hI => by unfold cellSec; rw [if_neg hI]) hM0 hMJ
    (fun J I I' h hI' => cellSec_mono y γ (baseCell_mono k₀ e subset_rfl h) (cellMeets_baseCell y k₀ e J hI'))
    ?_ ?_ n)
  · obtain ⟨i, hi⟩ := hM.1 k₀
    exact ⟨e i, by simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hi⟩
  · intro I hne hI
    obtain ⟨i, hi⟩ := hne k₀
    have hx : (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) (e i) ≠ 0 := by
      simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using hI k₀ i hi
    let J₀ : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm) :=
      ⟨{e i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr ((Kleiman.mem_support _).mpr hx)⟩
    have hadd : ∀ J : Finset (Fin (N + 1)), baseCell k₀ e ({e i} ∪ J) I = baseCell k₀ e J I := by
      intro J
      unfold baseCell
      congr 1
      rw [Finset.map_union, ← Finset.union_assoc, Finset.map_singleton]
      congr 1
      exact Finset.union_eq_left.mpr (Finset.singleton_subset_iff.mpr (by simpa using hi))
    have h₀ : baseCell k₀ e J₀.1 I = I := by
      have := hadd ∅
      rw [Finset.union_empty] at this
      rw [show J₀.1 = {e i} from rfl, this]
      unfold baseCell
      simp
    have := hC F Ω N _ (fun J => cellSec F y γ (baseCell k₀ e J.1 I)) J₀ (Finset.card_singleton _)
      (fun J J' h => hMJ J J' I h) (fun J J' h => by
        show cellSec F y γ (baseCell k₀ e J'.1 I) = _
        rw [h]; exact congrArg _ (hadd J.1))
    simpa only [h₀] using this
  · intro J
    have h := hR F K ι Ω y k₀ N e hM γ J
    rwa [← hT J, ← Submodule.coe_restrictScalars F, Submodule.span_eq] at h

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellMeetsPt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH

namespace CellZeroConst

variable {K : Type} [Fintype K] {ι : K → Type}

def pt (c : ∀ k, ι k) : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun _ => Finset.singleton_nonempty _, by simp⟩

theorem exists_pt (c : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0) : ∃ d : ∀ k, ι k, c = pt d := by
  have h1 : ∀ k, (c.1 k).card = 1 := by
    intro k
    have hk : (c.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp c.2.2) k (Finset.mem_univ _)
    have := (c.2.1 k).card_pos
    omega
  choose d hd using fun k => Finset.card_eq_one.mp (h1 k)
  exact ⟨d, Subtype.ext (funext hd)⟩

theorem cellMeets_pt {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    CellMeets y (pt c).1 ↔ ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  simp [CellMeets, pt]

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem edge (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d : ∀ k, ι k) (k : K)
    {i i' : ι k} (hii : i < i') (hd : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0) (hi : y ⟨k, i⟩ ≠ 0)
    (hi' : y ⟨k, i'⟩ ≠ 0) :
    s (pt (Function.update d k i)) = s (pt (Function.update d k i')) := by
  classical
  have hne : i ≠ i' := hii.ne
  obtain ⟨J, hJk, hJl⟩ : ∃ J : ∀ l, Finset (ι l), J k = {i, i'} ∧ ∀ l, l ≠ k → J l = {d l} :=
    ⟨Function.update (fun l => {d l}) k {i, i'}, by simp, fun l hl => by simp [hl]⟩
  have hJ1 : (∀ l, (J l).Nonempty) ∧ ∑ l, ((J l).card - 1) = 0 + 1 := by
    refine ⟨fun l => ?_, ?_⟩
    · by_cases hl : l = k
      · subst hl; simp [hJk]
      · simp [hJl l hl]
    · rw [Finset.sum_eq_single k (fun l _ hl => by simp [hJl l hl]) (by simp)]
      simp [hJk, Finset.card_pair hne]
  have hm : CellMeets y J := by
    intro l j hj
    by_cases hl : l = k
    · subst hl
      rw [hJk] at hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> assumption
    · rw [hJl l hl, Finset.mem_singleton] at hj
      subst hj
      exact hd l hl

  have hface : ∀ a b : ι k, J k = {a, b} → a ≠ b →
      Function.update J k ((J k).erase a) = (pt (Function.update d k b)).1 := by
    intro a b hab habn
    funext l
    by_cases hl : l = k
    · subst hl
      simp [pt, hab, habn]
    · simp [pt, hl, hJl l hl]
  have hfa := hface i i' hJk hne
  have hfb := hface i' i (by rw [hJk, Finset.pair_comm]) hne.symm
  have hlow : ∑ l ∈ Finset.univ.filter (· < k), ((J l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by
      rw [hJl l (ne_of_lt (Finset.mem_filter.mp hl).2)]
      simp
  have hsa : faceSign J k i = 1 := by
    unfold faceSign
    rw [hlow, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, not_lt_of_gt hii]
  have hsb : faceSign J k i' = -1 := by
    unfold faceSign
    rw [hlow, hJk]
    simp [Finset.filter_insert, Finset.filter_singleton, hii]
  have h0 : cellD S y 0 s ⟨J, hJ1⟩ = 0 := by rw [hs]; rfl
  unfold cellD at h0
  erw [LinearMap.pi_apply] at h0
  erw [if_pos (show CellMeets y J from hm)] at h0
  rw [LinearMap.sum_apply, Finset.sum_eq_single k] at h0
  rotate_left
  · intro l _ hl
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [dite_eq_right]
    · rfl
    rintro ⟨hn, -⟩
    have h2 := hn l
    rw [Function.update_self] at h2
    change j ∈ J l at hj
    rw [hJl l hl, Finset.mem_singleton] at hj
    subst hj
    change ((J l).erase (d l)).Nonempty at h2
    rw [hJl l hl] at h2
    simp at h2
  · simp
  rw [LinearMap.sum_apply, Finset.sum_eq_add i i' hne] at h0
  rotate_left
  · intro j hj hj2
    change j ∈ J k at hj
    rw [hJk] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact absurd rfl hj2.1
    · exact absurd rfl hj2.2
  · intro h; exact absurd (show i ∈ J k by rw [hJk]; simp) h
  · intro h; exact absurd (show i' ∈ J k by rw [hJk]; simp) h
  rw [dite_eq_left (hfa ▸ (pt (Function.update d k i')).2), dite_eq_left (hfb ▸ (pt (Function.update d k i)).2)] at h0
  simp only [LinearMap.smul_apply] at h0
  erw [LinearMap.proj_apply, LinearMap.proj_apply] at h0
  have e1 : ∀ h, s ⟨Function.update J k ((J k).erase i), h⟩ = s (pt (Function.update d k i')) :=
    fun _ => congrArg s (Subtype.ext hfa)
  have e2 : ∀ h, s ⟨Function.update J k ((J k).erase i'), h⟩ = s (pt (Function.update d k i)) :=
    fun _ => congrArg s (Subtype.ext hfb)
  rw [hsa, hsb, e1, e2, one_smul, neg_smul, one_smul] at h0
  linear_combination -h0

theorem step (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d : ∀ k, ι k)
    (hd : ∀ l, y ⟨l, d l⟩ ≠ 0) (k : K) (j : ι k) (hj : y ⟨k, j⟩ ≠ 0) :
    s (pt d) = s (pt (Function.update d k j)) := by
  classical
  have hdl : ∀ l, l ≠ k → y ⟨l, d l⟩ ≠ 0 := fun l _ => hd l
  rcases lt_trichotomy (d k) j with h | h | h
  · have := edge S y s hs d k h hdl (hd k) hj
    rwa [Function.update_eq_self] at this
  · rw [← h, Function.update_eq_self]
  · have := edge S y s hs d k h hdl hj (hd k)
    rw [Function.update_eq_self] at this
    exact this.symm

theorem chain (S : Type) [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
    (s : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι 0 → Ω) (hs : cellD S y 0 s = 0) (d d' : ∀ k, ι k)
    (hd : ∀ l, y ⟨l, d l⟩ ≠ 0) (hd' : ∀ l, y ⟨l, d' l⟩ ≠ 0) :
    s (pt d) = s (pt d') := by
  classical
  have key : ∀ T : Finset K, s (pt d) = s (pt (fun l => if l ∈ T then d' l else d l)) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · simp
    · intro a T ha ih
      rw [ih]
      have hmeet : ∀ l, y ⟨l, (fun l => if l ∈ T then d' l else d l) l⟩ ≠ 0 := fun l => by
        dsimp only
        split_ifs
        · exact hd' l
        · exact hd l
      rw [step S y s hs _ hmeet a (d' a) (hd' a)]
      congr 2
      funext l
      by_cases hl : l = a
      · subst hl
        simp
      · simp [hl]
  simpa using key Finset.univ

end CellZeroConst

theorem CellZeroConst.proof : CellZeroConst.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y s hs c c' hc hc'
  obtain ⟨d, rfl⟩ := CellZeroConst.exists_pt c
  obtain ⟨d', rfl⟩ := CellZeroConst.exists_pt c'
  rw [CellZeroConst.cellMeets_pt] at hc hc'
  exact CellZeroConst.chain S y s hs d d' hc hc'

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsFormDivOfMemChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver chartRingOver)

noncomputable section

theorem exists_form_div_of_mem_chartRing {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {i : Fin (N + 1)} (hi : x i ≠ 0) {a : Ω}
    (ha : a ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (e : ℕ) (f : Kleiman.Poly k N), f.IsHomogeneous e ∧ a = aeval x f / x i ^ e := by
  obtain ⟨f, t, e, ht, hf, hte, rfl⟩ := ha
  have ht' : t ∈ Submonoid.closure {(X i : Kleiman.Poly k N)} := by
    have : ((fun l => (X l : Kleiman.Poly k N)) '' ((({i} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X i} := by simp
    rw [← this]; exact ht
  obtain ⟨p, rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
  have hpe : e = p := hte.inj_right (isHomogeneous_X_pow i p) (by
    rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
  subst hpe
  exact ⟨e, f, hf, by rw [map_pow, aeval_X]⟩

theorem exists_common_form_div {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    {x : Fin (N + 1) → Ω} {ι : Type} [Fintype ι] {i : Fin (N + 1)} (hi : x i ≠ 0) (a : ι → Ω)
    (ha : ∀ t, a t ∈ Kleiman.chartRing k x (Kleiman.singleChart hi)) :
    ∃ (D : ℕ) (E : ι → Kleiman.Poly k N), (∀ t, (E t).IsHomogeneous D) ∧
      ∀ t, a t = aeval x (E t) / x i ^ D := by
  classical
  choose e f hf hfa using fun t => exists_form_div_of_mem_chartRing hi (ha t)
  have hle : ∀ t, e t ≤ ∑ t, e t := fun t =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  refine ⟨∑ t, e t, fun t => f t * X i ^ (∑ t, e t - e t), fun t => ?_, fun t => ?_⟩
  · have h := (hf t).mul (isHomogeneous_X_pow i (∑ t, e t - e t))
    rwa [Nat.add_sub_cancel' (hle t)] at h
  · have hD : x i ^ (∑ t, e t) = x i ^ e t * x i ^ (∑ t, e t - e t) := by
      rw [← pow_add, Nat.add_sub_cancel' (hle t)]
    rw [hfa t, map_mul, map_pow, aeval_X, hD, mul_div_mul_right _ _ (pow_ne_zero _ hi)]

theorem mConeMapOver_rename_base {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω]
    (x : Fin (N + 1) → Ω) {m : ℕ} (s : Fin m → Ω) {F : Kleiman.Poly k N} {D : ℕ} (hF : F.IsHomogeneous D) :
    mConeMapOver k (graphVec x s) (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) F) =
      C (aeval x F) * X baseBlock ^ D := by
  have h := congrArg (fun φ => φ F) (mConeMapOver_graph_comp_base (S := k) x s)
  simp only [AlgHom.comp_apply] at h
  rw [h, Kleiman.cone_eq, Kleiman.coneGen_of_isHomogeneous x hF]
  simp only [AlgHom.restrictScalars_apply, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    MvPolynomial.algebraMap_eq]

theorem mConeMapOver_X' {k : Type} [Field k] {N : ℕ} {Ω : Type} [Field Ω] [Algebra k Ω] {m : ℕ}
    (y : (Σ c, graphIdx N m c) → Ω) (v : Σ c, graphIdx N m c) :
    mConeMapOver k y (X v) = C (y v) * X v.1 := by
  simp [mConeMapOver]

theorem SectionRatio.full : SectionRatio.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle j b hYj
  have hmem : ∀ P, mConeMapOver k (graphVec x s) P = 0 → P ∈ W := fun P hP => hle (RingHom.mem_ker.mpr hP)
  obtain ⟨i, hXi⟩ : ∃ i : Fin (N + 1), (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) k) ∉ W :=
    hW.relevant baseBlock
  have hi : x i ≠ 0 := fun h0 => hXi (hmem _ (by
    rw [mConeMapOver_X', show graphVec x s ⟨baseBlock, i⟩ = 0 from h0, map_zero, zero_mul]))
  obtain ⟨w, hw, hsum⟩ := exists_graph_inverse Q n s hgen hi
  have hw' : ∀ p : Fin m × Fin m,
      x i ^ (-n) * s p.1 * w p.2 ∈ Kleiman.chartRing k x (Kleiman.singleChart hi) := fun p => by
    rw [← chartRingOver_oneBlock x (fun _ => i) hi]; exact hw p.1 p.2
  obtain ⟨D, E, hE, hEq⟩ := exists_common_form_div hi _ hw'
  have hval : ∀ a c, aeval x (E (a, c)) = x i ^ D * (x i ^ (-n) * s a * w c) := fun a c => by
    have h := hEq (a, c)
    dsimp only at h
    rw [h]; field_simp
  obtain ⟨b0, hb0⟩ : ∃ b0, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, b0)) ∉ W := by
    by_contra h
    push Not at h
    have key : ∑ c, aeval x (E (j, c)) * s c = x i ^ D * s j := by
      simp only [hval]
      calc ∑ c, x i ^ D * (x i ^ (-n) * s j * w c) * s c
          = x i ^ D * s j * ∑ c, x i ^ (-n) * s c * w c := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
        _ = x i ^ D * s j := by rw [hsum, mul_one]
    have hrel : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
          X ⟨Sum.inr (), c⟩ -
        rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i ^ D) *
          X ⟨Sum.inr (), j⟩ ∈ W := by
      apply hmem
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, map_mul, mConeMapOver_rename_base x s (isHomogeneous_X_pow i D), mConeMapOver_X']
      have hc : ∀ c, mConeMapOver k (graphVec x s)
          (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
            X ⟨Sum.inr (), c⟩) = C (aeval x (E (j, c)) * s c) * (X baseBlock ^ D * X (Sum.inr ())) := fun c => by
        rw [map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_X', graphVec_inr, map_mul]
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun c _ => hc c, ← Finset.sum_mul, ← map_sum, key, graphVec_inr]
      simp only [map_pow, aeval_X, map_mul]
      ring
    have hsumW : ∑ c, rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (E (j, c)) *
        X ⟨Sum.inr (), c⟩ ∈ W := W.sum_mem fun c _ => W.mul_mem_right _ (h c)
    have hXY := W.sub_mem hsumW hrel
    rw [sub_sub_cancel, map_pow, rename_X] at hXY
    rcases hW.isPrime.mem_or_mem hXY with h1 | h1
    · exact hXi (hW.isPrime.mem_of_pow_mem _ h1)
    · exact hYj h1
  refine ⟨D, E (b, b0), E (j, b0), hE _, hE _, hb0, hmem _ ?_⟩
  rw [map_sub, map_mul, map_mul, mConeMapOver_rename_base x s (hE _), mConeMapOver_rename_base x s (hE _),
    mConeMapOver_X', mConeMapOver_X', graphVec_inr, graphVec_inr, hval, hval]
  dsimp only
  simp only [map_mul]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

