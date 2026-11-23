module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

noncomputable section
namespace GlobalTheory.SBExtend

variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]


open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
theorem _root_.GlobalTheory.SBExtend.exists_isCompact_isClopen_between {K W : Set X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) : ∃ V : Set X, IsCompact V ∧ IsClopen V ∧ K ⊆ V ∧ V ⊆ W := by
  have hB := loc_compact_Haus_tot_disc_of_zero_dim (X := X)
  have h : ∀ x ∈ K, ∃ U : Set X, (IsClopen U ∧ IsCompact U) ∧ x ∈ U ∧ U ⊆ W := by
    intro x hx
    obtain ⟨C, hCx, hCW, hC⟩ := local_compact_nhds (hW.mem_nhds (hKW hx))
    obtain ⟨U, hU, hxU, hUC⟩ :=
      hB.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.2 hCx) isOpen_interior
    exact ⟨U, ⟨hU, hC.of_isClosed_subset hU.isClosed (hUC.trans interior_subset)⟩, hxU,
      (hUC.trans interior_subset).trans hCW⟩
  choose U hU hxU hUW using h
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U fun x hx => (hU x hx).1.isOpen.mem_nhds (hxU x hx)
  exact ⟨⋃ x ∈ t, U x x.2, t.isCompact_biUnion fun x _ => (hU x x.2).2,
    isClopen_biUnion_finset fun x _ => (hU x x.2).1, ht, Set.iUnion₂_subset fun x _ => hUW x x.2⟩


open Matrix Topology in
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] in
omit [LocallyCompactSpace X] [TotallyDisconnectedSpace X] in
theorem _root_.GlobalTheory.SBExtend.indicator_mem_SB {V : Set X} (hc : IsCompact V)
    (hV : IsClopen V) : (V.indicator fun _ => (1 : ℂ)) ∈ _root_.GlobalTheory.SplitWeil.SB X := by
  show IsLocallyConstant _ ∧ HasCompactSupport _
  refine ⟨fun s => ?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  rcases Set.indicator_const_preimage V s (1 : ℂ) with h | h | h | h <;> rw [h]
  exacts [isOpen_univ, hV.isOpen, hV.compl.isOpen, isOpen_empty]

end GlobalTheory.SBExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquare
section
namespace GlobalTheory.SplitFlip

def pathInnerDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem pathInnerDiff_tgt (e : Edge) : pathInnerDiff e.tgt = pathInnerDiff e.src + 1 := by
  cases e <;> simp [pathInnerDiff, Edge.tgt, Edge.src] <;> push_cast <;> ring

theorem IsPath.pairwise_lt_source_index_difference_along_path {γ : List Edge} (hγ : IsPath γ) :
    (γ.map fun e => pathInnerDiff e.src).Pairwise (· < ·) := by
  have h : (γ.map fun e => pathInnerDiff e.src).IsChain (· < ·) :=
    List.isChain_map_of_isChain _ (R := fun a b : Edge => a.tgt = b.src) (fun a b (hab : a.tgt = b.src) => by
      show pathInnerDiff a.src < pathInnerDiff b.src
      rw [← hab, pathInnerDiff_tgt]; omega) (by unfold IsPath at hγ; exact hγ)
  exact h.pairwise

theorem IsPath.eq_of_src_eq_of_mem {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : a.src = b.src) : a = b :=
  List.inj_on_of_nodup_map hγ.pairwise_lt_source_index_difference_along_path.nodup ha hb (by simp [h])

theorem src_flipEdge_pathInner (i j : ℕ) (e : Edge) :
    (if e = .theta i j then Edge.ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e).src =
      if e = .ex i j then (i + 1, j + 1) else e.src := by
  by_cases h1 : e = .theta i j
  · subst h1; simp
  · by_cases h2 : e = .ex i j
    · subst h2; simp
    · simp [h1, h2]

theorem mem_innerVertices_flipPath {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hp : PassesThrough i j γ) :
    ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  intro X hX
  rw [innerVertices, flipPath, ← List.map_tail, List.map_map, List.mem_map] at hX
  obtain ⟨e, he, rfl⟩ := hX
  rw [Function.comp_apply, src_flipEdge_pathInner]
  have hex : Edge.ex i j ∈ γ := hp.subset (by simp)
  have heγ : e ∈ γ := List.mem_of_mem_tail he
  by_cases h : e = .ex i j
  · simp only [h, if_true]
    refine ⟨fun H => ?_, fun H => absurd rfl H⟩
    simp at H
  · simp only [h, if_false]
    refine ⟨fun H => h (hγ.eq_of_src_eq_of_mem heγ hex (by simpa using H)), fun _ => List.mem_map.2 ⟨e, he, rfl⟩⟩

end GlobalTheory.SplitFlip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpEOmTargetUnipotent
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.RootEx.TargetUnip

theorem det_eq_one_of_level {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (f : ι → ℕ)
    (M : Matrix ι ι k) (hM : ∀ r s, f s ≤ f r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by
  have hb : M.BlockTriangular f := by
    intro r s h
    rw [hM r s h.le, Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h
  rw [hb.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have : M.toSquareBlock f a = 1 := by
    ext i j
    rw [Matrix.toSquareBlock_def, Matrix.of_apply, hM _ _ (by rw [i.2, j.2])]
    simp [Matrix.one_apply, Subtype.ext_iff]
  rw [this, Matrix.det_one]

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']

theorem mul_apply_of_inN {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) {m : Type*}
    (x : Matrix (n ⊕ Fin c) m k) (r : n ⊕ Fin c) (s : m) :
    (h.val * x) r s = x r s + ∑ r', if lev p r < lev p r' then h.val r r' * x r' s else 0 := by
  have h1 : x r s = ∑ r', (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r r' * x r' s := by
    rw [← Matrix.mul_apply, Matrix.one_mul]
  rw [Matrix.mul_apply, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r' _ => ?_
  split_ifs with hl
  · rw [Matrix.one_apply_ne, zero_mul, zero_add]
    rintro rfl
    exact lt_irrefl _ hl
  · rw [hh r r' (not_lt.1 hl), add_zero]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_of_not_free (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r s} (hrs : ¬ Free p (r, s)) :
    affPt p x₀ e r s = basePt c x₀ r s := by
  simp [affPt, hrs]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in
theorem affPt_eq_zero (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) {r r' : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hrs : ¬ Free p (r, s))
    (hl : lev p r < lev p r') : affPt p x₀ e r' s = 0 := by
  rcases r with r | r <;> rcases r' with r' | r' <;> rcases s with s | s <;>
    simp only [lev, Free, Sum.elim_inl, Sum.elim_inr, lt_irrefl] at hrs hl <;>
    rw [affPt_of_not_free _ _ _ (by simp only [Free]; omega)] <;>
    simp [basePt] <;> omega


open Classical in
def linPart (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    Matrix {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}
      {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} k :=
  Matrix.of fun a b => if a.1.2 = b.1.2 then h a.1.1 b.1.1 else 0

open Classical in
theorem det_linPart {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) :
    (linPart (n' := n') p h.val).det = 1 := by
  refine det_eq_one_of_level (fun a => lev p a.1.1) _ fun a b hab => ?_
  simp only [linPart, Matrix.of_apply]
  rw [hh _ _ hab]
  simp only [Matrix.one_apply, Subtype.ext_iff, Prod.ext_iff]
  by_cases h1 : a.1.1 = b.1.1 <;> by_cases h2 : a.1.2 = b.1.2 <;> simp [h1, h2]

open Classical in
theorem linPart_mulVec (p : ℕ) (h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (a : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}) :
    (linPart p h).mulVec e a =
      ∑ r', h a.1.1 r' * (if hf : Free p (r', a.1.2) then e ⟨(r', a.1.2), hf⟩ else 0) := by
  let F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun b =>
    (if a.1.2 = b.2 then h a.1.1 b.1 else 0) * (if hf : Free p b then e ⟨b, hf⟩ else 0)
  have h1 : (linPart p h).mulVec e a = ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 := by
    simp only [Matrix.mulVec, dotProduct, linPart, Matrix.of_apply, F]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dite_eq_left b.2]
  have h2 : ∑ b : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs}, F b.1 = ∑ b, F b := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun b => Free p b) (by simp) F]
    refine Finset.sum_filter_of_ne fun b _ hb => ?_
    by_contra hf
    exact hb (by simp [F, hf])
  rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [Finset.sum_eq_single a.1.2]
  · simp [F]
  · intro s _ hs
    simp [F, hs.symm]
  · simp

open Classical in
theorem mul_affPt {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    h.val * affPt p x₀ e = affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) := by
  ext r s
  by_cases hf : Free p (r, s)
  · have : affPt p x₀ ((linPart p h.val).mulVec e +
      fun a => (h.val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2) r s =
        basePt c x₀ r s + ((linPart p h.val).mulVec e ⟨(r, s), hf⟩ +
          (h.val * basePt c x₀ - basePt c x₀) r s) := by
      simp [affPt, hf]
    rw [this, linPart_mulVec, affPt, Matrix.mul_add, Matrix.add_apply, Matrix.sub_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply]
    ring
  · rw [affPt_of_not_free _ _ _ hf, mul_apply_of_inN hh, affPt_of_not_free _ _ _ hf,
      Finset.sum_eq_zero, add_zero]
    intro r' _
    split_ifs with hl
    · rw [affPt_eq_zero p x₀ e hf hl, mul_zero]
    · rfl

omit [Fintype n'] [DecidableEq n'] in
theorem ch_mul_affPt {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (h.val * affPt p x₀ e) = ch (affPt p x₀ e) + simpleSum h := by
  rw [ch, ch, simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_apply_of_inN hh, Fintype.sum_sum_type, Finset.sum_eq_zero, zero_add]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hl : lev (n := n) p (Sum.inr i) < lev (n := n) p (Sum.inr j)
    · rw [if_pos hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rw [if_neg hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [if_neg (by omega)]
  · intro r _
    split_ifs with hl
    · simp only [lev, Sum.elim_inr, Sum.elim_inl] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rfl

end GlobalTheory.RootEx.TargetUnip


open GlobalTheory.RootEx.TargetUnip in
theorem GlobalTheory.RootEx.opE_om_target_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure] (μ : kˣ →* ℂˣ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), ∀ g ∈ N k n c p, opE ψ ν p (om μ 1 g Φ) = (ψ (-simpleSum g) : ℂ) • opE ψ ν p Φ := by
  classical
  intro k _ _ _ _ _ _ n n' _ _ _ _ c p _ _ ψ ν _ μ Φ g hg
  obtain ⟨hN, hadd, hdet, -⟩ := GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c p
  have hg' : g⁻¹ ∈ N k n c p := inv_mem hg
  have hh : InN p g⁻¹ := (hN _).1 hg'
  have hs1 : simpleSum (1 : GL (n ⊕ Fin c) k) = 0 := by
    have := hadd 1 (one_mem _) 1 (one_mem _)
    rw [mul_one] at this
    exact left_eq_add.1 this
  have hs : simpleSum g⁻¹ = -simpleSum g := by
    have := hadd g hg g⁻¹ hg'
    rw [mul_inv_cancel, hs1] at this
    linear_combination -this
  have hn1 : nabs k 1 = 1 := by simp [nabs]
  have hom : ∀ x, om μ 1 g Φ x = Φ ((g⁻¹).val * x) := by
    intro x
    simp [om, hdet g hg, hn1]
  haveI := secondCountable k
  funext x₀
  let F : ({rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) → ℂ := fun e =>
    Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ)
  let t : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k :=
    fun a => ((g⁻¹).val * basePt c x₀ - basePt c x₀) a.1.1 a.1.2
  let L := Matrix.GeneralLinearGroup.mkOfDetNeZero (linPart (n' := n') p (g⁻¹).val)
    (by rw [det_linPart hh]; exact one_ne_zero)
  have hL : Matrix.GeneralLinearGroup.det L = 1 := by
    ext
    exact det_linPart hh
  have key : ∀ e, om μ 1 g Φ (affPt p x₀ e) * (ψ (-ch (affPt p x₀ e)) : ℂ) =
      (ψ (-simpleSum g) : ℂ) * F (L.val.mulVec e + t) := by
    intro e
    have h1 := mul_affPt hh x₀ e
    have h2 := ch_mul_affPt hh x₀ e
    have h3 : F (L.val.mulVec e + t) = Φ ((g⁻¹).val * affPt p x₀ e) *
        (ψ (-ch ((g⁻¹).val * affPt p x₀ e)) : ℂ) := by
      rw [h1]; rfl
    rw [h3, h2, hs, hom, mul_left_comm, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  have hcov := integral_comp_mulVec_eq_smul ν L
    (fun e => F (e + t))
  rw [hL, hn1, inv_one, one_smul, integral_add_right_eq_self] at hcov
  simp only [opE, Pi.smul_apply, smul_eq_mul, key]
  rw [integral_const_mul, hcov]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatEventuallyInvariantOfContinuousAct
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory

theorem schwartzBruhat_eventually_invariant_of_continuous_action :
    ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
      (r : X → G → X), (∀ x, r x 1 = x) → (∀ x g h, r x (g * h) = r (r x g) h) →
      Continuous (fun p : X × G => r p.1 p.2) →
      ∀ Φ : SB X, ∀ᶠ u in nhds (1 : G), ∀ x, Φ.1 (r x u) = Φ.1 x := by
  intro G X _ _ _ _ r h1 hmul hc Φ
  have hΦ : IsLocallyConstant Φ.1 ∧ HasCompactSupport Φ.1 := Φ.2
  obtain ⟨hlc, hcs⟩ := hΦ
  have hA : IsLocallyConstant (fun z : G × X => Φ.1 (r z.2 z.1)) :=
    hlc.comp_continuous (hc.comp continuous_swap)
  have hB : IsLocallyConstant (fun z : G × X => Φ.1 z.2) :=
    hlc.comp_continuous continuous_snd
  have key : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u) = Φ.1 x := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun u x => Φ.1 (r x u) = Φ.1 x) hcs ?_
    intro y _
    filter_upwards [hA.eventually_eq ((1 : G), y), hB.eventually_eq ((1 : G), y)] with z hz hz'
    rw [hz, hz']
    simp only [h1]
  have key' : ∀ᶠ u in nhds (1 : G), ∀ x ∈ tsupport Φ.1, Φ.1 (r x u⁻¹) = Φ.1 x := by
    have ht : Filter.Tendsto (fun u : G => u⁻¹) (nhds 1) (nhds 1) := by
      simpa using (continuous_inv (G := G)).tendsto 1
    exact ht.eventually key
  filter_upwards [key, key'] with u hu hu' x
  by_cases hx : x ∈ tsupport Φ.1
  · exact hu x hx
  · by_cases hy : r x u ∈ tsupport Φ.1
    · have := hu' _ hy
      rw [← hmul, mul_inv_cancel, h1] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruh
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

noncomputable section
namespace GlobalTheory.SplitWeil.FourierSurj

theorem hat_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  intro k _ _ _ _ _ _ n _ _ ψ hc h1 ν hν
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have key := FourierPi.fourier_pi k n ψ hc h1 ν hν
  have hhat : ∀ f : (n → k) → ℂ,
      hat ψ ν f = fun y : n → k => ∫ x, f x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν) := by
    intro f
    funext y
    simp only [hat, dotProduct_comm y]
  have hmem : ∀ f ∈ SB (n → k), hat ψ ν f ∈ SB (n → k) := fun f hf => hhat f ▸ (key f hf).1
  refine ⟨fun Φ₀ => hmem _ Φ₀.2, fun g => ?_⟩
  have hcomp : ∀ (e : (n → k) ≃ₜ (n → k)), ∀ f ∈ SB (n → k), (fun x => f (e x)) ∈ SB (n → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hg' : (fun x => g.1 (-x)) ∈ SB (n → k) := hcomp (Homeomorph.neg _) _ g.2
  refine ⟨⟨_, hmem _ hg'⟩, ?_⟩
  funext u
  have hf : (fun x => g.1 (-(x + -u))) ∈ SB (n → k) := hcomp (Homeomorph.addRight (-u)) _ hg'
  have h2 := (key _ hf).2
  simp only [zero_add, neg_neg] at h2
  rw [← h2]
  show ∫ β, hat ψ ν (fun x => g.1 (-x)) β * (ψ (u ⬝ᵥ β) : ℂ) ∂(Measure.pi fun _ => ν) = _
  congr 1
  funext y
  rw [hhat, ← integral_mul_const,
    ← integral_add_right_eq_self (μ := Measure.pi fun _ : n => ν) _ (-u)]
  congr 1
  funext x
  rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← add_dotProduct, neg_add_cancel_right]

end GlobalTheory.SplitWeil.FourierSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridPathAvoidsOppositeCorner
section
namespace GlobalTheory.SplitFlip

def vertexDiff (X : ℕ × ℕ) : ℤ := (X.1 : ℤ) - X.2

theorem vertexDiff_tgt (e : Edge) : vertexDiff e.tgt = vertexDiff e.src + 1 := by
  cases e <;> simp [vertexDiff, Edge.src, Edge.tgt] <;> omega

theorem IsPath.pairwise_vertexDiff : ∀ {γ : List Edge}, IsPath γ →
    γ.Pairwise fun a b => vertexDiff a.src < vertexDiff b.src := by
  intro γ h
  let r : Edge → Edge → Prop := fun a b => vertexDiff a.src < vertexDiff b.src
  let : Trans r r r := ⟨fun hab hbc => lt_trans hab hbc⟩
  change γ.Pairwise r
  apply List.IsChain.pairwise
  refine List.IsChain.imp (fun {a b} hab => ?_) h
  change vertexDiff a.src < vertexDiff b.src
  rw [← hab, vertexDiff_tgt]
  omega

theorem IsPath.eq_of_vertexDiff_eq {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : vertexDiff a.src = vertexDiff b.src) : a = b := by
  by_contra hne
  have hpw := hγ.pairwise_vertexDiff
  have key : ∀ {l : List Edge}, l.Pairwise (fun a b => vertexDiff a.src < vertexDiff b.src) →
      ∀ {a b : Edge}, a ∈ l → b ∈ l → a ≠ b → vertexDiff a.src ≠ vertexDiff b.src := by
    intro l hl
    induction hl with
    | nil => intro a b ha; simp at ha
    | @cons x l hx _ ih =>
      intro a b ha hb hab
      rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact (hx b hb').ne
      · exact (hx a ha').ne'
      · exact ih ha' hb' hab
  exact key hpw ha hb hne h

theorem pathAvoid : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ →
    ∀ b ∈ γ, b.src ≠ (i + 1, j + 1) ∧ b.tgt ≠ (i + 1, j + 1) := by
  intro γ i j hγ hp b hb
  have hθ : Edge.theta i j ∈ γ := hp.subset (by simp)
  have hx : Edge.ex i j ∈ γ := hp.subset (by simp)
  refine ⟨fun hs => ?_, fun ht => ?_⟩
  · have := hγ.eq_of_vertexDiff_eq hb hx (by rw [hs]; simp [vertexDiff, Edge.src])
    subst this
    simp [Edge.src] at hs
  · have h1 := vertexDiff_tgt b
    rw [ht] at h1
    have := hγ.eq_of_vertexDiff_eq hb hθ (by simp [vertexDiff, Edge.src] at h1 ⊢; omega)
    subst this
    simp [Edge.tgt] at ht

end GlobalTheory.SplitFlip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumWithLatKerEqMulSumWithKerLat
section
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair
open scoped Pointwise

namespace GlobalTheory.LatPair

theorem card_withLat_eq_card_withKer {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} (L : Submodule (↥𝒪[k]) (n → k))
    [Submodule.IsFullLattice k L] : (withLat L).card = (withKer L).card := by
  classical
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  have e : Red L ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red L) := (Module.Free.chooseBasis 𝓀[k] (Red L)).toDualEquiv
  have e' : {x : Red L // x ≠ 0} ≃ {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} :=
    e.toEquiv.subtypeEquiv (fun x => by simp)
  refine Finset.card_eq_of_equiv ?_
  exact (Equiv.subtypeEquivRight (fun P => mem_withLat)).trans
    ((latEquiv L).symm.trans (e'.symm.trans ((kerEquiv L q).trans
      (Equiv.subtypeEquivRight (fun P => mem_withKer.symm)))))

end GlobalTheory.LatPair
end

