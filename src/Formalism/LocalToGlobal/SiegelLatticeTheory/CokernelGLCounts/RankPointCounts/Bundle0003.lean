module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundT
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

section TriT

variable {P : Type} [Fintype P] [DecidableEq P] {α : P → Type} [∀ p, AddCommGroup (α p)]
  (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
  (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
  (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
  (A : ∀ p, AddSubgroup (α p)) (F : ∀ p, Set (α p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)

include hBd hτ hFd in

include hBd hτ hFd in
theorem box_fundT (g : ∀ q, α q) :
    ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ ∀ p, mlaw B γ g p ∈ F p := by
  let c : (∀ q, α q) → ∀ p, A p := fun x p => (hFd p (τ p x + g p + B p x g)).exists.choose
  have hc : ∀ x p, ((c x p : A p) : α p) + (τ p x + g p + B p x g) ∈ F p :=
    fun x p => (hFd p (τ p x + g p + B p x g)).exists.choose_spec
  let Φ : (∀ q, α q) → ∀ q, α q := fun x p => τ p x + (c x p : α p)
  have hΦ : ∀ (k : ℕ) (x x' : ∀ q, α q), (∀ q, h q < k → x q = x' q) →
      ∀ p, h p < k + 1 → Φ x p = Φ x' p := by
    intro k x x' hxx p hp
    have e1 : ∀ q, h q < h p → x q = x' q := fun q hq => hxx q (by omega)
    have h1 : τ p x = τ p x' := hτ p x x' e1
    have h2 : B p x g = B p x' g := hBd p x x' g g fun q hq => ⟨e1 q hq, rfl⟩
    show τ p x + ((hFd p (τ p x + g p + B p x g)).exists.choose : α p) =
      τ p x' + ((hFd p (τ p x' + g p + B p x' g)).exists.choose : α p)
    rw [h1, h2]
  have hit : ∀ (n : ℕ) p, h p < n → Φ (Φ^[n] 0) p = (Φ^[n] 0) p := by
    intro n
    induction n with
    | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro p hp
      rw [Function.iterate_succ_apply']
      exact hΦ k _ _ ih p hp
  have uniq : ∀ x y : ∀ q, α q, ((∀ p, x p - τ p x ∈ A p) ∧ ∀ p, mlaw B x g p ∈ F p) →
      ((∀ p, y p - τ p y ∈ A p) ∧ ∀ p, mlaw B y g p ∈ F p) → x = y := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    have step : ∀ (n : ℕ) p, h p < n → x p = y p := by
      intro n
      induction n with
      | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
      | succ k ih =>
        intro p hp
        have e1 : ∀ q, h q < h p → x q = y q := fun q hq => ih q (by omega)
        have ht : τ p x = τ p y := hτ p x y e1
        have hb : B p x g = B p y g := hBd p x y g g fun q hq => ⟨e1 q hq, rfl⟩
        have hx2' : ((⟨x p - τ p x, hx1 p⟩ : A p) : α p) + (τ p x + g p + B p x g) ∈ F p := by
          have hm : x p + g p + B p x g ∈ F p := hx2 p
          rw [show ((⟨x p - τ p x, hx1 p⟩ : A p) : α p) = x p - τ p x from rfl,
            show x p - τ p x + (τ p x + g p + B p x g) = x p + g p + B p x g by abel]
          exact hm
        have hy2' : ((⟨y p - τ p y, hy1 p⟩ : A p) : α p) + (τ p x + g p + B p x g) ∈ F p := by
          have hm : y p + g p + B p y g ∈ F p := hy2 p
          rw [ht, hb, show ((⟨y p - τ p y, hy1 p⟩ : A p) : α p) = y p - τ p y from rfl,
            show y p - τ p y + (τ p y + g p + B p y g) = y p + g p + B p y g by abel]
          exact hm
        have h3 : x p - τ p x = y p - τ p y :=
          congrArg Subtype.val ((hFd p _).unique hx2' hy2')
        rw [ht] at h3
        exact sub_left_injective h3
    funext p
    exact step _ p (Nat.lt_succ_self _)
  have hfix : ∀ p, τ p (Φ^[Finset.univ.sup h + 1] 0) + (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) =
      (Φ^[Finset.univ.sup h + 1] 0) p :=
    fun p => hit _ p (Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p)))
  have hsol : (∀ p, (Φ^[Finset.univ.sup h + 1] 0) p - τ p (Φ^[Finset.univ.sup h + 1] 0) ∈ A p) ∧
      ∀ p, mlaw B (Φ^[Finset.univ.sup h + 1] 0) g p ∈ F p := by
    constructor
    · intro p
      rw [← hfix p, add_sub_cancel_left]
      exact (c _ p).2
    · intro p
      show (Φ^[Finset.univ.sup h + 1] 0) p + g p + B p (Φ^[Finset.univ.sup h + 1] 0) g ∈ F p
      rw [← hfix p]
      rw [show τ p (Φ^[Finset.univ.sup h + 1] 0) + (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) + g p +
          B p (Φ^[Finset.univ.sup h + 1] 0) g = (c (Φ^[Finset.univ.sup h + 1] 0) p : α p) +
          (τ p (Φ^[Finset.univ.sup h + 1] 0) + g p + B p (Φ^[Finset.univ.sup h + 1] 0) g) by abel]
      exact hc _ p
  exact ⟨_, hsol, fun y hy => uniq y _ hy hsol⟩

end TriT

theorem triFundT (P : Type) [Fintype P] [DecidableEq P] (α : P → Type) [∀ p, AddCommGroup (α p)]
    [∀ p, MeasurableSpace (α p)] [∀ p, MeasurableAdd₂ (α p)]
    (μ : ∀ p, Measure (α p)) [∀ p, SigmaFinite (μ p)] [∀ p, (μ p).IsAddRightInvariant]
    (h : P → ℕ) (B : ∀ p, (∀ q, α q) → (∀ q, α q) → α p)
    (hBm : ∀ p, Measurable (fun z : (∀ q, α q) × (∀ q, α q) => B p z.1 z.2))
    (hBd : ∀ p (x x' y y' : ∀ q, α q), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
    (hB0 : ∀ p (x : ∀ q, α q), B p x 0 = 0)
    (τ : ∀ p, (∀ q, α q) → α p) (hτ : ∀ p (x x' : ∀ q, α q), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
    (A : ∀ p, AddSubgroup (α p)) [∀ p, Countable (A p)]
    (hinv : ∀ γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) → ∃ γ' : ∀ q, α q, (∀ p, γ' p - τ p γ' ∈ A p) ∧
      ∀ g, mlaw B γ' (mlaw B γ g) = g ∧ mlaw B γ (mlaw B γ' g) = g)
    (F : ∀ p, Set (α p)) (hF : ∀ p, MeasurableSet (F p)) (hFd : ∀ p (v : α p), ∃! a : A p, (a : α p) + v ∈ F p)
    (K : Set (∀ p, α p)) (hK : MeasurableSet K)
    (hKd : ∀ g, ∃! γ : ∀ q, α q, (∀ p, γ p - τ p γ ∈ A p) ∧ mlaw B γ g ∈ K) :
    Measure.pi μ K = ∏ p, μ p (F p) := by
  classical
  set T : (∀ q, α q) → (∀ q, α q) → (∀ q, α q) := fun γ g => mlaw B γ g with hTdef
  have hT : ∀ γ, MeasurePreserving (T γ) (Measure.pi μ) (Measure.pi μ) := by
    intro γ
    have := shear_mp (Fintype.card P) P rfl α μ h (fun p g => γ p + B p γ g)
      (fun p => measurable_const.add ((hBm p).comp (measurable_const.prodMk measurable_id)))
      (fun p x x' hxx => by rw [hBd p γ γ x x' fun q hq => ⟨rfl, hxx q hq⟩])
    convert this using 1
    funext g p
    simp only [hTdef, mlaw]
    abel
  have hTm : ∀ γ, Measurable (T γ) := fun γ => (hT γ).measurable
  have hT0 : ∀ γ, T γ 0 = γ := by
    intro γ; funext p; simp [hTdef, mlaw, hB0]
  let Γs := {x : ∀ q, α q // ∀ p, x p - τ p x ∈ A p}
  have hcount : Countable Γs := by
    have hinj : Function.Injective (fun x : Γs => fun p => (⟨x.1 p - τ p x.1, x.2 p⟩ : A p)) := by
      intro x y hxy
      apply Subtype.ext
      funext p
      suffices H : ∀ n, ∀ p, h p < n → x.1 p = y.1 p from H (h p + 1) p (by omega)
      intro n
      induction n with
      | zero => intro p hp; omega
      | succ k ih =>
        intro p hp
        have hl : ∀ q, h q < h p → x.1 q = y.1 q := fun q hq => ih q (by omega)
        have e := congrArg Subtype.val (congrFun hxy p)
        simp only at e
        rw [hτ p x.1 y.1 hl] at e
        simpa using e
    exact hinj.countable
  choose inv hinvA hinvT using hinv
  let iv : Γs → Γs := fun γ => ⟨inv γ.1 γ.2, hinvA γ.1 γ.2⟩
  have hiv1 : ∀ (γ : Γs) g, T (iv γ).1 (T γ.1 g) = g := fun γ g => (hinvT γ.1 γ.2 g).1
  have hiv2 : ∀ (γ : Γs) g, T γ.1 (T (iv γ).1 g) = g := fun γ g => (hinvT γ.1 γ.2 g).2
  have hivv : ∀ γ : Γs, iv (iv γ) = γ := by
    intro γ
    apply Subtype.ext
    have e : ∀ g, T (iv (iv γ)).1 g = T γ.1 g := by
      intro g
      calc T (iv (iv γ)).1 g = T (iv (iv γ)).1 (T (iv γ).1 (T γ.1 g)) := by rw [hiv1 γ g]
        _ = T γ.1 g := hiv1 (iv γ) (T γ.1 g)
    rw [← hT0 (iv (iv γ)).1, ← hT0 γ.1, e]
  let ivE : Γs ≃ Γs := ⟨iv, iv, hivv, hivv⟩
  let R : Set (∀ p, α p) := Set.pi Set.univ F
  have hR : MeasurableSet R := MeasurableSet.univ_pi hF
  have hRd := box_fundT h B hBd τ hτ A F hFd
  have hK1 : Measure.pi μ K = ∑' γ : Γs, Measure.pi μ (K ∩ T γ.1 ⁻¹' R) := by
    have hU : K = ⋃ γ : Γs, K ∩ T γ.1 ⁻¹' R := by
      ext g; constructor
      · intro hg
        obtain ⟨γ, ⟨hγA, hγF⟩, -⟩ := hRd g
        exact Set.mem_iUnion.2 ⟨⟨γ, hγA⟩, hg, fun p _ => hγF p⟩
      · intro hg
        obtain ⟨γ, hg, -⟩ := Set.mem_iUnion.1 hg
        exact hg
    conv_lhs => rw [hU]
    refine measure_iUnion ?_ fun γ => hK.inter (hTm γ.1 hR)
    intro γ δ hγδ
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨-, hg1⟩ ⟨-, hg2⟩
    apply hγδ
    apply Subtype.ext
    exact (hRd g).unique ⟨γ.2, fun p => hg1 p (Set.mem_univ p)⟩ ⟨δ.2, fun p => hg2 p (Set.mem_univ p)⟩
  have hR1 : Measure.pi μ R = ∑' γ : Γs, Measure.pi μ (R ∩ T γ.1 ⁻¹' K) := by
    have hU : R = ⋃ γ : Γs, R ∩ T γ.1 ⁻¹' K := by
      ext g; constructor
      · intro hg
        obtain ⟨γ, ⟨hγA, hγK⟩, -⟩ := hKd g
        exact Set.mem_iUnion.2 ⟨⟨γ, hγA⟩, hg, hγK⟩
      · intro hg
        obtain ⟨γ, hg, -⟩ := Set.mem_iUnion.1 hg
        exact hg
    conv_lhs => rw [hU]
    refine measure_iUnion ?_ fun γ => hR.inter (hTm γ.1 hK)
    intro γ δ hγδ
    rw [Function.onFun, Set.disjoint_left]
    rintro g ⟨-, hg1⟩ ⟨-, hg2⟩
    apply hγδ
    apply Subtype.ext
    exact (hKd g).unique ⟨γ.2, hg1⟩ ⟨δ.2, hg2⟩
  have hterm : ∀ γ : Γs, Measure.pi μ (K ∩ T γ.1 ⁻¹' R) = Measure.pi μ (R ∩ T (iv γ).1 ⁻¹' K) := by
    intro γ
    have e : K ∩ T γ.1 ⁻¹' R = T γ.1 ⁻¹' (R ∩ T (iv γ).1 ⁻¹' K) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      rw [hiv1 γ g]
      tauto
    rw [e]
    exact (hT γ.1).measure_preimage (hR.inter (hTm _ hK)).nullMeasurableSet
  rw [hK1, tsum_congr hterm, show (∑' γ : Γs, Measure.pi μ (R ∩ T (iv γ).1 ⁻¹' K)) =
      ∑' γ : Γs, Measure.pi μ (R ∩ T γ.1 ⁻¹' K) from ivE.tsum_eq (fun γ => Measure.pi μ (R ∩ T γ.1 ⁻¹' K)),
    ← hR1]
  exact Measure.pi_pi μ F

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdealCovol
section
noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem idealCovol (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : AddSubgroup K)
    (hΛ : ∀ a ∈ Λ, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : ℕ)
    (hk : Λ.relIndex (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k)
    (hk0 : k ≠ 0) (s : ℝ) (hs : s ≠ 0) (F : Set (ι → ℂ)) (hF : MeasurableSet F)
    (hFd : ∀ v, ∃! a : Λ, (fun i => (s : ℂ) * φ i a) + v ∈ F) :
    volume F = ENNReal.ofReal ((k : ℝ) * (FractionalIdeal.absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
      2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * |s| ^ (2 * Fintype.card ι)) := by
  set cj : ι → Prop := fun i => φ i ≠ (σ i).1.embedding
  have hψ : MeasurePreserving (phiMap σ cj (K := K)) volume volume := phiMap_mp σ cj
  have hψe : ∀ a : K, phiMap σ cj (mixedEmbedding K a) = fun i => φ i a := by
    intro a; funext i
    simp only [phiMap, mixedEmbedding_apply_isComplex]
    by_cases hi : cj i
    · rw [if_pos hi]
      rcases hφ i with h | h
      · exact absurd h hi
      · rw [h, ComplexEmbedding.conjugate_coe_eq]
    · rw [if_neg hi]
      have : φ i = (σ i).1.embedding := not_not.1 hi
      rw [this]
  set emb : K →+ mixedSpace K := (mixedEmbedding K).toAddMonoidHom
  have hinj : Function.Injective emb := mixedEmbedding_injective K
  set Λm := Λ.map emb
  set G := phiMap σ cj (K := K) ⁻¹' (s⁻¹ • F)
  have hGm : MeasurableSet G := hψ.measurable (hF.const_smul₀ (s⁻¹))
  have hmem : ∀ y : ι → ℂ, y ∈ s⁻¹ • F ↔ s • y ∈ F := by
    intro y
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hs), inv_inv]
  have hsm : ∀ a : K, ∀ x : mixedSpace K, s • phiMap σ cj (emb a + x) = (fun i => (s : ℂ) * φ i a) + s • phiMap σ cj x := by
    intro a x
    rw [phiMap_add, smul_add, show emb a = mixedEmbedding K a from rfl, hψe]
    funext i
    simp [Complex.real_smul]
  have hdG : ∀ x, ∃! b : Λm, (b : mixedSpace K) + x ∈ G := by
    intro x
    obtain ⟨a, ha, hu⟩ := hFd (s • phiMap σ cj x)
    refine ⟨⟨emb a, AddSubgroup.mem_map_of_mem emb a.2⟩, ?_, ?_⟩
    · show phiMap σ cj (emb a + x) ∈ s⁻¹ • F
      rw [hmem, hsm]; exact ha
    · rintro ⟨b, hb⟩ hbG
      obtain ⟨a', ha', rfl⟩ := AddSubgroup.mem_map.1 hb
      have h1 : (fun i => (s : ℂ) * φ i (⟨a', ha'⟩ : Λ)) + s • phiMap σ cj x ∈ F := by
        have : phiMap σ cj (emb a' + x) ∈ s⁻¹ • F := hbG
        rw [hmem, hsm] at this; exact this
      have := hu ⟨a', ha'⟩ h1
      apply Subtype.ext
      show emb a' = emb a
      rw [show a' = (a : K) from congrArg Subtype.val this]

  set L := (idealLattice K I).toAddSubgroup
  have hL : L = (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup).map emb := by
    ext x
    simp only [L, Submodule.mem_toAddSubgroup, mem_idealLattice, AddSubgroup.mem_map]
    rfl
  have hle : Λm ≤ L := by
    rw [hL]; exact AddSubgroup.map_mono (fun a ha => hΛ a ha)
  have hk' : Λm.relIndex L = k := by
    rw [hL, AddSubgroup.relIndex_map_map_of_injective _ _ hinj, hk]
  have hcount : Countable L := by
    have b := Module.Free.chooseBasis ℤ (idealLattice K I)
    exact (Module.Free.chooseBasis ℤ (idealLattice K I)).equivFun.injective.countable
  set b := Module.Free.chooseBasis ℤ (idealLattice K I)
  set b' := Module.Basis.ofZLatticeBasis ℝ (idealLattice K I) b
  set FL := ZSpan.fundamentalDomain b'
  have hFLm : MeasurableSet FL := ZSpan.fundamentalDomain_measurableSet b'
  have hspan := Module.Basis.ofZLatticeBasis_span ℝ (idealLattice K I) b
  have hdL : ∀ x, ∃! l : L, (l : mixedSpace K) + x ∈ FL := by
    intro x
    obtain ⟨v, hv, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b' x
    have hvL : (v : mixedSpace K) ∈ idealLattice K I :=
      (congrArg (fun S : Submodule ℤ (mixedSpace K) => (v : mixedSpace K) ∈ S) hspan).mp v.2
    refine ⟨⟨v, hvL⟩, hv, ?_⟩
    rintro ⟨l, hl⟩ hlF
    have hl' : l ∈ Submodule.span ℤ (Set.range b') :=
      (congrArg (fun S : Submodule ℤ (mixedSpace K) => l ∈ S) hspan).mpr hl
    have h3 := hu ⟨l, hl'⟩ hlF
    have h2 : l = (v : mixedSpace K) := by rw [← h3]
    exact Subtype.ext h2
  have hidx := fund_index (volume : Measure (mixedSpace K)) L Λm hle k hk' hk0 FL G hFLm hGm hdL hdG

  have hfd := ZLattice.isAddFundamentalDomain b (volume : Measure (mixedSpace K))
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain (idealLattice K I) volume hfd
  rw [covolume_idealLattice] at hcov
  have hfin : volume FL ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b').measure_lt_top.ne
  have hFLv : volume FL = ENNReal.ofReal ((FractionalIdeal.absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
      2⁻¹ ^ InfinitePlace.nrComplexPlaces K * √|(discr K : ℝ)|) := by
    rw [hcov, measureReal_def, ENNReal.ofReal_toReal hfin]
  have hr2 : InfinitePlace.nrComplexPlaces K = Fintype.card ι := by
    rw [InfinitePlace.nrComplexPlaces, Fintype.card_congr σ.symm]

  have hGv : volume G = volume (s⁻¹ • F) := hψ.measure_preimage (hF.const_smul₀ (s⁻¹)).nullMeasurableSet
  have hscale : volume F = ENNReal.ofReal |s ^ Module.finrank ℝ (ι → ℂ)| * volume (s⁻¹ • F) := by
    conv_lhs => rw [← smul_inv_smul₀ hs F]
    exact Measure.addHaar_smul volume s (s⁻¹ • F)
  have hdim : Module.finrank ℝ (ι → ℂ) = 2 * Fintype.card ι := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  rw [hscale, ← hGv, hidx, hFLv, hr2, hdim]
  rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_pow]
  ring

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemTorsionOfMulConj
section
noncomputable section

open NumberField

namespace Formalism.L2.SG.NGCut.TorsionTotientBound

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cO (E : Type) [Field E] [NumberField E] [IsCMField E] : 𝓞 E ≃+* 𝓞 E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv

theorem cO_coe (y : 𝓞 E) : ((cO E y : 𝓞 E) : E) = IsCMField.complexConj E (y : E) := rfl

theorem mem_torsion_of_mul_conj (u : (𝓞 E)ˣ)
    (hu : ((u : 𝓞 E) : E) * IsCMField.complexConj E ((u : 𝓞 E) : E) = 1) : u ∈ Units.torsion E := by
  rw [Units.mem_torsion]
  intro w
  have h1 : w.embedding ((u : 𝓞 E) : E) *
      w.embedding (IsCMField.complexConj E ((u : 𝓞 E) : E)) = 1 := by
    rw [← map_mul, hu, map_one]
  rw [IsCMField.complexEmbedding_complexConj, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 : ‖w.embedding ((u : 𝓞 E) : E)‖ ^ 2 = 1 := by exact_mod_cast h1
  have key : ‖w.embedding ((u : 𝓞 E) : E)‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
  exact (InfinitePlace.norm_embedding_eq w _).symm.trans key

theorem count_int (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (m : 𝓞 E) (hm : m ≠ 0) (S : Finset (𝓞 E))
    (hS : ∀ y ∈ S, y ∈ I ∧ y * cO E y = m) :
    S.card * Ideal.absNorm I ^ 2 ≤ 2 * (Module.finrank ℚ E) ^ 2 * (Algebra.norm ℤ m).natAbs := by
  classical
  haveI : Fintype (Units.torsion E) := Fintype.ofFinite _
  rcases S.eq_empty_or_nonempty with hS0 | ⟨y0, hy0⟩
  · simp [hS0]
  have hNI' : Ideal.absNorm (I.map (cO E)) = Ideal.absNorm I :=
    absNorm_map_equiv (cO E) I
  have hI0 : Ideal.absNorm I ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hI'0 : I.map (cO E) ≠ ⊥ := by
    intro h; apply hI0; rw [← hNI']; exact Ideal.absNorm_eq_zero_iff.mpr h
  have hdvdI : ∀ y ∈ S, I ∣ Ideal.span {y} := fun y hy =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem I).mpr (hS y hy).1)
  have hdvdI' : ∀ y ∈ S, I.map (cO E) ∣ Ideal.span {cO E y} := fun y hy =>
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_map_of_mem (cO E) (hS y hy).1))
  have hspan : ∀ y ∈ S, Ideal.span {y} * Ideal.span {cO E y} = Ideal.span {m} :=
    fun y hy => by rw [Ideal.span_singleton_mul_span_singleton, (hS y hy).2]
  obtain ⟨M, hM⟩ : I * I.map (cO E) ∣ Ideal.span {m} := by
    rw [← hspan y0 hy0]; exact mul_dvd_mul (hdvdI y0 hy0) (hdvdI' y0 hy0)
  have hm0 : Ideal.span {m} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  have hM0 : M ≠ ⊥ := by
    rintro rfl; rw [Ideal.mul_bot] at hM; exact hm0 hM
  have hNm : (Algebra.norm ℤ m).natAbs = Ideal.absNorm I ^ 2 * Ideal.absNorm M := by
    rw [← Ideal.absNorm_span_singleton, hM, map_mul, map_mul, hNI', sq]
  have hII' : I * I.map (cO E) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, not_or]; exact ⟨hI, hI'0⟩
  have hdiv : ∀ y ∈ S, ∃ K : Ideal (𝓞 E), Ideal.span {y} = I * K := fun y hy => by
    obtain ⟨K, hK⟩ := hdvdI y hy; exact ⟨K, hK⟩
  choose! J hJ using hdiv
  have hJM : ∀ y ∈ S, J y ∣ M := fun y hy => by
    obtain ⟨K, hK⟩ := hdvdI' y hy
    refine ⟨K, ?_⟩
    have h := hspan y hy
    rw [hJ y hy, hK, hM] at h
    apply mul_left_cancel₀ hII'
    rw [← h]; ring
  have hcardJ : (S.image J).card ≤ Ideal.absNorm M :=
    card_dvd_le_absNorm M hM0 _ (fun K hK => by
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hK; exact hJM y hy)
  have hT : ∀ K ∈ S.image J, (S.filter fun y => J y = K).card ≤ Fintype.card (Units.torsion E) := by
    intro K hK
    obtain ⟨y1, hy1, rfl⟩ := Finset.mem_image.mp hK
    calc (S.filter fun y => J y = J y1).card
        ≤ ((Finset.univ : Finset (Units.torsion E)).image
            (fun ζ : Units.torsion E => ((ζ : (𝓞 E)ˣ) : 𝓞 E) * y1)).card := by
          apply Finset.card_le_card
          intro y hy
          rw [Finset.mem_filter] at hy
          obtain ⟨hyS, hyJ⟩ := hy
          have hsp : Ideal.span {y1} = Ideal.span {y} := by rw [hJ y hyS, hJ y1 hy1, hyJ]
          obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hsp
          have hy1m := (hS y1 hy1).2
          have hym := (hS y hyS).2
          rw [← hu, map_mul] at hym
          have huu : (u : 𝓞 E) * cO E (u : 𝓞 E) = 1 := by
            apply mul_left_cancel₀ hm
            calc m * ((u : 𝓞 E) * cO E (u : 𝓞 E))
                = y1 * (u : 𝓞 E) * (cO E y1 * cO E (u : 𝓞 E)) := by
                  rw [← hy1m]; ring
              _ = m * 1 := by rw [hym, mul_one]
          have htor : u ∈ Units.torsion E := by
            apply mem_torsion_of_mul_conj
            have h := congrArg (fun z : 𝓞 E => (z : E)) huu
            simpa [cO_coe] using h
          rw [Finset.mem_image]
          exact ⟨(⟨u, htor⟩ : Units.torsion E), Finset.mem_univ _, by
            show (u : 𝓞 E) * y1 = y
            rw [mul_comm]; exact hu⟩
      _ ≤ Fintype.card (Units.torsion E) := by
          rw [← Finset.card_univ]; exact Finset.card_image_le
  have hcard : S.card ≤ Fintype.card (Units.torsion E) * (S.image J).card :=
    Finset.card_le_mul_card_image S _ hT
  have htors : Fintype.card (Units.torsion E) ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
    have h := torsionOrder_le E
    first
    | exact h
    | (rw [← Nat.card_eq_fintype_card]; exact h)
    | (rw [← Nat.card_eq_fintype_card]; unfold Units.torsionOrder at h; exact h)
    | (simpa [Units.torsionOrder, Nat.card_eq_fintype_card] using h)
  have hS' : S.card ≤ 2 * (Module.finrank ℚ E) ^ 2 * Ideal.absNorm M :=
    hcard.trans (Nat.mul_le_mul htors hcardJ)
  calc S.card * Ideal.absNorm I ^ 2
      ≤ 2 * (Module.finrank ℚ E) ^ 2 * Ideal.absNorm M * Ideal.absNorm I ^ 2 :=
        Nat.mul_le_mul hS' le_rfl
    _ = 2 * (Module.finrank ℚ E) ^ 2 * (Algebra.norm ℤ m).natAbs := by rw [hNm]; ring

end Formalism.L2.SG.NGCut.TorsionTotientBound
end
end

