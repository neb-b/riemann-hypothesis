module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2954
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0493
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAdicSumAtImageOfZeroPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1436
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicImageNotOntoModConjIdeal
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.CoisBar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem cois_dvd (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) {n : ℕ} (hn : 0 < n) (hc : Cois D y n) {p : ℕ} (hpn : p ∣ n) (a : D.La)
    (ha : ∀ b, (∃ e, y b = p • e) → (p : ℤ) ∣ D.EF a b) : ∃ e, y a = p • e := by
  obtain ⟨k, rfl⟩ := hpn
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨e, he⟩ := hc.2 (k • a) fun b ⟨e, he⟩ => by
    obtain ⟨c, hc'⟩ := ha b ⟨k • e, by rw [he, mul_smul]⟩
    exact ⟨c, by rw [map_nsmul, LinearMap.smul_apply, hc', nsmul_eq_mul]; push_cast; ring⟩
  refine ⟨e, ?_⟩
  have h2 : (k : ℤ) • (y a - p • e) = 0 := by
    rw [natCast_zsmul, smul_sub, ← map_nsmul, he, smul_smul, mul_comm k p, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd (by exact_mod_cast h) hk
  · exact sub_eq_zero.1 h

theorem exists_pair (D : Datum H) {p : ℕ} (hp : p.Prime) (S : AddSubgroup D.La) (hpS : ∀ x : D.La, p • x ∈ S)
    {c : D.La} (hc : c ∉ S) : ∃ a : D.La, (∀ b ∈ S, (p : ℤ) ∣ D.EF a b) ∧ ¬ (p : ℤ) ∣ D.EF a c := by
  haveI := Fact.mk hp
  letI : Module (ZMod p) (D.La ⧸ S) := AddCommGroup.zmodModule (fun x => by
    induction x using QuotientAddGroup.induction_on with
    | H x => rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]; exact hpS x)
  have hc' : (QuotientAddGroup.mk c : D.La ⧸ S) ≠ 0 := by rwa [Ne, QuotientAddGroup.eq_zero_iff]
  obtain ⟨f, hf⟩ : ∃ f : (D.La ⧸ S) →+ ZMod p, f (QuotientAddGroup.mk c) ≠ 0 := by
    by_contra hne
    push_neg at hne
    refine hc' ((Module.forall_dual_apply_eq_zero_iff (ZMod p) _).1 fun φ => ?_)
    exact hne (LinearMap.toAddMonoidHom φ)
  let g : D.La →+ ZMod p := f.comp (QuotientAddGroup.mk' S)
  haveI := datum_finite_int D
  haveI := datum_isTorsionFree_int D
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let bs := Module.Free.chooseBasis ℤ D.La
  let G : D.La →ₗ[ℤ] ℤ := bs.constr ℤ (fun i => ((g (bs i)).val : ℤ))
  have hG : ∀ x, ((G x : ℤ) : ZMod p) = g x := by
    have : (Int.castAddHom (ZMod p)).toIntLinearMap.comp G = g.toIntLinearMap := bs.ext fun i => by
      simp [G, Module.Basis.constr_basis]
    intro x
    exact LinearMap.congr_fun this x
  obtain ⟨a, ha⟩ := D.unimod.2 G
  refine ⟨a, fun b hb => ?_, fun hdvd => hf ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ha, hG]
    show f (QuotientAddGroup.mk b) = 0
    rw [(QuotientAddGroup.eq_zero_iff b).2 hb, map_zero]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ha, hG] at hdvd
    exact hdvd

variable {D : Datum H} {Z Z' : Submodule (𝓞 E) D.La}

theorem mem_nsmul_of_dvd (h : IsOpp D Z Z') {p : ℕ} (hp : 0 < p) {z : D.La} (hz : z ∈ Z)
    (hd : ∀ b ∈ Z', (p : ℤ) ∣ D.EF z b) : ∃ w ∈ Z, z = p • w := by
  choose c hc using fun b : Z' => hd b b.2
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  let φ : Z' →+ ℤ := AddMonoidHom.mk' c fun x x' =>
    mul_left_cancel₀ hp' (by rw [mul_add, ← hc, ← hc, ← hc, Submodule.coe_add, map_add (f := _)])
  obtain ⟨w, hw, -⟩ := h.2.2.2 φ
  refine ⟨w, w.2, ?_⟩
  have : z - p • (w : D.La) = 0 := h.symm.eq_zero (sub_mem hz (Z.nsmul_mem w.2 p)) fun b hb => by
    have := hw ⟨b, hb⟩
    simp only [AddMonoidHom.mk'_apply, φ] at this
    rw [map_sub, LinearMap.sub_apply, map_nsmul, LinearMap.smul_apply, this, hc ⟨b, hb⟩, nsmul_eq_mul, sub_self]
  exact sub_eq_zero.1 this

end GlobalTheory.LowFilt.CoisBar

namespace GlobalTheory.LowFilt.CoisBar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem mem_nsmul_of_img_eq_top (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔮 : Ideal (𝓞 E)) (h𝔮 : 𝔮.IsMaximal)
    (htop : img D y Z' 𝔮 = ⊤) {p : ℕ} {b : D.La} (hb : b ∈ Z') (hyb : ∃ e, y b = p • e)
    (hq : ∀ t ∈ 𝔮, ∃ e ∈ Z', t • b = p • e) : ∃ e ∈ Z', b = p • e := by
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨r, hr1, hrX⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := 𝔮) (N := Z'.map y)
    (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl (le_of_eq htop.symm)
  have hr0 : r ∉ 𝔮 := fun h' => h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h' hr1))
  have hrx : ∀ x : X, ∃ k ∈ Z', y k = r • x := fun x =>
    Submodule.mem_map.1 (hrX (Submodule.smul_mem_pointwise_smul x r ⊤ trivial))
  have hinj : ∀ k ∈ Z', y k = 0 → k = 0 := by
    obtain ⟨hZf', hZn'⟩ := sub_free_finite D Z'
    have hrank : Module.finrank ℤ Z' = Module.finrank ℤ X := by
      obtain ⟨hZf, hZn⟩ := sub_free_finite D Z
      rw [h.finrank_int_eq, GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E Z,
        GlobalTheory.finrank_int_eq_finrank_ringOfIntegers_mul E X, hr]
    have hr00 : r ≠ 0 := fun h0 => hr0 (h0 ▸ 𝔮.zero_mem)
    set N := Ideal.absNorm (Ideal.span {r}) with hN
    have hN0 : N ≠ 0 := by
      rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hr00
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {r}))
    let g : Z' →ₗ[ℤ] X := (y.restrictScalars ℤ).comp (Z'.subtype.restrictScalars ℤ)
    have hmem : ∀ x : X, (N • LinearMap.id : X →ₗ[ℤ] X) x ∈ LinearMap.range g := fun x => by
      obtain ⟨k, hk, hyk⟩ := hrx (s • x)
      refine ⟨⟨k, hk⟩, ?_⟩
      show y k = N • x
      rw [hyk, smul_smul, mul_comm, hs, Nat.cast_smul_eq_nsmul]
    let m : X →ₗ[ℤ] LinearMap.range g := LinearMap.codRestrict _ (N • LinearMap.id) hmem
    have hm : Function.Injective m := fun x x' hxx => by
      have h1 : (N : ℤ) • (x - x') = 0 := by
        have : N • x = N • x' := congrArg Subtype.val hxx
        rw [natCast_zsmul, smul_sub, this, sub_self]
      rcases smul_eq_zero.1 h1 with h2 | h2
      · exact absurd (by exact_mod_cast h2) hN0
      · exact sub_eq_zero.1 h2
    have h1 := LinearMap.rank_le_of_injective m hm
    have h2 := LinearMap.rank_range_add_rank_ker g
    have h3 := rank_range_le g
    rw [← Module.finrank_eq_rank (R := ℤ) (M := X)] at h1
    rw [← Module.finrank_eq_rank (R := ℤ) (M := Z'), hrank] at h2 h3
    have h4 : Module.rank ℤ (LinearMap.range g) = Module.finrank ℤ X := le_antisymm h3 h1
    rw [h4] at h2
    have h5 : Module.rank ℤ (LinearMap.ker g) = 0 := by
      obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 (lt_of_le_of_lt (le_add_self.trans h2.le) Cardinal.natCast_lt_aleph0)
      rw [hk] at h2 ⊢
      norm_cast at h2 ⊢
      omega
    intro k hk hyk
    obtain ⟨a, ha0, hak⟩ := (rank_eq_zero_iff.1 h5) ⟨⟨k, hk⟩, hyk⟩
    have : a • (⟨k, hk⟩ : Z') = 0 := congrArg Subtype.val hak
    rcases smul_eq_zero.1 this with h' | h'
    · exact absurd h' ha0
    · exact congrArg Subtype.val h'
  obtain ⟨x, hx⟩ := hyb
  obtain ⟨b'', hb'', hyb''⟩ := hrx x
  have hrb : r • b = p • b'' := sub_eq_zero.1 (hinj _ (sub_mem (Z'.smul_mem r hb) (Z'.nsmul_mem hb'' p))
    (by rw [map_sub, map_smul, map_nsmul, hx, hyb'', smul_comm r p x, sub_self]))
  obtain ⟨c, u, hu, hcu⟩ := h𝔮.exists_inv hr0
  obtain ⟨e, he, hue⟩ := hq u hu
  refine ⟨c • b'' + e, add_mem (Z'.smul_mem c hb'') he, ?_⟩
  calc b = (c * r + u) • b := by rw [hcu, one_smul]
    _ = p • (c • b'' + e) := by rw [add_smul, mul_smul, hrb, hue, smul_add, smul_comm c p]

end GlobalTheory.LowFilt.CoisBar

namespace GlobalTheory.LowFilt.CoisBar

theorem img_bar_ne_top : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ := by
  intro E _ _ _ H D X _ _ _ _ y n hn hc Z Z' h hr 𝔭 h𝔭 hn𝔭 hi hL htop
  obtain ⟨p, hp, hp𝔭, hpn⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ 𝔭 ∧ p ∣ n := by
    letI := Ideal.Quotient.field 𝔭
    obtain ⟨p, hch⟩ := CharP.exists (𝓞 E ⧸ 𝔭)
    have hn0 : Ideal.Quotient.mk 𝔭 (n : 𝓞 E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hn𝔭
    rw [map_natCast] at hn0
    have hpn : p ∣ n := (CharP.cast_eq_zero_iff (𝓞 E ⧸ 𝔭) p n).1 hn0
    have hp : p.Prime := (CharP.char_is_prime_or_zero (𝓞 E ⧸ 𝔭) p).resolve_right (by
      rintro rfl
      rw [zero_dvd_iff] at hpn
      omega)
    refine ⟨p, hp, Ideal.Quotient.eq_zero_iff_mem.1 ?_, hpn⟩
    rw [map_natCast]
    exact CharP.cast_eq_zero _ p
  have hp0 := hp.pos
  have hsmA : ∀ t ∈ 𝔭, ∀ x : X, t • x ∈ img D y Z' 𝔭 := fun t ht x =>
    Submodule.mem_sup_right (Submodule.smul_mem_smul ht trivial)
  have hpA : ∀ x : X, p • x ∈ img D y Z' 𝔭 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hsmA _ hp𝔭 x
  obtain ⟨c0, hc0⟩ : ∃ c, y c ∉ img D y Z' 𝔭 := by
    by_contra hne
    push_neg at hne
    apply hi
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, e, he⟩ := hc.1 x
    have : x = y a - n • e := by rw [he, add_sub_cancel_right]
    rw [this]
    refine sub_mem (hne a) ?_
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact hsmA _ hn𝔭 e
  obtain ⟨a, ha, hac⟩ := exists_pair D hp ((img D y Z' 𝔭).toAddSubgroup.comap y.toAddMonoidHom)
    (fun x => by
      show y (p • x) ∈ img D y Z' 𝔭
      rw [map_nsmul]
      exact hpA _) (c := c0) hc0
  replace ha : ∀ b, y b ∈ img D y Z' 𝔭 → (p : ℤ) ∣ D.EF a b := fun b hb => ha b hb
  have hya : ∃ e, y a = p • e := cois_dvd D y hn hc hpn a fun b ⟨e, he⟩ => ha b (by rw [he]; exact hpA e)
  have hbar : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), H.bar t ∈ 𝔭 := fun t ht => by
    rw [Ideal.map_comap_of_equiv, Ideal.mem_comap] at ht
    have : H.bar.symm t = H.bar t := by
      apply H.bar.injective
      rw [RingEquiv.apply_symm_apply, bar_bar]
    rwa [← this]
  have hta : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), ∃ e, t • a = p • e := fun t ht =>
    GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hp0 _ fun c => by
      rw [D.adj]
      apply ha
      rw [map_smul]
      exact hsmA _ (hbar t ht) _
  obtain ⟨z, hz, m, hm, b', hb', rfl⟩ := h.exists_decomp a
  obtain ⟨w1, -, hw1⟩ := mem_nsmul_of_dvd h hp0 hz fun b hb => by
    have := ha b (Submodule.mem_sup_left (Submodule.mem_map_of_mem hb))
    rwa [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hm.2 b hb, h.2.1 hb' b hb, add_zero,
      add_zero] at this
  obtain ⟨w2, hw2⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hp0 m fun c => by
    obtain ⟨zc, hzc, mc, hmc, bc, hbc, rfl⟩ := h.exists_decomp c
    have h1 := ha mc (hL (Submodule.mem_map_of_mem hmc))
    have e1 : D.EF z mc = 0 := by rw [ef_swap, hmc.1 z hz, neg_zero]
    have e2 : D.EF b' mc = 0 := by rw [ef_swap, hmc.2 b' hb', neg_zero]
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, e1, e2, zero_add, add_zero] at h1
    rwa [map_add, map_add, hm.1 zc hzc, hm.2 bc hbc, zero_add, add_zero]
  have hzm : z + m = p • (w1 + w2) := by rw [hw1, hw2, smul_add]
  have hyb : ∃ e, y b' = p • e := by
    obtain ⟨e, he⟩ := hya
    refine ⟨e - y (w1 + w2), ?_⟩
    calc y b' = y (z + m + b') - y (z + m) := by rw [map_add y (z + m) b', add_sub_cancel_left]
      _ = p • (e - y (w1 + w2)) := by rw [he, hzm, map_nsmul, smul_sub]
  have hq : ∀ t ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E), ∃ e ∈ Z', t • b' = p • e := fun t ht => by
    obtain ⟨e, he⟩ := hta t ht
    have h1 : t • b' = p • (e - t • (w1 + w2)) := by
      calc t • b' = t • (z + m + b') - t • (z + m) := by rw [smul_add t (z + m) b', add_sub_cancel_left]
        _ = p • (e - t • (w1 + w2)) := by rw [he, hzm, smul_comm t p, smul_sub]
    refine ⟨_, (h.symm.isIsoSat).2 p _ hp.ne_zero ?_, h1⟩
    rw [← h1]
    exact Z'.smul_mem t hb'
  haveI := Ideal.map_isMaximal_of_equiv H.bar (p := 𝔭)
  obtain ⟨e, -, he⟩ := mem_nsmul_of_img_eq_top D y Z Z' h hr _ this htop hb' hyb hq
  apply hac
  rw [hzm, he, ← smul_add, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact dvd_mul_right _ _

end GlobalTheory.LowFilt.CoisBar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KltOfAdjunctionKltLocalModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

section Transport

variable {k K K' : Type} [Field k] [Field K] [Field K'] {c : k →+* K} {c' : k →+* K'}

theorem Place.contains_map_iff (e : K ≃+* K') (E : Place c) (E' : Place c')
    (hring : ∀ a, e a ∈ E'.ring ↔ a ∈ E.ring) (R : Subring K) :
    E'.Contains (R.map e.toRingHom) ↔ E.Contains R := by
  constructor
  · intro h f hf
    exact (hring f).1 (h _ ⟨f, hf, rfl⟩)
  · rintro h _ ⟨f, hf, rfl⟩
    exact (hring f).2 (h f hf)

theorem Place.isPrimeOf_map_iff (e : K ≃+* K') (E : Place c) (E' : Place c')
    (hring : ∀ a, e a ∈ E'.ring ↔ a ∈ E.ring) (hord : ∀ a, E'.ord (e a) = E.ord a)
    (R : Subring K) : E'.IsPrimeOf (R.map e.toRingHom) ↔ E.IsPrimeOf R := by
  rw [Place.IsPrimeOf, Place.IsPrimeOf, Place.contains_map_iff e E E' hring]
  refine and_congr_right fun _ => ⟨fun h f hf => ?_, fun h f' hf' => ?_⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, hb0, hbo, hfb⟩ := h (e f) ((hring f).2 hf)
    refine ⟨a, ha, b, hb, fun h0 => hb0 (by simp [h0]), (hord b).symm.trans hbo, e.injective ?_⟩
    simpa using hfb
  · obtain ⟨a, ha, b, hb, hb0, hbo, hfb⟩ := h (e.symm f') ((hring _).1 (by simpa using hf'))
    refine ⟨e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, by simpa using hb0, (hord b).trans hbo, ?_⟩
    rw [← hfb]
    simp

theorem adjKlt_congr {n : ℕ} {T : Subring K} {S : Place c} {η : Forms c n} {φ ψ : K →₀ ℚ}
    (hφ : φ 0 = 0) (hψ : ψ 0 = 0)
    (h : ∀ P : Place c, P.ordQ φ = P.ordQ ψ) : AdjKlt c n T S η φ ↔ AdjKlt c n T S η ψ := by
  have h' : ∀ P : Place c, P.disc η φ = P.disc η ψ := fun P => by rw [Place.disc, Place.disc, h]
  simp only [AdjKlt, h', hφ, hψ]

end Transport

theorem klt_of_adjKlt_locModel : GlobalTheory.Published.Principalisation → ∀ {L : Type} [Field L] (c : ℂ →+* L)
    (n : ℕ) (T : Subring L) (x : Fin n → L) (φ : L →₀ ℚ) (f : L) (S : Place c), IsLocModel c T →
    IsIntegrallyClosed T → TrBasis c x → f ∈ T → f ≠ 0 → S.IsPrimeOf T → S.ord f = 1 →
    S.disc (dForm c x) φ = 0 → EffAt c n T (dForm c x) φ →
    AdjKlt c n T S (dForm c x) (φ + Finsupp.single f 1) → Klt c n T (dForm c x) φ := by
  intro hP L _ c n T x φ f S hT hTic hx hfT hf0 hS hSf hSd hEff hAdj
  obtain ⟨Y, hY, p, e, y, hproj, hdim, hc, hy⟩ := _root_.GlobalTheory.LocModelProj.exists_projective_of_isLocModel L c T n x hT hx
  haveI := hY
  haveI : LocallyOfFiniteType p := GlobalTheory.isProjOver_locallyOfFiniteType ℂ Y p hproj
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have hc' : ∀ a, e.symm (c a) = Cartier.constFn p a := fun a => by
    rw [← hc a]
    exact e.symm_apply_apply _
  have hyT : T.map e.symm.toRingHom = locRing y := by
    rw [← hy]
    ext z
    simp [Subring.mem_map]
  obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.FieldPair.placeEquiv_ringEquiv c (Cartier.constFn p) e.symm hc'
  obtain ⟨hx', -, -, -⟩ := GlobalTheory.T.ringEquiv_transports_varietyPair_data c (Cartier.constFn p) e.symm hc' n x T φ hx
  have hψ0 : (φ + Finsupp.single f 1 : L →₀ ℚ) 0 = 0 := by
    simp [hEff.apply_zero, Finsupp.single_apply, hf0]
  obtain ⟨m, g, hm, hg⟩ := _root_.GlobalTheory.FieldPair.exists_ordQ_eq_ord_div (Cartier.constFn p)
    (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) (by
      rw [← map_zero e.symm, Finsupp.mapDomain_apply_of_injective e.symm.injective]
      exact hψ0)

  have hkey : ∀ E : Place c, (Φ E).disc (dForm (Cartier.constFn p) (e.symm ∘ x))
      (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) =
      E.disc (dForm c x) (φ + Finsupp.single f 1) := fun E => by
    rw [Place.disc, Place.disc, (hΦ E).2.2.1, (hΦ E).2.2.2 n x hx]
    rfl
  have hψ : ∀ E : Place c, E.disc (dForm c x) (φ + Finsupp.single f 1) =
      E.disc (dForm c x) φ - E.ord f := fun E => by
    simp only [Place.disc, map_add (f := _), Place.ordQ_single]
    ring
  have hordQ : ∀ P : Place (Cartier.constFn p),
      P.ordQ (Finsupp.mapDomain e.symm (φ + Finsupp.single f 1)) =
      P.ordQ (Finsupp.single (g : Y.functionField) (1 / (m : ℚ))) := fun P => by
    rw [hg, Place.ordQ_single]
    ring
  have hdisc : ∀ D : DivOver p, discrep D (dForm (Cartier.constFn p) (e.symm ∘ x)) m g =
      (Φ.symm (placeEquiv p D)).disc (dForm c x) (φ + Finsupp.single f 1) := fun D => by
    rw [← disc_placeEquiv, ← hkey, Φ.apply_symm_apply, Place.disc, Place.disc, hordQ]
  let f' : Y.functionFieldˣ := Units.mk0 (e.symm f) (by simpa using hf0)
  have hord : ∀ D : DivOver p, (D.ord f' : ℚ) = (Φ.symm (placeEquiv p D)).ord f := fun D => by
    rw [← ord_placeEquiv]
    have h := (hΦ (Φ.symm (placeEquiv p D))).2.1 f
    rw [Φ.apply_symm_apply] at h
    exact_mod_cast h

  have hstalk : IsIntegrallyClosed (Y.presheaf.stalk y) := by
    let e₁ : Y.presheaf.stalk y ≃+* locRing y := RingEquiv.ofBijective
      (algebraMap (Y.presheaf.stalk y) Y.functionField).rangeRestrict
      ⟨fun _ _ h => IsFractionRing.injective _ Y.functionField (congrArg Subtype.val h),
        RingHom.rangeRestrict_surjective _⟩
    have : IsIntegrallyClosed (locRing y) := IsIntegrallyClosed.of_equiv
      ((T.equivMapOfInjective e.symm.toRingHom e.symm.injective).trans
        (RingEquiv.subringCongr hyT))
    exact IsIntegrallyClosed.of_equiv e₁.symm
  have hreg : RegAt y (f' : Y.functionField) := by
    rw [← mem_locRing, ← hyT]
    exact ⟨f, hfT, rfl⟩
  have hSprime : (placeEquiv p ((placeEquiv p).symm (Φ S))).IsPrimeOf (locRing y) := by
    rw [Equiv.apply_symm_apply, ← hyT]
    exact (Place.isPrimeOf_map_iff e.symm S (Φ S) (hΦ S).1 (hΦ S).2.1 T).2 hS
  have hSord : ((placeEquiv p).symm (Φ S)).ord f' = 1 := by
    have h := hord ((placeEquiv p).symm (Φ S))
    rw [Equiv.apply_symm_apply, Φ.symm_apply_apply, hSf] at h
    exact_mod_cast h
  have hSdisc : discrep ((placeEquiv p).symm (Φ S)) (dForm (Cartier.constFn p) (e.symm ∘ x)) m g
      = -1 := by
    rw [hdisc, Equiv.apply_symm_apply, Φ.symm_apply_apply, hψ, hSd, hSf]
    norm_num
  have heff : ∀ D : DivOver p, (placeEquiv p D).IsPrimeOf (locRing y) →
      discrep D (dForm (Cartier.constFn p) (e.symm ∘ x)) m g ≤ 0 := by
    intro D hD
    have hE : (Φ.symm (placeEquiv p D)).IsPrimeOf T := by
      refine (Place.isPrimeOf_map_iff e.symm _ (Φ (Φ.symm (placeEquiv p D)))
        (hΦ _).1 (hΦ _).2.1 T).1 ?_
      rw [Φ.apply_symm_apply, hyT]
      exact hD
    have h0 : (0 : ℚ) ≤ (Φ.symm (placeEquiv p D)).ord f := by
      exact_mod_cast ((Φ.symm (placeEquiv p D)).ord_nonneg_iff hf0).2 (hE.1 f hfT)
    rw [hdisc, hψ]
    linarith [hEff.disc_le hE]
  have hadj : AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p ((placeEquiv p).symm (Φ S)))
      (dForm (Cartier.constFn p) (e.symm ∘ x)) (Finsupp.single (g : Y.functionField) (1 / (m : ℚ))) := by
    rw [Equiv.apply_symm_apply, ← hyT]
    have h := _root_.GlobalTheory.FieldPair.adjKlt_ringEquiv c (Cartier.constFn p) e.symm hc' n x T _ S (Φ S) hx (hΦ S).1 hAdj
    exact (adjKlt_congr h.apply_zero (Finsupp.single_eq_of_ne g.ne_zero.symm) hordQ).1 h
  have hmain := _root_.GlobalTheory.inversion_of_adjunction_proj hP Y p n hproj hdim (e.symm ∘ x) m g f' y ((placeEquiv p).symm (Φ S))
    hx' hm hstalk hreg hSprime hSord hSdisc heff hadj
  refine ⟨hEff.form_ne_zero, hEff.apply_zero, fun E hE => ?_⟩
  have hThr : ((placeEquiv p).symm (Φ E)).Through y := by
    rw [← contains_placeEquiv, Equiv.apply_symm_apply, ← hyT]
    exact (Place.contains_map_iff e.symm E (Φ E) (hΦ E).1 T).2 hE
  have h := hmain _ hThr
  rw [hdisc, hord, Equiv.apply_symm_apply, Φ.symm_apply_apply, hψ] at h
  linarith

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeClassZeroOfMemberTerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.GSep.TermsLabel

theorem yy_zero_of_terms : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : X → C → V), 𝔪.Terms x₀ lab T → ∀ c, 𝔪.YY (lab c) 0 := by
  intro I X₁ z₁ act x₀ V _ _ _ ev X _ t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, -, hw₀, -, hg, -⟩ := hT
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨⟨o, ho₁, ho₂⟩, hwc, hov⟩ := hg c
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (FractionRing V)
  letI := GlobalTheory.TorusExt.gtGroup 𝔪.D.toPre (AlgebraicClosure (FractionRing V))
  have hkg : (X₁.S.r * X₁.S.N) • g' c = 0 :=
    ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho₁).symm.trans ((GlobalTheory.TorusExt.isZero_iff_eq _).1 ho₂)
  set gb := GlobalTheory.TorusExt.gtExt 𝔪.D.toPre (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))
    (RingHom.comp_id _) (g' c) with hgb
  have hkgb : (X₁.S.r * X₁.S.N) • gb = 0 := by
    rw [hgb, ← map_nsmul, hkg, map_zero]

  have hi : GtPtF.IsIota 0 (0 : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V))) := by
    have hz := (GlobalTheory.TorusExt.isZero_iff_eq (0 : GtPtF 𝔪.D.toPre (AlgebraicClosure (FractionRing V)))).2 rfl
    obtain ⟨hb, hv⟩ := (GlobalTheory.TorusExt.isZero_iff_val _).1 hz
    refine (GlobalTheory.TorusExt.isIota_iff_val 0 _).2 ⟨hb.trans (cPoint_zero _).symm, fun χ y J hJ => ?_⟩
    have C : IsCub (DVR.th 𝔪.D.toPre (T := TF (R := V) (AlgebraicClosure (FractionRing V))) y J) := isCub_cubV 𝔪.D.toPre.cub hJ
    have tt := tau_mul (𝟙 (TF (R := V) (AlgebraicClosure (FractionRing V)))) hJ hB 0 0 χ
    rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at tt
    exact (hv χ y J hJ).trans (mul_eq_left.1 tt.symm).symm
  let p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) :=
    ⟨0, gb, 0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 hkgb.symm, hi⟩
  let xb : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A :=
    GlobalTheory.TorsionExt.fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ x (lab c)
  obtain ⟨wb, frb, hwb, hfrb, hlb⟩ := GlobalTheory.T.torusExtension_point_liesOver_after_field_extension V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀
    hw₀ (g' c) (w c) (x (lab c)) (fr (lab c)) hwc (hfr _).1 hov xb rfl

  obtain ⟨f', f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have hq := (f₁ p (f' p)).2 rfl
  obtain ⟨w', fr', hw', hfr', hl'⟩ := GlobalTheory.Poinc.Tors.ValPair.liesOver_of_qkToAkU V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V))
    w₀ hw₀ _ hk p (f' p) rfl hq

  have e := GlobalTheory.Poinc.Tors.OneOver.eq_of_liesOver hL V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U (AlgebraicClosure (FractionRing V)) w₀ hw₀ p.g wb w' xb
    (f' p) frb fr' hwb hw' hfrb hfr' hlb hl'
  refine ⟨p, xb, (map_zero 𝔪.e₈).symm, e ▸ hq, ?_⟩
  have e₁ : spMap (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) :=
    (Spec.map_comp (CommRingCat.ofHom 𝔪.yK) (CommRingCat.ofHom (algebraMap _ _))).symm
  rw [← e₁, Category.assoc, ← hx (lab c)]
  rfl

end GlobalTheory.GSep.TermsLabel
end
end

