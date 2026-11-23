module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqNsmulOfForallDvdOfBijective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsMonogenicSeparating
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootMulComplexConjEqOne
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_mul_complexConj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E]
    (x : E) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) : x * IsCMField.complexConj E x = 1 := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  have h1 : ‖φ x‖ = 1 := by
    have h : ‖φ x‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, hx, map_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  rw [map_mul, IsCMField.complexEmbedding_complexConj, map_one, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h1]
  simp

theorem root_eq_one_of_halfLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → ∀ (I : Ideal (𝓞 E)) (M : ℕ), 3 ≤ M → I * I.map (bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(M : 𝓞 E)} → I ⊔ I.map (bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∀ (u : 𝓞 E) (n : ℕ), 0 < n → u ^ n = 1 → u - 1 ∈ I → u = 1 := by
  intro E _ _ _ bar hbar I M hM hI hco u n hn hu h1
  have hub : u * bar u = 1 := by
    apply RingOfIntegers.ext
    have hx : (u : E) ^ n = 1 := by
      have := congrArg (fun a : 𝓞 E => (a : E)) hu
      simpa using this
    have := root_mul_complexConj_eq_one (u : E) n hn hx
    rw [← hbar] at this
    simpa using this
  have h2 : bar u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (bar : 𝓞 E →+* 𝓞 E) h1
    simpa using this
  have h3 : u - 1 ∈ I.map (bar : 𝓞 E →+* 𝓞 E) := by
    have e : u - 1 = (-u) * (bar u - 1) := by linear_combination hub
    rw [e]
    exact Ideal.mul_mem_left _ _ h2
  have h4 : u - 1 ∈ Ideal.span {(M : 𝓞 E)} := by
    rw [← hI, Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.2 hco)]
    exact ⟨h1, h3⟩
  exact GlobalTheory.CompanionTheory.Ar.Flat.root_of_unity_eq_one_of_dvd_sub_one E u n M hn hu hM (Ideal.mem_span_singleton.1 h4)

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SaturatedLatticeQuotientCount
section
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mem_of_forall_exists_sub_eq_nsmul (Λ : Type) [AddCommGroup Λ] [Module.Finite ℤ Λ]
    (W : Submodule ℤ Λ) (hW : ∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) (x : Λ)
    (h : ∀ N : ℕ, 0 < N → ∃ w ∈ W, ∃ b : Λ, x - w = N • b) : x ∈ W := by
  have htf : Module.IsTorsionFree ℤ (Λ ⧸ W) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective W m
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hrm
      exact (Submodule.Quotient.mk_eq_zero W).mpr (hW r y hr hrm)
  have hfree : Module.Free ℤ (Λ ⧸ W) := Module.free_iff_isTorsionFree.mpr htf
  let bs := Module.Free.chooseBasis ℤ (Λ ⧸ W)
  rw [← Submodule.Quotient.mk_eq_zero W]
  refine bs.repr.injective ?_
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  obtain ⟨w, hw, b, hb⟩ := h ((bs.repr (Submodule.Quotient.mk x) i).natAbs + 1) (by omega)
  generalize hn : (bs.repr (Submodule.Quotient.mk x) i).natAbs = n at hb
  have hq : (Submodule.Quotient.mk x : Λ ⧸ W) = (n + 1) • Submodule.Quotient.mk b := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← hb]
    simpa using hw
  have hc : bs.repr (Submodule.Quotient.mk x) i =
      ((n + 1 : ℕ) : ℤ) * bs.repr (Submodule.Quotient.mk b) i := by
    rw [hq, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  have habs := congrArg Int.natAbs hc
  rw [Int.natAbs_mul, Int.natAbs_natCast, hn] at habs
  rcases Nat.eq_zero_or_pos (bs.repr (Submodule.Quotient.mk b) i).natAbs with ht | ht
  · rw [ht, mul_zero] at habs
    rw [habs] at hn
    exact Int.natAbs_eq_zero.mp hn
  · nlinarith

theorem mem_of_forall_card_mul_eq_pow :
    ∀ (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
      (B : LinearMap.BilinForm ℤ Λ), Function.Bijective B → (∀ x, B x x = 0) →
      ∀ W : Submodule ℤ Λ, (∀ (k : ℤ) x, k ≠ 0 → k • x ∈ W → x ∈ W) →
      (∀ N : ℕ, 0 < N →
        ∃ T : Set (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))),
          Nat.card (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) * Nat.card T
            = N ^ Module.finrank ℤ Λ ∧
          ∀ x y : W, Submodule.Quotient.mk x ∈ T → (N : ℤ) ∣ B x y) →
      ∀ x, (∀ y ∈ W, B x y = 0) → x ∈ W := by
  intro Λ _ _ _ B hB halt W hW hT x hx
  apply mem_of_forall_exists_sub_eq_nsmul Λ W hW x
  intro N hN
  obtain ⟨T, hcard, hTpair⟩ := hT N hN
  let R : Λ → (W ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : W →ₗ[ℤ] W))) → Prop :=
    fun a p => ∃ w : W, Submodule.Quotient.mk w = p ∧ ∃ b : Λ, a - w = N • b
  have h1 : ∀ a b p, R a p → R (a + N • b) p := by
    rintro a b p ⟨w, hw, b0, hb0⟩
    refine ⟨w, hw, b0 + b, ?_⟩
    rw [smul_add, ← hb0]
    abel
  have h2 : ∀ a p p', R a p → R a p' → p = p' := by
    rintro a p p' ⟨w, rfl, b, hb⟩ ⟨w', rfl, b', hb'⟩
    have hdiff : ((w : Λ) - w') = (N : ℤ) • (b' - b) := by
      rw [natCast_zsmul, smul_sub, ← hb, ← hb']
      abel
    have hmem : b' - b ∈ W :=
      hW (N : ℤ) (b' - b) (by exact_mod_cast hN.ne') (by rw [← hdiff]; exact W.sub_mem w.2 w'.2)
    rw [Submodule.Quotient.eq]
    refine ⟨⟨b' - b, hmem⟩, ?_⟩
    apply Subtype.ext
    exact hdiff.symm
  have h3 : ∀ p, ∃ a, R a p := by
    intro p
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    exact ⟨w, w, rfl, 0, by simp⟩
  have h4 : ∀ a p a' p', R a p → p ∈ T → R a' p' → (N : ℤ) ∣ B a a' := by
    rintro a p a' p' ⟨w, rfl, b, hb⟩ hp ⟨w', -, b', hb'⟩
    have ha : a = w + N • b := by rw [← hb]; abel
    have ha' : a' = w' + N • b' := by rw [← hb']; abel
    have hww := hTpair w w' hp
    have hexp : B (↑w + N • b) (↑w' + N • b') = B w w' + N * (B w b' + B b w' + N * B b b') := by
      simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      ring
    rw [ha, ha', hexp]
    exact dvd_add hww (dvd_mul_right _ _)
  have h5 : ∀ a' p', R a' p' → (N : ℤ) ∣ B x a' := by
    rintro a' p' ⟨w', -, b', hb'⟩
    have ha' : a' = w' + N • b' := by rw [← hb']; abel
    rw [ha', map_add (f := _), map_nsmul, hx w' w'.2, zero_add]
    exact ⟨B x b', nsmul_eq_mul _ _⟩
  obtain ⟨p, w, -, b, hwb⟩ :=
    GlobalTheory.exists_rel_of_forall_dvd_of_card_mul Λ B hB N hN _ T R h1 h2 h3 hcard h4 x h5
  exact ⟨w, w.2, b, hwb⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SmulMemSpanOver
section
namespace GlobalTheory.CompanionTheory.Ar.Num.SpanExact

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω]
  {E E₂ : Type*} [AddCommGroup E] [Module Ω E] [AddCommGroup E₂] [Module Ω E₂]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {v : E}
    (hv : v ∈ spanOver R S) : a • v ∈ spanOver R S := by
  unfold spanOver at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, R.mul_mem ha hb, e, he, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem map_spanOver (R : Subalgebra o Ω) (S : Set E) (q : E →ₗ[Ω] E₂) :
    (spanOver R S).map q.toAddMonoidHom = spanOver R (q '' S) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, e, he, rfl⟩, rfl⟩
    exact ⟨a, ha, q e, ⟨e, he, rfl⟩, by simp⟩
  · rintro ⟨a, ha, _, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨a • e, ⟨a, ha, e, he, rfl⟩, by simp⟩

theorem local_step (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (f : Ω) (hf : f ∈ R) (b : Fin r → E₂)
    (hb : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = ⊤)
    (hloc : ∀ e, (∃ n : ℕ, f ^ n • e ∈ L.map q.toAddMonoidHom) ↔
        ∃ a : Fin r → Ω, (∀ j, ∃ n : ℕ, f ^ n * a j ∈ R) ∧ e = ∑ j, a j • b j)
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    ∃ m : ℕ, f ^ m • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  classical
  have h1 : ∀ j, ∃ n : ℕ, ∃ s ∈ L, q s = f ^ n • b j := by
    intro j
    obtain ⟨n, s, hs, hs'⟩ := (hloc (b j)).2 ⟨Pi.single j 1, fun k => ⟨0, by
      by_cases h : k = j
      · subst h; simpa using R.one_mem
      · simpa [h] using R.zero_mem⟩, by simp [Pi.single_apply]⟩
    exact ⟨n, s, hs, hs'⟩
  choose n s hs hqs using h1
  set N := ∑ j, n j with hN
  have hle : ∀ j, n j ≤ N := fun j =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let t : Fin r → E := fun j => f ^ (N - n j) • s j
  have ht : ∀ j, t j ∈ L := fun j => hL _ (R.pow_mem hf _) _ (hs j)
  have hqt : ∀ j, q (t j) = f ^ N • b j := fun j => by
    simp only [t, map_smul, hqs, smul_smul, ← pow_add, Nat.sub_add_cancel (hle j)]
  let B : Module.Basis (Fin r) Ω E₂ := Module.Basis.mk hb hsp.ge
  let σ : E₂ →ₗ[Ω] E := B.constr Ω t
  have hσ : ∀ j, σ (b j) = t j := fun j => by
    have : b j = B j := by simp [B]
    rw [this]; simp [σ]
  set S := spanOver R₁ {e | e ∈ L ∧ q e = 0} with hS
  have hup : ∀ (w : E) (m k : ℕ), f ^ m • w ∈ S → f ^ (k + m) • w ∈ S := fun w m k h => by
    rw [pow_add, mul_smul]
    exact smul_mem_spanOver R₁ _ (R₁.pow_mem (hR hf) _) h
  have key : ∃ m : ℕ, f ^ m • (f ^ N • v - σ (q v)) ∈ S := by
    clear hq
    unfold spanOver at hv
    induction hv using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, e, he, rfl⟩ := hx
      obtain ⟨c, hc, hce⟩ := (hloc (q e)).1 ⟨0, e, he, by simp⟩
      choose p hp using hc
      set M := ∑ j, p j with hM
      have hle' : ∀ j, p j ≤ M := fun j =>
        Finset.single_le_sum (f := p) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have hp' : ∀ j, f ^ M * c j ∈ R := fun j => by
        rw [← Nat.sub_add_cancel (hle' j), pow_add, mul_assoc]
        exact R.mul_mem (R.pow_mem hf _) (hp j)
      refine ⟨M, AddSubgroup.subset_closure ⟨a, ha, f ^ M • (f ^ N • e - σ (q e)), ⟨?_, ?_⟩, ?_⟩⟩
      · rw [smul_sub]
        refine sub_mem (hL _ (R.pow_mem hf _) _ (hL _ (R.pow_mem hf _) _ he)) ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hce, map_sum, Finset.smul_sum]
        refine sum_mem fun j _ => ?_
        rw [map_smul, smul_smul, hσ]
        exact hL _ (hp' j) _ (ht j)
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_smul, map_sub, map_smul, hce, map_sum, map_sum, Finset.smul_sum]
        simp only [map_smul, hσ, hqt]
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_zero, smul_zero]
        intro j _
        rw [smul_comm, sub_self]
      · simp only [map_smul]
        module
    | zero => exact ⟨0, by simpa using S.zero_mem⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨k, hk⟩ := hy
      refine ⟨k + m, ?_⟩
      have h2 := hup _ _ m hk
      rw [add_comm] at h2
      convert add_mem (hup _ _ k hm) h2 using 1
      simp only [map_add (f := _)]
      module
    | neg x _ hx =>
      obtain ⟨m, hm⟩ := hx
      refine ⟨m, ?_⟩
      convert neg_mem hm using 1
      simp only [map_neg]
      module
  obtain ⟨m, hm⟩ := key
  refine ⟨m + N, ?_⟩
  simpa [hq, smul_smul, pow_add] using hm

theorem mem_spanOver_ker (R R₁ : Subalgebra o Ω) (hR : R ≤ R₁) (q : E →ₗ[Ω] E₂) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {r : ℕ} (hF : LocFree R r (L.map q.toAddMonoidHom))
    {v : E} (hv : v ∈ spanOver R₁ (L : Set E)) (hq : q v = 0) :
    v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
  obtain ⟨-, k, f, c, hf, hc, hsum, hl⟩ := hF
  let J : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0}}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subalgebra.coe_add, add_smul] at ha hb ⊢
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at hb ⊢
        exact smul_mem_spanOver R₁ _ (hR a.2) hb }
  have h1 : (1 : R) ∈ J.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [hsum]
    rw [this]
    refine sum_mem fun l _ => Ideal.mul_mem_left _ _ ?_
    obtain ⟨b, hb, hsp, hloc⟩ := hl l
    obtain ⟨m, hm⟩ := local_step R R₁ hR q L hL (f l) (hf l) b hb hsp hloc hv hq
    exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := h1
  have : ((1 ^ m : R) : Ω) • v ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := hm
  simpa using this

theorem span_comap_exact : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R R₁ : Subalgebra o Ω), R ≤ R₁ → ∀ {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₂ : ℕ), (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) → LocFree R r₂ (L.map q.toAddMonoidHom) → (spanOver R₁ (L : Set E)).comap i.toAddMonoidHom = spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) ∧ (spanOver R₁ (L : Set E)).map q.toAddMonoidHom = spanOver R₁ (L.map q.toAddMonoidHom : Set E₂) := by
  intro o Ω _ _ _ R R₁ hR E E₁ E₂ _ _ _ _ _ _ i q hi hex L r₂ hL hF
  refine ⟨?_, ?_⟩
  · have himg : i '' (L.comap i.toAddMonoidHom : Set E₁) = {e | e ∈ L ∧ q e = 0} := by
      ext e
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩⟩
      · rintro ⟨he, hq⟩
        rw [← LinearMap.mem_ker, ← hex] at hq
        obtain ⟨x, rfl⟩ := hq
        exact ⟨x, he, rfl⟩
    have hmap := map_spanOver R₁ (L.comap i.toAddMonoidHom : Set E₁) i
    rw [himg] at hmap
    ext x
    constructor
    · intro hx
      have hq : q (i x) = 0 := by rw [← LinearMap.mem_ker, ← hex]; exact ⟨x, rfl⟩
      have := mem_spanOver_ker R R₁ hR q L hL hF (v := i x) hx hq
      rw [← hmap] at this
      obtain ⟨y, hy, hxy⟩ := this
      obtain rfl : y = x := hi hxy
      exact hy
    · intro hx
      have h1 : i x ∈ spanOver R₁ {e | e ∈ L ∧ q e = 0} := by
        rw [← hmap]; exact ⟨x, hx, rfl⟩
      have h2 : spanOver R₁ {e | e ∈ L ∧ q e = 0} ≤ spanOver R₁ (L : Set E) :=
        AddSubgroup.closure_mono fun w ⟨a, ha, e, he, hw⟩ => ⟨a, ha, e, he.1, hw⟩
      exact h2 h1
  · rw [map_spanOver, AddSubgroup.coe_map]
    rfl

end GlobalTheory.CompanionTheory.Ar.Num.SpanExact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.StatementUnavailableOne
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem block_monogenic_of_residual_character : ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (emb : (E →+* C) → (𝓞 E →+* V)), (∀ s (a : 𝓞 E), algebraMap V C (emb s a) = s (a : E)) → Nat.card (E →+* C) = Module.finrank ℚ E → ∀ σ : E →+* C, ∃ π : 𝓞 E, (∀ s s' : E →+* C, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → (∀ a, ¬ IsUnit (emb s' a - emb σ a)) → emb s π = emb s' π → s = s') ∧ ∀ f : (E →+* C) → V, (∀ s, (∃ a, IsUnit (emb s a - emb σ a)) → f s = 0) → ((∃ g : Polynomial V, ∀ s, (∀ a, ¬ IsUnit (emb s a - emb σ a)) → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span V (Set.range fun a : 𝓞 E => fun s => emb s a)) := by
  exact @PositivityTheory.Xgn.exists_monogenic_separating

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticPeriodMatrixIntegrality
section
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem gp_mat_lattice :
    ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
      v.Integers R → ∀ (g : ℕ) (Ht Bt : Matrix (Fin g) (Fin g ⊕ Fin g) R)
        (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) (cp : R),
        cp ≠ 0 → Eᵀ = -E → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E →
          let φ := algebraMap R C
          let intg : (Fin g → C) → Prop := fun w => ∀ k, v (w k) ≤ 1
          let hb : Matrix (Fin g ⊕ Fin g) (Fin g) C := ((Eᵀ)⁻¹ * Htᵀ).map φ
          v (φ (Matrix.fromRows Ht Bt).det) = v (φ cp) ^ g ∧
            (∀ x : Fin g ⊕ Fin g → C, ((Ht.map φ) *ᵥ x = 0 ∧ intg ((Bt.map φ) *ᵥ x)) ↔
              ∃ w, intg w ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧
            (∀ w, intg w → ∃ x : Fin g ⊕ Fin g → C,
              (Ht.map φ) *ᵥ x = w ∧ (Bt.map φ) *ᵥ x = 0) ∧
            (∀ l : Fin g ⊕ Fin g → R,
              cp • l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k)) := by
  intro C _ v R _ _ hv g Ht Bt E cp hcp hE hEu hform φ intg hb
  have : IsDomain R := hv.hom_inj.isDomain _
  have hcp' : φ cp ≠ 0 := fun h => hcp (hv.hom_inj (by rw [map_zero]; exact h))
  have hEt : IsUnit (Eᵀ).det := by rwa [det_transpose]
  set U : Matrix (Fin g ⊕ Fin g) (Fin g) R := -((Eᵀ)⁻¹ * Btᵀ) with hU
  set W : Matrix (Fin g ⊕ Fin g) (Fin g) R := (Eᵀ)⁻¹ * Htᵀ with hW
  have h1 : U * Ht + W * Bt = cp • (1 : Matrix _ _ R) := by
    have : U * Ht + W * Bt = (Eᵀ)⁻¹ * (-(Btᵀ * Ht - Htᵀ * Bt)) := by
      rw [hU, hW, neg_sub, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    rw [this, hform, ← smul_neg, ← hE, Matrix.mul_smul, nonsing_inv_mul _ hEt]
  have h2 : fromCols U W * fromRows Ht Bt = cp • (1 : Matrix _ _ R) := by
    rw [fromCols_mul_fromRows, h1]
  have h3 := PositivityTheory.HtPt.Rh.mul_eq_smul_one_symm hcp h2
  rw [fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj] at h3
  obtain ⟨a11, a12, a21, a22⟩ := h3
  rw [smul_zero] at a12 a21
  have hone : ∀ {n : Type} [DecidableEq n], (cp • (1 : Matrix n n R)).map φ = φ cp • (1 : Matrix n n C) := by
    intro n _
    ext i j
    by_cases h : i = j <;> simp [h]
  have b1 := congrArg (·.map φ) h1
  have b11 := congrArg (·.map φ) a11
  have b12 := congrArg (·.map φ) a12
  have b21 := congrArg (·.map φ) a21
  have b22 := congrArg (·.map φ) a22
  simp only [Matrix.map_add _ (map_add φ), Matrix.map_mul, hone, Matrix.map_zero _ (map_zero φ)]
    at b1 b11 b12 b21 b22
  refine ⟨?_, fun x => ⟨fun hx => ⟨_, hx.2, ?_⟩, ?_⟩, fun w _ => ⟨(φ cp)⁻¹ • (U.map φ *ᵥ w), ?_, ?_⟩,
    fun l => ?_⟩
  · have hJ : (fromRows Ht Bt)ᵀ * Matrix.J (Fin g) R * fromRows Ht Bt = cp • E := by
      rw [← hform, Matrix.J, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [sub_eq_add_neg]
    have hd := congrArg (fun M => v (φ M.det)) hJ
    simp only [det_mul, det_transpose, det_smul, map_mul, map_pow, Fintype.card_sum,
      Fintype.card_fin] at hd
    rw [hv.one_of_isUnit (Matrix.isUnit_det_J (Fin g) R), hv.one_of_isUnit hEu, mul_one, mul_one,
      pow_add] at hd
    exact (mul_self_inj zero_le zero_le).1 hd
  · have := congrArg (· *ᵥ x) b1
    simp only [add_mulVec, ← mulVec_mulVec, hx.1, mulVec_zero, zero_add, smul_mulVec,
      one_mulVec] at this
    change x = (φ cp)⁻¹ • (W.map φ *ᵥ _)
    rw [this, inv_smul_smul₀ hcp']
  · rintro ⟨w, hw, rfl⟩
    change Ht.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)) = 0 ∧
      intg (Bt.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)))
    rw [mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, b12, b22, zero_mulVec, smul_zero,
      smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
    exact ⟨rfl, hw⟩
  · rw [mulVec_smul, mulVec_mulVec, b11, smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
  · rw [mulVec_smul, mulVec_mulVec, b21, zero_mulVec, smul_zero]
  · have : cp • l = (l ᵥ* fromCols U W) ᵥ* fromRows Ht Bt := by
      rw [vecMul_vecMul, h2, vecMul_smul, vecMul_one]
    rw [this, vecMul_eq_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.GR
end

