module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.Imports
section
namespace GlobalTheory.UnimodularLatticeLemma

theorem main {L : Type} [Field L] [IsAlgClosed L] {ι V : Type} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Nontrivial V] (f : ι → Module.End L V)
    (hc : ∀ (a b : ι), f a * f b = f b * f a) :
    ∃ (v : V), v ≠ (0 : V) ∧ ∀ (b : ι), ∃ (μ : L), (f b : V → V) v = μ • v := by
  classical
  let S : Set (Submodule L V) := {W | W ≠ ⊥ ∧ ∀ b, ∀ x ∈ W, f b x ∈ W}
  have hS : (⊤ : Submodule L V) ∈ S := ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top⟩
  obtain ⟨W, hW, hmin⟩ := (wellFounded_lt (α := Submodule L V)).has_min S ⟨⊤, hS⟩
  have key : ∀ b, ∃ μ : L, ∀ x ∈ W, f b x = μ • x := by
    intro b
    have hWb : ∀ x ∈ W, f b x ∈ W := hW.2 b
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW.1
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((f b).restrict hWb)
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    have hw1 : (f b).restrict hWb w = μ • w := hw.apply_eq_smul
    have hw0 : w ≠ 0 := hw.2
    let W' : Submodule L V := W ⊓ LinearMap.ker (f b - μ • 1)
    have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ f b x = μ • x := by
      intro x
      simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hW'S : W' ∈ S := by
      refine ⟨?_, ?_⟩
      · intro h
        apply hw0
        have : (w : V) ∈ W' := by
          rw [hmem]
          refine ⟨w.2, ?_⟩
          have := congrArg Subtype.val hw1
          simpa using this
        rw [h, Submodule.mem_bot] at this
        exact Subtype.ext this
      · intro c x hx
        rw [hmem] at hx ⊢
        refine ⟨hW.2 c x hx.1, ?_⟩
        have h1 : f b (f c x) = (f b * f c) x := rfl
        rw [h1, hc b c, Module.End.mul_apply, hx.2, map_smul]
    have hle : W' ≤ W := inf_le_left
    have heq : W' = W := by
      by_contra hne
      exact hmin W' hW'S (lt_of_le_of_ne hle hne)
    refine ⟨μ, fun x hx => ?_⟩
    have : x ∈ W' := heq ▸ hx
    exact ((hmem x).1 this).2
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.1
  refine ⟨v, hv0, fun b => ?_⟩
  obtain ⟨μ, hμ⟩ := key b
  exact ⟨μ, hμ v hvW⟩

end GlobalTheory.UnimodularLatticeLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ImportsAlt
section
universe u_1 u_2

namespace GlobalTheory.UnimodularLatticeExistence

open Representation

theorem main : ∀ {G : Type u_1} [inst : Group G] {V : Type u_2} [inst_1 : AddCommGroup V] [inst_2 : Module ℂ V] (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ↔ Nontrivial V ∧ ∀ (U : Submodule ℂ V), (∀ (g : G), ∀ v ∈ U, ((ρ : G → V →ₗ[ℂ] V) g : V → V) v ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro G _ V _ _ ρ
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl
  have htop : (⊤ : Subrepresentation ρ).toSubmodule = ⊤ := rfl
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
      apply Subrepresentation.toSubmodule_injective
      rw [hbot, htop]
      exact Subsingleton.elim _ _
    · intro U hU
      let σ : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
      rcases h.eq_bot_or_eq_top σ with h1 | h1
      · left
        have := congrArg Subrepresentation.toSubmodule h1
        exact this
      · right
        have := congrArg Subrepresentation.toSubmodule h1
        exact this
  · rintro ⟨hV, hU⟩
    haveI : Nontrivial (Subrepresentation ρ) := by
      refine ⟨⟨⊥, ⊤, fun h => ?_⟩⟩
      have := congrArg Subrepresentation.toSubmodule h
      rw [hbot, htop] at this
      exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤) this
    refine ⟨fun σ => ?_⟩
    rcases hU σ.toSubmodule (fun g v hv => σ.apply_mem_toSubmodule g hv) with h1 | h1
    · left
      apply Subrepresentation.toSubmodule_injective
      rw [h1, hbot]
    · right
      apply Subrepresentation.toSubmodule_injective
      rw [h1, htop]

end GlobalTheory.UnimodularLatticeExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleIdempotentEqOneAndCharacterEqWeightAl
section
namespace GlobalTheory

theorem irreducible_idempotent_eq_one_and_character_eq_weight
    (L : Type) [Field L] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (ρ : Representation L G V) (hρ : ρ.IsIrreducible) :
    (∀ e : Module.End L V, e ≠ 0 → e * e = e → (∀ g, ρ g * e = e * ρ g) → e = 1) ∧
    (∀ (lam : G →* Lˣ) (v : V), v ≠ 0 → (∀ g, ρ g v = (lam g : L) • v) →
      ∀ g, ρ.character g = (lam g : L)) := by
  have key : ∀ (W : Submodule L V), (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W ≠ ⊥ → W = ⊤ := by
    intro W hW hne
    let S : Subrepresentation ρ := ⟨W, fun g x hx => hW g x hx⟩
    rcases hρ.eq_bot_or_eq_top S with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hne
    · exact congrArg Subrepresentation.toSubmodule h
  refine ⟨fun e he hee hc => ?_, fun lam v hv hl g => ?_⟩
  · have h : LinearMap.range e = ⊤ := by
      refine key _ ?_ ?_
      · rintro g _ ⟨u, rfl⟩
        exact ⟨ρ g u, (congrArg (fun f : Module.End L V => f u) (hc g)).symm⟩
      · intro h
        exact he (LinearMap.range_eq_bot.mp h)
    ext w
    obtain ⟨u, rfl⟩ := LinearMap.range_eq_top.mp h w
    exact congrArg (fun f : Module.End L V => f u) hee
  · have h : Submodule.span L {v} = ⊤ := by
      refine key _ ?_ ?_
      · intro g x hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, hl]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
      · simpa using hv
    have hfin : Module.finrank L V = 1 := by
      rw [← finrank_top, ← h]
      exact finrank_span_singleton hv
    have hg : ρ g = (lam g : L) • LinearMap.id := by
      ext x
      have hx : x ∈ Submodule.span L {v} := h ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hl, smul_comm c]
    simp [Representation.character, hg, hfin]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.LinearMapShortExactCommute
section
namespace GlobalTheory

theorem trace_eq_add_of_shortExact (K : Type) [Field K]
    (U : Type) [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (i : U →ₗ[K] V) (p : V →ₗ[K] W) (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : LinearMap.range i = LinearMap.ker p)
    (hb : b ∘ₗ i = i ∘ₗ a) (hc : p ∘ₗ b = c ∘ₗ p) :
    LinearMap.trace K V b = LinearMap.trace K U a + LinearMap.trace K W c := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hp)
  obtain ⟨r₀, hr₀⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hs' : ∀ w, p (s w) = w := fun w => LinearMap.congr_fun hs w
  have hr' : ∀ u, r₀ (i u) = u := fun u => LinearMap.congr_fun hr₀ u
  have hpi : ∀ u, p (i u) = 0 := fun u => by
    have : i u ∈ LinearMap.ker p := hex ▸ LinearMap.mem_range_self i u
    exact this
  have hb' : ∀ u, b (i u) = i (a u) := fun u => LinearMap.congr_fun hb u
  have hc' : ∀ v, p (b v) = c (p v) := fun v => LinearMap.congr_fun hc v
  let r : V →ₗ[K] U := r₀ ∘ₗ (LinearMap.id - s ∘ₗ p)
  have hri : ∀ u, r (i u) = u := fun u => by
    simp [r, hpi, hr']
  have hir : ∀ v, i (r v) = v - s (p v) := fun v => by
    have : v - s (p v) ∈ LinearMap.range i := by
      rw [hex, LinearMap.mem_ker, map_sub, hs', sub_self]
    obtain ⟨u, hu⟩ := this
    have h2 : r v = u := by
      show r₀ (v - s (p v)) = u
      rw [← hu, hr']
    rw [h2, hu]
  have hdec : b = (b ∘ₗ i) ∘ₗ r + (b ∘ₗ s) ∘ₗ p := by
    ext v
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hir, map_sub, sub_add_cancel]
  have h1 : r ∘ₗ (b ∘ₗ i) = a := by
    ext u
    simp only [LinearMap.comp_apply, hb', hri]
  have h2 : p ∘ₗ (b ∘ₗ s) = c := by
    ext w
    simp only [LinearMap.comp_apply, hc', hs']
  calc LinearMap.trace K V b
      = LinearMap.trace K V ((b ∘ₗ i) ∘ₗ r) + LinearMap.trace K V ((b ∘ₗ s) ∘ₗ p) := by
        rw [← map_add (f := _), ← hdec]
    _ = LinearMap.trace K U a + LinearMap.trace K W c := by
        rw [LinearMap.trace_comp_comm' r (b ∘ₗ i), LinearMap.trace_comp_comm' p (b ∘ₗ s), h1, h2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvd
section
namespace GlobalTheory

theorem one_mem_of_mul_mem_of_forall_prime_not_dvd (X : Type) [Finite X]
    (S : AddSubgroup (X → ℤ)) (hmul : ∀ f ∈ S, ∀ g ∈ S, f * g ∈ S)
    (hp : ∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) : (1 : X → ℤ) ∈ S := by
  classical
  have h1 : ∀ x : X, ∃ f ∈ S, f x = 1 := by
    intro x
    obtain ⟨d, hd⟩ := Int.subgroup_cyclic (S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x))
    have hd1 : (d : ℤ).natAbs = 1 := by
      rw [Nat.eq_one_iff_not_exists_prime_dvd]
      intro p pp hpd
      obtain ⟨f, hf, hnd⟩ := hp x p pp
      apply hnd
      have hmem : f x ∈ AddSubgroup.zmultiples (d : ℤ) := by
        obtain ⟨z, hz⟩ := hd ⟨f x, ⟨f, hf, rfl⟩⟩
        rw [Int.mem_zmultiples_iff]
        refine ⟨z, ?_⟩
        simpa [zsmul_eq_mul, mul_comm] using (congrArg Subtype.val hz).symm
      exact (Int.natCast_dvd.mpr hpd).trans (Int.mem_zmultiples_iff.mp hmem)
    have : (1 : ℤ) ∈ AddSubgroup.zmultiples (d : ℤ) := by
      rw [Int.mem_zmultiples_iff]
      exact isUnit_iff_dvd_one.mp (Int.isUnit_iff_natAbs_eq.mpr hd1)
    have hmap : (1 : ℤ) ∈ S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x) := by
      obtain ⟨z, hz⟩ := Int.mem_zmultiples_iff.mp this
      have hzmem : z • (d : ℤ) ∈ S.map (Pi.evalAddMonoidHom (fun _ : X => ℤ) x) :=
        AddSubgroup.zsmul_mem _ d.property z
      simpa [hz, mul_comm] using hzmem
    obtain ⟨f, hf, hfx⟩ := hmap
    exact ⟨f, hf, hfx⟩
  choose f hfS hf1 using h1
  have key : ∀ s : Finset X, 1 - ∏ x ∈ s, (1 - f x) ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have e : 1 - (1 - f a) * ∏ x ∈ s, (1 - f x)
          = f a + (1 - ∏ x ∈ s, (1 - f x)) - f a * (1 - ∏ x ∈ s, (1 - f x)) := by ring
      rw [e]
      exact S.sub_mem (S.add_mem (hfS a) ih) (hmul _ (hfS a) _ ih)
  haveI := Fintype.ofFinite X
  have h0 : ∏ x : X, (1 - f x) = 0 := by
    funext y
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [hf1])
  simpa [h0] using key Finset.univ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumConjIdempotentEqCardSmul
section
namespace GlobalTheory

theorem sum_conj_idempotent_eq_card_smul (L : Type) [Field L] (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module L V] (ρ : Representation L G V) (T : Subgroup G)
    (e : Module.End L V) (hirr : ρ.IsIrreducible) (he0 : e ≠ 0) (hee : e * e = e)
    (hT : ∀ t ∈ T, ρ t * e = e * ρ t) (hoff : ∀ g ∉ T, e * ρ g * e = 0) :
    ∑ x : G, ρ x * e * ρ x⁻¹ = (Nat.card T : L) • (1 : Module.End L V) := by
  classical
  set E : Module.End L V := ∑ x : G, ρ x * e * ρ x⁻¹ with hE
  have hcomm : ∀ g : G, ρ g * E = E * ρ g := by
    intro g
    rw [hE, Finset.mul_sum, Finset.sum_mul]
    refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ ?_
    intro x
    have h1 : ρ (g * x)⁻¹ * ρ g = ρ x⁻¹ := by
      rw [← map_mul]; congr 1; group
    simp only [Equiv.coe_mulLeft]
    rw [mul_assoc (ρ (g * x) * e), h1, map_mul]
    simp only [mul_assoc]
  have hEe : E * e = (Nat.card T : L) • e := by
    rw [hE, Finset.sum_mul]
    have h2 : ∀ x : G, ρ x * e * ρ x⁻¹ * e = if x ∈ T then e else 0 := by
      intro x
      split_ifs with hx
      · have h3 : ρ x * ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        rw [hT x hx, mul_assoc e, h3, mul_one, hee]
      · have h4 := hoff x⁻¹ (fun h => hx (by simpa using T.inv_mem h))
        calc ρ x * e * ρ x⁻¹ * e = ρ x * (e * ρ x⁻¹ * e) := by simp only [mul_assoc]
          _ = 0 := by rw [h4, mul_zero]
    rw [Finset.sum_congr rfl (fun x _ => h2 x), ← Finset.sum_filter, Finset.sum_const,
      Nat.cast_smul_eq_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]
  set D : Module.End L V := E - (Nat.card T : L) • (1 : Module.End L V) with hD
  have hDc : ∀ g : G, ρ g * D = D * ρ g := by
    intro g
    rw [hD, mul_sub, sub_mul, hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hDe : D * e = 0 := by
    rw [hD, sub_mul, hEe, smul_mul_assoc, one_mul, sub_self]
  let K : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker D
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        have := congrArg (fun f : Module.End L V => f v) (hDc g)
        simp only [Module.End.mul_apply] at this
        rw [← this, hv, map_zero] }
  have := hirr
  rcases IsSimpleOrder.eq_bot_or_eq_top K with h | h
  · exfalso
    apply he0
    ext v
    have hv : e v ∈ K.toSubmodule := by
      change e v ∈ LinearMap.ker D
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, hDe]; rfl
    rw [h] at hv
    exact hv
  · have hk : LinearMap.ker D = ⊤ := by
      change K.toSubmodule = ⊤
      rw [h]; rfl
    exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp hk)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
section
open Matrix Polynomial
open scoped BigOperators

namespace GlobalTheory

def E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

def W8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  0, -1,  0,  0,  0,  0,  0;
       0,  1,  0, -1,  0,  0,  0,  0;
       0,  0,  1, -1,  0,  0,  0,  0;
       0,  0,  0,  1, -1,  0,  0,  0;
       0,  0,  0,  0,  1, -1,  0,  0;
       0,  0,  0,  0,  0,  1, -1,  0;
       0,  0,  0,  0,  0,  0,  1, -1;
       0,  0,  0,  0,  0,  0,  0,  1]

def E8inv : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  7, 10,  8,  6,  4,  2;
       5,  8, 10, 15, 12,  9,  6,  3;
       7, 10, 14, 20, 16, 12,  8,  4;
      10, 15, 20, 30, 24, 18, 12,  6;
       8, 12, 16, 24, 20, 15, 10,  5;
       6,  9, 12, 18, 15, 12,  8,  4;
       4,  6,  8, 12, 10,  8,  6,  3;
       2,  3,  4,  6,  5,  4,  3,  2]

def w8 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  4,  5,  3, -2, -2, -2, -2, -2;
       5,  8,  5, -3, -3, -3, -3, -3;
       7, 10,  7, -4, -4, -4, -4, -4;
      10, 15, 10, -5, -6, -6, -6, -6;
       8, 12,  8, -4, -4, -5, -5, -5;
       6,  9,  6, -3, -3, -3, -4, -4;
       4,  6,  4, -2, -2, -2, -2, -3;
       2,  3,  2, -1, -1, -1, -1, -1]

def E8roots : Matrix (Fin 8) (Fin 8) ℤ :=
  !![  1,  2, -2,  0,  0,  0,  0,  0;
      -1,  2,  2, -2,  0,  0,  0,  0;
      -1,  0,  0,  2, -2,  0,  0,  0;
      -1,  0,  0,  0,  2, -2,  0,  0;
      -1,  0,  0,  0,  0,  2, -2,  0;
      -1,  0,  0,  0,  0,  0,  2, -2;
      -1,  0,  0,  0,  0,  0,  0,  2;
       1,  0,  0,  0,  0,  0,  0,  0]

theorem w8_add_transpose_eq_e8 : W8 + W8ᵀ = E8 := by decide

theorem e8_transpose : E8ᵀ = E8 := CartanMatrix.E₈_transpose

theorem e8_det_eq_one : E8.det = 1 := CartanMatrix.E₈_det

theorem e8inv_mul_e8 : E8inv * E8 = 1 := by decide

theorem e8_mul_e8inv : E8 * E8inv = 1 := by decide

theorem E8roots_transpose_mul_self : E8rootsᵀ * E8roots = (4 : ℤ) • E8 := by decide

theorem e8_posDef : (E8.map (fun x : ℤ => (x : ℝ))).PosDef := by
  set f : ℤ →+* ℝ := Int.castRingHom ℝ with hf
  change (E8.map f).PosDef
  have h : E8.map f = ((1 / 2 : ℝ) • E8roots.map f)ᴴ * ((1 / 2 : ℝ) • E8roots.map f) := by
    have h4 : (E8roots.map f)ᵀ * E8roots.map f = (4 : ℝ) • E8.map f := by
      rw [← Matrix.transpose_map, ← Matrix.map_mul, E8roots_transpose_mul_self]
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        smul_eq_mul, map_mul]
      simp [hf]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, h4, smul_smul, smul_smul]
    norm_num
  have hs : (E8.map f).PosSemidef := by
    rw [h]; exact Matrix.posSemidef_conjTranspose_mul_self _
  rw [hs.posDef_iff_det_ne_zero]
  have : (E8.map f).det = f E8.det := (RingHom.map_det f E8).symm
  rw [this, e8_det_eq_one, map_one]
  exact one_ne_zero

end GlobalTheory
end

