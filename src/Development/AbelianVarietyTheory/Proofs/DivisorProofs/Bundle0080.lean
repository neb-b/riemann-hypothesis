module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnitriangularMulUpperTriangularOfIsUnitLead
section
open Matrix

namespace GlobalTheory

theorem lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors :
    ∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R),
      (∀ (k : ℕ) (hk : k ≤ n), IsUnit (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det) →
      ∃ L U : Matrix (Fin n) (Fin n) R, (∀ i j : Fin n, i < j → L i j = 0) ∧ (∀ i, L i i = 1) ∧
        U.BlockTriangular id ∧ (∀ i, IsUnit (U i i)) ∧ M = L * U := by
  intro R _ n
  induction n with
  | zero =>
    intro M _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      Subsingleton.elim _ _⟩
  | succ n ih =>
    intro M hM
    set M' : Matrix (Fin n) (Fin n) R := M.submatrix Fin.castSucc Fin.castSucc with hM'
    have hM'min : ∀ (k : ℕ) (hk : k ≤ n),
        IsUnit (M'.submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
      intro k hk
      have := hM k (hk.trans n.le_succ)
      convert this using 2
      ext i j; rfl
    obtain ⟨L', U', hL'0, hL'1, hU't, hU'd, hLU'⟩ := ih M' hM'min
    have hL'det : L'.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L' (fun i j hij => hL'0 i j hij)]
      simp [hL'1]
    have hL'u : IsUnit L'.det := by rw [hL'det]; exact isUnit_one
    have hM'u : IsUnit M'.det := by
      have := hM'min n le_rfl
      convert this using 2
      ext i j; rfl
    have hU'u : IsUnit U'.det := by
      rw [hLU', det_mul, hL'det, one_mul] at hM'u; exact hM'u
    let v : Fin n → R := fun i => M (Fin.castSucc i) (Fin.last n)
    let u : Fin n → R := fun j => M (Fin.last n) (Fin.castSucc j)
    let a : Fin n → R := u ᵥ* U'⁻¹
    let b : Fin n → R := L'⁻¹ *ᵥ v
    let e : R := M (Fin.last n) (Fin.last n) - a ⬝ᵥ b
    let L : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) 1 (fun j' => a j') j)
        (fun i' => Fin.lastCases (motive := fun _ => R) 0 (fun j' => L' i' j') j) i
    let U : Matrix (Fin (n+1)) (Fin (n+1)) R := Matrix.of fun i j =>
      Fin.lastCases (motive := fun _ => R)
        (Fin.lastCases (motive := fun _ => R) e (fun _ => 0) j)
        (fun i' => Fin.lastCases (motive := fun _ => R) (b i') (fun j' => U' i' j') j) i
    have ha : a ᵥ* U' = u := by
      simp only [a]; rw [vecMul_vecMul, nonsing_inv_mul _ hU'u, vecMul_one]
    have hb : L' *ᵥ b = v := by
      simp only [b]; rw [mulVec_mulVec, mul_nonsing_inv _ hL'u, one_mulVec]
    have hL0 : ∀ i j : Fin (n+1), i < j → L i j = 0 := by
      intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [L] at *
      all_goals first
        | exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)
        | exact hL'0 _ _ hij
    have hL1 : ∀ i, L i i = 1 := by
      intro i
      induction i using Fin.lastCases <;> simp [L, hL'1]
    have hUt : U.BlockTriangular id := by
      intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [U] at *
      all_goals first
        | exact absurd hij (not_lt.2 (Fin.castSucc_lt_last _).le)
        | exact hU't hij
    have hLU : M = L * U := by
      ext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last =>
          simp only [L, U, e, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, dotProduct]
          ring
        | cast j =>
          have hj := congrFun ha j
          simp only [vecMul, dotProduct, u] at hj
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hj]
          ring
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          have hi := congrFun hb i
          simp only [mulVec, dotProduct, v] at hi
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hi]
          ring
        | cast j =>
          have hij := congrFun (congrFun hLU' i) j
          simp only [M', Matrix.submatrix_apply, Matrix.mul_apply] at hij
          simp only [L, U, Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.of_apply,
            Fin.lastCases_last, Fin.lastCases_castSucc, hij]
          ring
    have hdetL : L.det = 1 := by
      rw [Matrix.det_of_lowerTriangular L (fun i j hij => hL0 i j hij)]
      simp [hL1]
    have hMu : IsUnit M.det := by
      have := hM (n+1) le_rfl
      convert this using 2
      ext i j; rfl
    have he : IsUnit e := by
      rw [hLU, det_mul, hdetL, one_mul, Matrix.det_of_upperTriangular hUt,
        Fin.prod_univ_castSucc] at hMu
      have := isUnit_of_mul_isUnit_right hMu
      simpa [U] using this
    refine ⟨L, U, hL0, hL1, hUt, ?_, hLU⟩
    intro i
    induction i using Fin.lastCases with
    | last => simpa [U] using he
    | cast i => simpa [U] using hU'd i
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapMaximalIdealEqOfFormallyUnramified
section
open IsLocalRing

namespace GlobalTheory

theorem map_comap_maximalIdeal_eq_of_formallyUnramified
    (A B : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] :
    ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := by
  set p := (maximalIdeal B).comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let A' := Localization.AtPrime p
  have hg : ∀ y : p.primeCompl, IsUnit (algebraMap A B y) := by
    intro y
    have : (y : A) ∉ p := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp this
  let f : A' →+* B := IsLocalization.lift (M := p.primeCompl) hg
  letI : Algebra A' B := f.toAlgebra
  haveI : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq
    (fun x => (IsLocalization.lift_eq (M := p.primeCompl) hg x).symm)
  haveI : IsLocalHom (algebraMap A' B) := by
    constructor
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    have e : IsLocalization.mk' A' a s * algebraMap A A' s = algebraMap A A' a :=
      IsLocalization.mk'_spec A' a s
    have hs : IsUnit (algebraMap A' B (algebraMap A A' s)) := by
      rw [← IsScalarTower.algebraMap_apply]; exact hg s
    have ha : IsUnit (algebraMap A B a) := by
      rw [IsScalarTower.algebraMap_apply A A' B, ← e, map_mul]; exact hx.mul hs
    have ha' : a ∈ p.primeCompl := by
      show a ∉ p
      rw [hp, Ideal.mem_comap]
      exact IsLocalRing.notMem_maximalIdeal.mpr ha
    have hu : IsUnit (algebraMap A A' a) := IsLocalization.map_units A' (⟨a, ha'⟩ : p.primeCompl)
    rw [← e] at hu
    exact isUnit_of_mul_isUnit_left hu
  haveI : Algebra.FormallyUnramified A' B := .of_restrictScalars A A' B
  haveI : Algebra.EssFiniteType A' B := .of_comp A A' B
  have h := Algebra.FormallyUnramified.map_maximalIdeal (R := A') (S := B)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapDomainRelationLiftCommutingSquare
section
namespace GlobalTheory

theorem mapDomain_apply_eq_sum_filter {α β : Type} {M : Type*} [AddCommMonoid M] (f : α → β)
    (x : α →₀ M) (b : β) [DecidableEq β] :
    (Finsupp.mapDomain f x) b = ∑ a ∈ x.support.filter (fun a => f a = b), x a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem mapDomain_neg_of_group {α β : Type} {M : Type*} [AddCommGroup M] (f : α → β)
    (x : α →₀ M) : Finsupp.mapDomain f (-x) = -Finsupp.mapDomain f x :=
  map_neg (Finsupp.mapDomain.addMonoidHom f) x

theorem mapDomain_corner_lift : ∀ (M : Type 1) [AddCommGroup M] (X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : Type)
    (c : X₂ → X₄) (d : X₃ → X₄) (u : Y₁ → Y₂) (v : Y₁ → Y₃) (c' : Y₂ → Y₄) (d' : Y₃ → Y₄)
    (r₂ : X₂ → Y₂) (r₃ : X₃ → Y₃) (r₄ : X₄ → Y₄) (G : Y₄ → Prop),
    (∀ x, c' (r₂ x) = r₄ (c x)) → (∀ y, d' (r₃ y) = r₄ (d y)) → (∀ x, c' (u x) = d' (v x)) →
    Function.Injective c' → (∀ x, G (c' x)) → (∀ y, G (d' y) → ∃ x, v x = y) →
    ∀ (a₂ : X₂ →₀ M) (a₃ : X₃ →₀ M), Finsupp.mapDomain c a₂ + Finsupp.mapDomain d a₃ = 0 →
    (∀ y ∈ a₃.support, ∀ y' ∈ a₃.support, d y = d y' → r₃ y = r₃ y' ∨ G (d' (r₃ y))) →
    ∃ a : Y₁ →₀ M, Finsupp.mapDomain u a = Finsupp.mapDomain r₂ a₂ ∧
      Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
  intro M _ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ c d u v c' d' r₂ r₃ r₄ G h1 h2 h3 hinj hG hlift a₂ a₃ hsum hpair
  classical
  have hdownF : Finsupp.mapDomain d a₃ = -Finsupp.mapDomain c a₂ :=
    eq_neg_of_add_eq_zero_right hsum
  have hdown : ∀ z, (Finsupp.mapDomain d a₃) z = -(Finsupp.mapDomain c a₂) z := fun z => by
    rw [hdownF, Finsupp.neg_apply]

  have hsupp : ∀ y'', ¬ G (d' y'') → (Finsupp.mapDomain r₃ a₃) y'' = 0 := by
    intro y'' hy''
    rw [mapDomain_apply_eq_sum_filter]
    rw [← Finset.sum_fiberwise_of_maps_to (t := (a₃.support.filter (fun y => r₃ y = y'')).image d)
      (g := d) (fun i hi => Finset.mem_image_of_mem d hi)]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hz
    have hyF' := Finset.mem_filter.mp hyF
    have hnot : ¬ G (r₄ (d y)) := by rw [← h2, hyF'.2]; exact hy''
    have hfib : ((a₃.support.filter (fun y => r₃ y = y'')).filter fun i => d i = d y) =
        a₃.support.filter (fun i => d i = d y) := by
      ext y'
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨h1', _⟩, h3'⟩; exact ⟨h1', h3'⟩
      · rintro ⟨h1', h3'⟩
        refine ⟨⟨h1', ?_⟩, h3'⟩
        rcases hpair y hyF'.1 y' h1' h3'.symm with h | h
        · rw [← h, hyF'.2]
        · rw [hyF'.2] at h; exact absurd h hy''
    have hc0 : (Finsupp.mapDomain c a₂) (d y) = 0 := by
      rw [mapDomain_apply_eq_sum_filter]
      refine Finset.sum_eq_zero fun x hx => ?_
      exfalso
      have hx' := (Finset.mem_filter.mp hx).2
      apply hnot
      rw [← hx', ← h1]; exact hG _
    have e := mapDomain_apply_eq_sum_filter d a₃ (d y)
    rw [hdown, hc0, neg_zero] at e
    rw [hfib]
    convert e.symm

  let S : Set Y₃ := {y | G (d' y)}
  have hS : ↑(Finsupp.mapDomain r₃ a₃).support ⊆ Set.range (Subtype.val : S → Y₃) := by
    intro y hy
    by_contra hn
    apply Finsupp.mem_support_iff.mp hy
    apply hsupp
    intro hG'
    exact hn ⟨⟨y, hG'⟩, rfl⟩
  let lift : S → Y₁ := fun s => Classical.choose (hlift s.1 s.2)
  have hlift' : v ∘ lift = Subtype.val := funext fun s => Classical.choose_spec (hlift s.1 s.2)
  let a : Y₁ →₀ M := -Finsupp.mapDomain lift
    (Finsupp.comapDomain Subtype.val (Finsupp.mapDomain r₃ a₃) Subtype.val_injective.injOn)
  have hva : Finsupp.mapDomain v a = -Finsupp.mapDomain r₃ a₃ := by
    simp only [a, mapDomain_neg_of_group, ← Finsupp.mapDomain_comp, hlift']
    rw [Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective _ hS]

  refine ⟨a, Finsupp.mapDomain_injective hinj ?_, hva⟩
  have e1 : Finsupp.mapDomain c' (Finsupp.mapDomain u a) =
      Finsupp.mapDomain d' (Finsupp.mapDomain v a) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show c' ∘ u = d' ∘ v from funext h3]
  have e2 : Finsupp.mapDomain d' (Finsupp.mapDomain r₃ a₃) =
      Finsupp.mapDomain r₄ (Finsupp.mapDomain d a₃) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show d' ∘ r₃ = r₄ ∘ d from funext h2]
  have e3 : Finsupp.mapDomain c' (Finsupp.mapDomain r₂ a₂) =
      Finsupp.mapDomain r₄ (Finsupp.mapDomain c a₂) := by
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, show c' ∘ r₂ = r₄ ∘ c from funext h1]
  rw [e1, hva, mapDomain_neg_of_group, e2, hdownF, mapDomain_neg_of_group, neg_neg, e3]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapEqZeroOfCommuteDoubling
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieFaithful

open IsLocalRing

theorem map_sub_two_pow_mul_mem {R : Type} [CommRing R] (m : Ideal R) (φ : R →+* R)
    (h : ∀ x ∈ m, φ x - 2 * x ∈ m ^ 2) (n : ℕ) :
    ∀ y ∈ m ^ (n + 1), φ y - 2 ^ (n + 1) * y ∈ m ^ (n + 2) := by
  have hφ : ∀ x ∈ m, φ x ∈ m := fun x hx => by
    have h1 := Ideal.pow_le_self (two_ne_zero) (h x hx)
    have h2 := m.add_mem h1 (m.mul_mem_left 2 hx)
    simpa using h2
  induction n with
  | zero =>
    intro y hy
    simpa using h y (by simpa using hy)
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have e : φ (a * b) - 2 ^ (n + 1 + 1) * (a * b) =
          (φ a - 2 ^ (n + 1) * a) * φ b + (2 ^ (n + 1) * a) * (φ b - 2 * b) := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have := Ideal.mul_mem_mul (ih a ha) (hφ b hb)
        rwa [← pow_succ] at this
      · have := Ideal.mul_mem_mul (Ideal.mul_mem_left _ (2 ^ (n + 1)) ha) (h b hb)
        rw [← pow_add] at this
        exact this
    · intro a b ha hb
      have e : φ (a + b) - 2 ^ (n + 1 + 1) * (a + b) =
          (φ a - 2 ^ (n + 1 + 1) * a) + (φ b - 2 ^ (n + 1 + 1) * b) := by
        rw [map_add (f := _)]; ring
      rw [e]
      exact Ideal.add_mem _ ha hb

theorem map_eq_zero_of_commute_doubling {k RA RB : Type} [Field k] [CharZero k] [CommRing RA]
    [IsLocalRing RA] [IsNoetherianRing RA] [Algebra k RA] [CommRing RB] (mB : Ideal RB)
    (φA : RA →+* RA) (φB : RB →+* RB) (ψ : RB →+* RA) (hc : ∀ x, ψ (φB x) = φA (ψ x))
    (h1 : ∀ x ∈ mB, ψ x ∈ maximalIdeal RA ^ 2)
    (hA : ∀ x ∈ maximalIdeal RA, φA x - 2 * x ∈ maximalIdeal RA ^ 2)
    (hB : ∀ x ∈ mB, φB x - 2 * x ∈ mB ^ 2) (x : RB) (hx : x ∈ mB) : ψ x = 0 := by
  have key : ∀ n : ℕ, ∀ x ∈ mB, ψ x ∈ maximalIdeal RA ^ (n + 2) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      intro x hx
      set m := maximalIdeal RA with hm
      have hy := ih x hx
      have hle : Ideal.map ψ mB ≤ m ^ (n + 2) := Ideal.map_le_iff_le_comap.2 ih
      have hz : ψ (φB x - 2 * x) ∈ m ^ (n + 3) := by
        have h2 : ψ (φB x - 2 * x) ∈ Ideal.map ψ (mB ^ 2) := Ideal.mem_map_of_mem _ (hB x hx)
        rw [Ideal.map_pow] at h2
        have h3 : (Ideal.map ψ mB) ^ 2 ≤ (m ^ (n + 2)) ^ 2 := Ideal.pow_right_mono hle 2
        have h4 := h3 h2
        rw [← pow_mul] at h4
        exact Ideal.pow_le_pow_right (by omega) h4
      have hd := map_sub_two_pow_mul_mem m φA hA (n + 1) _ hy
      have e : (2 ^ (n + 2) - 2 : RA) * ψ x = ψ (φB x - 2 * x) - (φA (ψ x) - 2 ^ (n + 2) * ψ x) := by
        rw [map_sub, map_mul, hc, map_ofNat]; ring
      have h5 : (2 ^ (n + 2) - 2 : RA) * ψ x ∈ m ^ (n + 3) := by
        rw [e]; exact Ideal.sub_mem _ hz hd
      have hne : (2 ^ (n + 2) - 2 : k) ≠ 0 := by
        have : ((2 ^ (n + 2) - 2 : ℤ) : k) ≠ 0 := by
          rw [Int.cast_ne_zero]
          have : (2 : ℤ) ^ (n + 2) = 4 * 2 ^ n := by ring
          have h6 : (0 : ℤ) < 2 ^ n := by positivity
          omega
        simpa using this
      have h7 := Ideal.mul_mem_left _ (algebraMap k RA (2 ^ (n + 2) - 2 : k)⁻¹) h5
      have e2 : algebraMap k RA (2 ^ (n + 2) - 2 : k)⁻¹ * ((2 ^ (n + 2) - 2 : RA) * ψ x) = ψ x := by
        have : (2 ^ (n + 2) - 2 : RA) = algebraMap k RA (2 ^ (n + 2) - 2 : k) := by
          rw [map_sub, map_pow, map_ofNat]
        rw [this, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hne, map_one, one_mul]
      rwa [e2] at h7
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal RA) (Ideal.IsPrime.ne_top inferInstance)
  have : ψ x ∈ (⨅ i : ℕ, maximalIdeal RA ^ i) := by
    refine (Submodule.mem_iInf _).2 fun i => ?_
    exact Ideal.pow_le_pow_right (by omega) (key i x hx)
  rw [hinf] at this
  simpa using this

section Tan

variable {k R : Type} [Field k] [CommRing R] [Algebra k R] (ev : R →ₐ[k] k)

def kerPart (x : R) : RingHom.ker ev :=
  ⟨x - algebraMap k R (ev x), by simp [RingHom.mem_ker]⟩

def cotPart (x : R) : (RingHom.ker ev).Cotangent := (RingHom.ker ev).toCotangent (kerPart ev x)

theorem cotPart_add (x y : R) : cotPart ev (x + y) = cotPart ev x + cotPart ev y := by
  rw [cotPart, cotPart, cotPart, ← map_add (f := _)]
  congr 1
  apply Subtype.ext
  simp only [kerPart, map_add (f := _), Submodule.coe_add]
  ring

theorem cotPart_algebraMap (a : k) : cotPart ev (algebraMap k R a) = 0 := by
  have : kerPart ev (algebraMap k R a) = 0 := Subtype.ext (by simp [kerPart])
  rw [cotPart, this, map_zero]

theorem cotPart_mul (x y : R) : cotPart ev (x * y) = ev x • cotPart ev y + ev y • cotPart ev x := by
  rw [← algebraMap_smul R (ev x), ← algebraMap_smul R (ev y), cotPart, cotPart, cotPart, ← map_smul,
    ← map_smul, ← map_add, Ideal.toCotangent_eq]
  have e : ((kerPart ev (x * y) : R) - (algebraMap k R (ev x) • kerPart ev y + algebraMap k R (ev y) • kerPart ev x :
      RingHom.ker ev)) = (kerPart ev x : R) * (kerPart ev y : R) := by
    simp only [kerPart, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
    ring
  rw [e, pow_two]
  exact Ideal.mul_mem_mul (kerPart ev x).2 (kerPart ev y).2

def tanHom (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) : R →ₐ[k] DualNumber k where
  toFun x := TrivSqZeroExt.inl (ev x) + TrivSqZeroExt.inr (lam (cotPart ev x))
  map_one' := by
    have := cotPart_algebraMap ev 1
    rw [map_one] at this
    ext <;> simp [this]
  map_mul' x y := by
    ext
    · simp
    · simp [cotPart_mul, mul_comm]
  map_zero' := by
    have := cotPart_algebraMap ev 0
    rw [map_zero] at this
    ext <;> simp [this]
  map_add' x y := by
    ext
    · simp
    · simp [cotPart_add]
  commutes' a := by
    ext
    · simp [TrivSqZeroExt.algebraMap_eq_inl]
    · simp [cotPart_algebraMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem tanHom_fst (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) (x : R) : (tanHom ev lam x).fst = ev x := by
  simp [tanHom]

theorem tanHom_snd (lam : (RingHom.ker ev).Cotangent →ₗ[k] k) (x : R) :
    (tanHom ev lam x).snd = lam (cotPart ev x) := by
  simp [tanHom]

theorem mem_sq_of_tanHom_eq_zero (x : R) (h : ∀ lam, tanHom ev lam x = 0) : x ∈ RingHom.ker ev ^ 2 := by
  have h0 : ev x = 0 := by rw [← tanHom_fst ev 0, h]; rfl
  have h1 : cotPart ev x = 0 := by
    refine (Module.forall_dual_apply_eq_zero_iff k _).1 fun lam => ?_
    rw [← tanHom_snd ev lam, h]; rfl
  rw [cotPart, Ideal.toCotangent_eq_zero] at h1
  simpa [kerPart, h0] using h1

theorem ker_eq_maximalIdeal_of_algHom [IsLocalRing R] : RingHom.ker ev = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (ev : R →+* k)
    (fun a => ⟨algebraMap k R a, by simp⟩))

end Tan

end GlobalTheory.LieFaithful
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDiagonalizableOfCharpolyEqProdDistinct
section
open Polynomial

namespace GlobalTheory

theorem matrix_diagonalizable_of_charpoly_eq_prod_distinct (K : Type) [Field K] (n : ℕ)
    (γ : Matrix (Fin n) (Fin n) K) (ν : Fin n → K) (hν : Function.Injective ν)
    (hγ : γ.charpoly = ∏ k, (X - C (ν k))) :
    ∃ y : GL (Fin n) K, γ * (y : Matrix (Fin n) (Fin n) K) = (y : Matrix (Fin n) (Fin n) K) * Matrix.diagonal ν := by
  have hev : ∀ k, Module.End.HasEigenvalue (Matrix.toLin' γ) (ν k) := by
    intro k
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hγ]
    simp only [IsRoot, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)
  choose v hv using fun k => (hev k).exists_hasEigenvector
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' _ ν hν v hv
  set Y : Matrix (Fin n) (Fin n) K := Matrix.of fun i k => v k i with hY
  have hcols : Y.col = v := by
    funext k i; rfl
  have hu : IsUnit Y := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    rw [hcols]; exact hli
  refine ⟨hu.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  ext i k
  rw [Matrix.mul_diagonal]
  have h1 := (hv k).apply_eq_smul
  rw [Matrix.toLin'_apply] at h1
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  rw [Matrix.mul_apply]
  simp only [hY, Matrix.of_apply]
  rw [mul_comm, ← h2]
  rfl

end GlobalTheory
end

