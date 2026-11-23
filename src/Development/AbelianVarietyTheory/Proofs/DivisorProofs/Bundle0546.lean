module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0531
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineKroneckerRightMatrixConjTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FerrandPushoutGoodBasicOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem basicOpen_res_eq {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (b : Γ(Y₁, upOpen i U)) :
    Y₀.basicOpen ((res i U).hom b) = i ⁻¹ᵁ Y₁.basicOpen b := by
  change Y₀.basicOpen (i.appLE (upOpen i U) U (preimage_upOpen i U).ge b) = _
  rw [Scheme.basicOpen_appLE]
  refine inf_eq_right.mpr ?_
  calc i ⁻¹ᵁ Y₁.basicOpen b ≤ i ⁻¹ᵁ upOpen i U := fun x hx => Y₁.basicOpen_le b hx
    _ = U := preimage_upOpen i U

theorem upOpen_basicOpen_res {Y₀ Y₁ : Scheme.{0}} (i : Y₀ ⟶ Y₁) [IsClosedImmersion i] [Surjective i]
    (U : Y₀.Opens) (b : Γ(Y₁, upOpen i U)) :
    upOpen i (Y₀.basicOpen ((res i U).hom b)) = Y₁.basicOpen b := by
  rw [basicOpen_res_eq, upOpen_preimage]

theorem basicOpen_fibπ_mem_good {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
    [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂] :
    ∀ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, ∀ a : (GlobalTheory.FerrandPush.fib i₁ i₂).obj (op U),
      Y₀.basicOpen (((GlobalTheory.FerrandPush.fibπ i₁ i₂).app (op U)).hom a) ∈
        GlobalTheory.FerrandPush.good i₁ i₂ := by
  intro U hU a
  obtain ⟨h0, h1, h2⟩ := hU
  have e1 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₁ U).hom ((cone i₁ i₂ U).fst.hom a) := rfl
  have e2 : ((fibπ i₁ i₂).app (op U)).hom a = (res i₂ U).hom ((cone i₁ i₂ U).snd.hom a) := by
    rw [e1]
    exact congrArg (fun f : (cone i₁ i₂ U).pt ⟶ Γ(Y₀, U) => f.hom a) (cone i₁ i₂ U).condition
  refine ⟨h0.basicOpen _, ?_, ?_⟩
  · rw [e1, upOpen_basicOpen_res]
    exact h1.basicOpen _
  · rw [e2, upOpen_basicOpen_res]
    exact h2.basicOpen _

end GlobalTheory.FerrandPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLe
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem lvlIdem_apply_of_mem_eig {Γ V : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (x : V) (hx : x ∈ eig ρ Hb lam) :
    ρ.asAlgebraHom (Formalism.L2.DIV.lvlIdem Hb lam) x = x := by
  classical
  rw [mem_eig] at hx
  have hc : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Formalism.L2.DIV.lvlIdem
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, hx, smul_smul]
  have e1 : ∀ h : Hb, (Nat.card Hb : ℂ)⁻¹ * ((lam h⁻¹ : ℂˣ) : ℂ) * ((lam h : ℂˣ) : ℂ) = (Nat.card Hb : ℂ)⁻¹ := fun h => by
    rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [e1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem finrank_eig_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  intro Γ V _ _ _ _ _ ρ Hb lam H n e b s c hemb hcard hidem hcomm he hsupp hcoeff
  set p := Formalism.L2.DIV.lvlIdem Hb lam with hp
  set W : Submodule ℂ V := eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) with hW
  let f : W →ₗ[ℂ] LinearMap.range (ρ.asAlgebraHom (b 0 * p)) × LinearMap.range (ρ.asAlgebraHom (b 1 * p)) :=
    ((ρ.asAlgebraHom (b 0 * p)).rangeRestrict.comp W.subtype).prod
      ((ρ.asAlgebraHom (b 1 * p)).rangeRestrict.comp W.subtype)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hxe, hxk⟩ hx0
    have h0 : ρ.asAlgebraHom (b 0 * p) x = 0 := by
      have := congrArg (fun z => ((z.1 : _) : V)) hx0; simpa [f] using this
    have h1 : ρ.asAlgebraHom (b 1 * p) x = 0 := by
      have := congrArg (fun z => ((z.2 : _) : V)) hx0; simpa [f] using this
    have hpx : ρ.asAlgebraHom p x = x := lvlIdem_apply_of_mem_eig ρ Hb lam x hxe
    have hb : ∀ k, ρ.asAlgebraHom (b k) x = ρ.asAlgebraHom (b k * p) x := fun k => by
      rw [map_mul, Module.End.mul_apply, hpx]
    have hb0 : ρ.asAlgebraHom (b 0) x = 0 := (hb 0).trans h0
    have hb1 : ρ.asAlgebraHom (b 1) x = 0 := (hb 1).trans h1
    have hek : ρ.asAlgebraHom e x = 0 := hxk
    have hx1 : x = ρ.asAlgebraHom (1 - e) x := by
      rw [map_sub, map_one, LinearMap.sub_apply, hek, sub_zero]; rfl
    have : x = 0 := by
      rw [hx1, he, map_sub, map_add (f := _), map_mul]
      simp [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, hb0, hb1]
    exact Subtype.ext this
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hdim
  have hbnd : ∀ k, (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤
      c * s k * finrank ℂ (eig ρ Hb lam) := by
    intro k
    have hid : b k * p * (b k * p) = b k * p := by
      calc b k * p * (b k * p) = b k * (p * b k) * p := by simp only [mul_assoc]
        _ = b k * (b k * p) * p := by rw [hcomm k]
        _ = (b k * b k) * (p * p) := by simp only [mul_assoc]
        _ = b k * p := by rw [hidem k, Formalism.L2.DIV.lvlIdem_idem]
    obtain ⟨r, hr, hle⟩ := _root_.GlobalTheory.BadCount.finrank_range_idem_le_of_embReg ℂ Γ V ρ (H k) (n k) (hemb k) (b k * p) (hsupp k) hid
    rw [hcoeff k] at hr
    have hHb : (0 : ℝ) < Nat.card Hb := by exact_mod_cast Nat.card_pos
    have hH : (0 : ℝ) < Nat.card (H k) := by exact_mod_cast Nat.card_pos
    have hrR : (r : ℝ) * Nat.card Hb = Nat.card (H k) * s k := by
      have hHbC : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast hHb.ne'
      have : ((r : ℝ) * Nat.card Hb : ℝ) = ((Nat.card (H k) * s k : ℝ) : ℂ) := by
        push_cast; rw [hr]; field_simp
      exact_mod_cast this
    have hs : 0 ≤ s k := by
      have : 0 ≤ (Nat.card (H k) : ℝ) * s k := by rw [← hrR]; positivity
      exact le_of_mul_le_mul_left (by simpa using this) hH
    have hd : (0 : ℝ) ≤ finrank ℂ (eig ρ Hb lam) := by positivity
    have hleR : (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤ n k * r := by exact_mod_cast hle
    have key : ((n k : ℝ) * r) * Nat.card Hb ≤ (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by
      calc ((n k : ℝ) * r) * Nat.card Hb = ((n k : ℝ) * Nat.card (H k)) * s k := by rw [mul_assoc, hrR]; ring
        _ ≤ (c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) * s k := mul_le_mul_of_nonneg_right (hcard k) hs
        _ = (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by ring
    exact hleR.trans (le_of_mul_le_mul_right key hHb)
  have hdimR : (finrank ℂ W : ℝ) ≤ (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 0 * p))) : ℝ) +
      finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 1 * p))) := by exact_mod_cast hdim
  calc (finrank ℂ W : ℝ) ≤ _ := hdimR
    _ ≤ c * s 0 * finrank ℂ (eig ρ Hb lam) + c * s 1 * finrank ℂ (eig ρ Hb lam) := add_le_add (hbnd 0) (hbnd 1)
    _ = c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by ring

end GlobalTheory.BadCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankEigenCoindMackeyDoubleCosets
section
noncomputable section

namespace GlobalTheory.FinGL.MackeyCosets

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem mem_eig' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ : G → ℂ) (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

variable {G : Type} [Group G] {P U : Subgroup G} {V : Type} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ P V) (χ : G → ℂ)

theorem left_eq (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (p : P) (g : G) :
    φ.1.1 (p * g) = σ p (φ.1.1 g) := φ.1.2 p g

theorem right_eq (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (u : G) (hu : u ∈ U) (g : G) :
    φ.1.1 (g * u) = χ u • φ.1.1 g := by
  have h := (mem_eig' _ _ _ _).1 φ.2 u hu
  exact congrArg (fun f : Representation.coindV P.subtype σ => f.1 g) h

theorem eval_mem (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (y : G) :
    φ.1.1 y ∈ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)) := by
  rw [mem_eig']
  intro p hp
  rw [← left_eq, ← right_eq σ χ φ _ hp]
  congr 1
  group

theorem eval_dc (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (y p u : G) (hp : p ∈ P) (hu : u ∈ U) :
    φ.1.1 (p * y * u) = χ u • σ ⟨p, hp⟩ (φ.1.1 y) := by
  rw [right_eq σ χ φ u hu, ← left_eq]

def evalMap {ι : Type} (x : ι → G) : eig (Representation.coind P.subtype σ) (U : Set G) χ →ₗ[ℂ]
    ∀ i : ι, eig σ {p | (x i)⁻¹ * (p : G) * x i ∈ U} (fun p => χ ((x i)⁻¹ * (p : G) * x i)) where
  toFun φ i := ⟨φ.1.1 (x i), eval_mem σ χ φ (x i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem key (hχ : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') (y : G) (v : V)
    (hv : v ∈ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)))
    (p p' : P) (u u' : G) (hu : u ∈ U) (hu' : u' ∈ U) (h : (p : G) * y * u = p' * y * u') :
    χ u • σ p v = χ u' • σ p' v := by
  have e : y⁻¹ * ((p'⁻¹ * p : P) : G) * y = u' * u⁻¹ := by
    have : u' = ((p' : G) * y)⁻¹ * (p * y * u) := by rw [h]; group
    rw [this]; push_cast; group
  have hm : u' * u⁻¹ ∈ U := U.mul_mem hu' (U.inv_mem hu)
  have h1 := (mem_eig' _ _ _ _).1 hv (p'⁻¹ * p) (by simp only [Set.mem_setOf_eq, e]; exact hm)
  simp only [e] at h1
  have h2 : σ p v = σ p' (σ (p'⁻¹ * p) v) := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have h3 : χ u' = χ (u' * u⁻¹) * χ u := by rw [← hχ _ hm _ hu]; simp
  rw [h2, h1, map_smul, smul_smul, h3, mul_comm]

theorem surj (h1 : χ 1 = 1) (hχ : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') {ι : Type} (x : ι → G)
    (hx : ∀ i i' : ι, ∀ p ∈ P, ∀ u ∈ U, p * x i = x i' * u → i = i') :
    Function.Surjective (evalMap (U := U) σ χ x) := by
  classical
  intro v
  let R : G → V → Prop := fun g w => ∃ i : ι, ∃ p : P, ∃ u ∈ U, g = p * x i * u ∧ w = χ u • σ p (v i).1
  have huniq : ∀ g w w', R g w → R g w' → w = w' := by
    rintro g w w' ⟨i, p, u, hu, rfl, rfl⟩ ⟨i', p', u', hu', h, rfl⟩
    have hi : i = i' := by
      refine hx i i' ((p' : G)⁻¹ * p) (P.mul_mem (P.inv_mem p'.2) p.2) (u' * u⁻¹) (U.mul_mem hu' (U.inv_mem hu)) ?_
      have : u' = ((p' : G) * x i')⁻¹ * (p * x i * u) := by rw [h]; group
      rw [this]; group
    subst hi
    exact key σ χ hχ (x i) _ (v i).2 p p' u u' hu hu' h
  let f : G → V := fun g => if h : ∃ w, R g w then h.choose else 0
  have hf : ∀ g w, R g w → f g = w := by
    intro g w hw
    have h : ∃ w, R g w := ⟨w, hw⟩
    simp only [f, dif_pos h]
    exact huniq g _ _ h.choose_spec hw
  have hf0 : ∀ g, (¬ ∃ w, R g w) → f g = 0 := by
    intro g h
    simp only [f, dif_neg h]
  have hL : ∀ (q : P) g w, R g w → R (q * g) (σ q w) := by
    rintro q g w ⟨i, p, u, hu, rfl, rfl⟩
    refine ⟨i, q * p, u, hu, by push_cast; group, ?_⟩
    rw [map_smul, map_mul, Module.End.mul_apply]
  have hR : ∀ t ∈ U, ∀ g w, R g w → R (g * t) (χ t • w) := by
    rintro t ht g w ⟨i, p, u, hu, rfl, rfl⟩
    refine ⟨i, p, u * t, U.mul_mem hu ht, by group, ?_⟩
    rw [hχ _ hu _ ht, smul_smul, mul_comm]
  have fL : ∀ (q : P) g, f (q * g) = σ q (f g) := by
    intro q g
    by_cases h : ∃ w, R g w
    · obtain ⟨w, hw⟩ := h
      rw [hf _ _ hw, hf _ _ (hL q g w hw)]
    · rw [hf0 g h, hf0, map_zero]
      rintro ⟨w, hw⟩
      have := hL q⁻¹ _ _ hw
      exact h ⟨_, by simpa using this⟩
  have fR : ∀ t ∈ U, ∀ g, f (g * t) = χ t • f g := by
    intro t ht g
    by_cases h : ∃ w, R g w
    · obtain ⟨w, hw⟩ := h
      rw [hf _ _ hw, hf _ _ (hR t ht g w hw)]
    · rw [hf0 g h, hf0, smul_zero]
      rintro ⟨w, hw⟩
      have := hR t⁻¹ (U.inv_mem ht) _ _ hw
      exact h ⟨_, by simpa using this⟩
  refine ⟨⟨⟨f, fL⟩, (mem_eig' _ _ _ _).2 fun t ht => ?_⟩, ?_⟩
  · ext g
    exact fR t ht g
  · funext i
    apply Subtype.ext
    exact hf _ _ ⟨i, 1, 1, U.one_mem, by simp, by simp [h1]⟩

theorem finrank_eig_coind : ∀ (G : Type) [Group G] (P U : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (σ : Representation ℂ P V) (χ : G → ℂ), χ 1 = 1 → (∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') → ∀ (ι : Type) [Fintype ι] (x : ι → G), (∀ i i' : ι, ∀ p ∈ P, ∀ u ∈ U, p * x i = x i' * u → i = i') → (∀ g : G, (∃ i : ι, ∃ p ∈ P, ∃ u ∈ U, g = p * x i * u) ∨ ∃ y : G, (∃ p ∈ P, ∃ u ∈ U, g = p * y * u) ∧ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)) = ⊥) → finrank ℂ (eig (Representation.coind P.subtype σ) (U : Set G) χ) = ∑ i : ι, finrank ℂ (eig σ {p | (x i)⁻¹ * (p : G) * x i ∈ U} (fun p => χ ((x i)⁻¹ * (p : G) * x i))) := by
  intro G _ P U V _ _ _ σ χ h1 hχ ι _ x hx hcov
  have hinj : Function.Injective (evalMap (U := U) σ χ x) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro φ hφ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change φ.1.1 g = 0
    rcases hcov g with ⟨i, p, hp, u, hu, rfl⟩ | ⟨y, ⟨p, hp, u, hu, rfl⟩, hy⟩
    · have : φ.1.1 (x i) = 0 := congrArg Subtype.val (congrFun hφ i)
      rw [eval_dc σ χ φ _ _ _ hp hu, this, map_zero, smul_zero]
    · have : φ.1.1 y = 0 := by
        have := eval_mem σ χ φ y
        rwa [hy, Submodule.mem_bot] at this
      rw [eval_dc σ χ φ _ _ _ hp hu, this, map_zero, smul_zero]
  rw [(LinearEquiv.ofBijective _ ⟨hinj, surj σ χ h1 hχ x hx⟩).finrank_eq, Module.finrank_pi_fintype]

end GlobalTheory.FinGL.MackeyCosets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerDecompositionFockNoncompactParts
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial GlobalTheory.JointHarm

namespace GlobalTheory.FischerParts

theorem exists_fockIP (σ : Type) [DecidableEq σ] :
    ∃ ι : MvPolynomial σ ℂ →ₗ[ℂ] lp (fun _ : σ →₀ ℕ => ℂ) 2,
      IsFockIP ι ∧ Function.Injective ι := by
  classical
  let w : (σ →₀ ℕ) → ℕ := fun α => α.prod fun _ k => k.factorial
  have hw : ∀ α, w α ≠ 0 := fun α => Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _
  let v : (σ →₀ ℕ) → lp (fun _ : σ →₀ ℕ => ℂ) 2 := fun α => lp.single 2 α (√(w α) : ℝ)
  have hv : ∀ α β, inner ℂ (v α) (v β) = if α = β then (w α : ℂ) else 0 := by
    intro α β
    simp only [v, lp.inner_single_left, lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      simp only [RCLike.inner_apply, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
    · simp
  refine ⟨(basisMonomials σ ℂ).constr ℂ v, fun α β => ?_, ?_⟩
  · have e : ∀ α, (basisMonomials σ ℂ).constr ℂ v (monomial α 1) = v α := fun α => by
      have := (basisMonomials σ ℂ).constr_basis ℂ v α
      rwa [coe_basisMonomials] at this
    rw [e, e, hv]
    simp [w, Finsupp.prod]
  · refine (basisMonomials σ ℂ).injective_constr_of_linearIndependent ?_
    refine linearIndependent_of_ne_zero_of_inner_eq_zero (fun α h => hw α ?_) fun α β h => ?_
    · have := hv α α
      rw [h, inner_zero_left, if_pos rfl] at this
      exact_mod_cast this.symm
    · exact (hv α β).trans (if_neg h)

theorem fischer_parts : ∀ (p q r s d : ℕ), (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm2 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (harm1 p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) ∧ (homog (Ix p q × Ix r s) (d + 2) = (homog (Ix p q × Ix r s) (d + 2) ⊓ Submodule.span ℂ (jointHarm p q r s)) ⊔ Submodule.span ℂ {R | ∃ Q ∈ homog (Ix p q × Ix r s) d, (∃ Z : Mat p q, IsPC Z ∧ R = plusPart (fockAct1 p q r s Z) Q) ∨ ∃ Z : Mat r s, IsPC Z ∧ R = plusPart (fockAct2 p q r s Z) Q}) := by
  intro p q r s d
  obtain ⟨ι, hι, hinj⟩ := exists_fockIP (Ln p q r s)
  refine ⟨fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron1 r s Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | ∃ Z, IsPC Z ∧ M = kron2 p q Z} ?_ ?_ d _ _ (fun P hP => ?_)
      fun P => ?_,
    fischer hι hinj {M | (∃ Z, IsPC Z ∧ M = kron1 r s Z) ∨ ∃ Z, IsPC Z ∧ M = kron2 p q Z}
      ?_ ?_ d _ _ (fun P hP => ?_) fun P => ?_⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron1 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ ⟨Z, hZ, rfl⟩
    exact odd_kron2 hZ
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ⟨_, ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩
  · exact fun Z hZ => hP _ ⟨Z, hZ, rfl⟩
  · constructor
    · rintro ⟨Q, hQ, Z, hZ, rfl⟩
      exact ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩, rfl⟩
      exact ⟨Q, hQ, Z, hZ, rfl⟩
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [odd_kron1 hZ, odd_kron2 hZ]
  · rintro _ (⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩)
    exacts [⟨_, .inl ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerLeftMatrix_conjTranspose Z⟩,
      ⟨_, .inr ⟨_, isPC_conjTranspose hZ, rfl⟩, lineKroneckerRightMatrix_conjTranspose Z⟩]
  · exact ⟨fun Z hZ => hP _ (.inl ⟨Z, hZ, rfl⟩), fun Z hZ => hP _ (.inr ⟨Z, hZ, rfl⟩)⟩
  · constructor
    · rintro ⟨Q, hQ, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩⟩
      exacts [⟨Q, hQ, _, .inl ⟨Z, hZ, rfl⟩, rfl⟩, ⟨Q, hQ, _, .inr ⟨Z, hZ, rfl⟩, rfl⟩]
    · rintro ⟨Q, hQ, _, ⟨Z, hZ, rfl⟩ | ⟨Z, hZ, rfl⟩, rfl⟩
      exacts [⟨Q, hQ, .inl ⟨Z, hZ, rfl⟩⟩, ⟨Q, hQ, .inr ⟨Z, hZ, rfl⟩⟩]

end GlobalTheory.FischerParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHens
section
open IsLocalRing GlobalTheory.Henselisation

noncomputable section

namespace GlobalTheory.Henselisation

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem Hens.of_trans {i j : EtNbhd R} (h : i ≤ j) (y : i.B) :
    Hens.of j (EtNbhd.trans h y) = Hens.of i y :=
  Ring.DirectLimit.of_f h y

theorem Hens.exists_of (hdir : IsDirected (EtNbhd R) (· ≤ ·)) (z : Hens R) :
    ∃ (i : EtNbhd R) (y : i.B), Hens.of i y = z :=
  haveI : IsDirectedOrder (EtNbhd R) := hdir
  Ring.DirectLimit.exists_of (G := fun i : EtNbhd R => i.B)
    (f := fun _ _ h => ⇑(EtNbhd.trans h)) z

theorem Hens.exists_of_fin (hdir : IsDirected (EtNbhd R) (· ≤ ·)) :
    ∀ (l : ℕ) (x : Fin l → Hens R), ∃ (i : EtNbhd R) (y : Fin l → i.B), ∀ k, Hens.of i (y k) = x k := by
  intro l
  induction l with
  | zero => exact fun x => ⟨EtNbhd.base, fun k => k.elim0, fun k => k.elim0⟩
  | succ l ih =>
    intro x
    obtain ⟨i, y, hy⟩ := ih (fun k => x k.castSucc)
    obtain ⟨j, z, hz⟩ := Hens.exists_of hdir (x (Fin.last l))
    obtain ⟨m, him, hjm⟩ := directed_of (· ≤ ·) i j
    refine ⟨m, Fin.lastCases (EtNbhd.trans hjm z) (fun k => EtNbhd.trans him (y k)), ?_⟩
    intro k
    induction k using Fin.lastCases with
    | last => dsimp only; rw [Fin.lastCases_last, Hens.of_trans, hz]
    | cast k => dsimp only; rw [Fin.lastCases_castSucc, Hens.of_trans, hy]

theorem flat_hens_of_stages (hdir : IsDirected (EtNbhd R) (· ≤ ·))
    (hinj : ∀ i : EtNbhd R, Function.Injective (Hens.of i))
    (halg : ∀ (i : EtNbhd R) (r : R), Hens.of i (algebraMap R i.B r) = algebraMap R (Hens R) r)
    (hflat : ∀ i : EtNbhd R, Module.Flat R i.B) : Module.Flat R (Hens R) := by
  have hsmul : ∀ (i : EtNbhd R) (r : R) (y : i.B), Hens.of i (r • y) = r • Hens.of i y := by
    intro i r y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halg]
  refine Module.Flat.iff_forall_isTrivialRelation.mpr ?_
  intro l f x hfx
  obtain ⟨i, y, hy⟩ := Hens.exists_of_fin hdir l x
  have h0 : ∑ k, f k • y k = 0 := by
    apply hinj i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum]
    simp only [hsmul, hy]
    exact hfx
  obtain ⟨k, a, z, hya, haf⟩ := Module.Flat.iff_forall_isTrivialRelation.mp (hflat i) h0
  refine ⟨k, a, fun j => Hens.of i (z j), fun m => ?_, haf⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hy m, hya m, map_sum]
  simp only [hsmul]

theorem flat_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) :=
  fun R _ _ => flat_hens_of_stages (_root_.GlobalTheory.Henselisation.etNbhd_isDirected R) (_root_.GlobalTheory.Henselisation.Hens.of_injective_of_nbhd R) (_root_.GlobalTheory.Henselisation.Hens.of_algebraMap R) (_root_.GlobalTheory.Henselisation.EtNbhd.flat_B R)

end GlobalTheory.Henselisation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStabiliserMapsToCompletedLatticeStatement
section
open NumberField
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameStabiliser_mapsTo_completedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ → ∀ x ∈ Formalism.L2.DIV.St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  first | exact @GlobalTheory.stab_hatL_mapsTo | exact GlobalTheory.stab_hatL_mapsTo | (intros; apply GlobalTheory.stab_hatL_mapsTo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreBaseChangeInjective
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_base_change_injective : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA) P₁ := by
  first | (exact @GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser) | (exact GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser) | (intros; apply GlobalTheory.AbhHeightOne.closureEtaleAt_of_root_of_uniformiser  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerVanishingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_etale_vanishing : GlobalTheory.EtC.B6h1 := by
  first | (exact @GlobalTheory.EtC.kummer_vanishing) | (exact GlobalTheory.EtC.kummer_vanishing) | (intros; apply GlobalTheory.EtC.kummer_vanishing  <;> assumption)
end

