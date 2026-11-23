module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMobiusInverseMonicEq
section
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem mass_comp_charpoly_eq_mul (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (P : F[X]) :
    mass (fun g : Module.End F V => s (LinearMap.charpoly g)) P =
      s P * mass (fun _ : Module.End F V => (1 : ℂ)) P := by
  have : Finite (Module.End F V) := Module.finite_of_finite F
  unfold mass
  have hfin : ({g : Module.End F V | LinearMap.charpoly g = P}).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have : LinearMap.charpoly g = P := by simpa using hg
  simp [this]

theorem mass_psi_eq_glCard_mul_mangoldt_div :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (s : F[X] → ℂ), IsAdditive s → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V →
      mass (psi s V) P = glCard F P.natDegree * mangoldt s P / ((Nat.card F : ℂ) ^ P.natDegree - 1) := by
  intro F _ _ V _ _ _ s hs P hP hdeg
  have hiso := _root_.GlobalTheory.CuspGL.psi_conj F s
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hmu1 : mu (1 : F[X]) = 1 := (_root_.GlobalTheory.CuspGL.mu_rec F 1 monic_one).2
  have hlog := GlobalTheory.T.additive_mul_eq_vonMangoldt_convolution F (Nat.card F) hq s mu hs hmu1 (fun Q hQ => (_root_.GlobalTheory.CuspGL.mu_rec F Q hQ).1)
  have hmul : ∀ Q : F[X], Q.Monic → s Q * mu Q =
      conv (fun D => mass (psi s (Fin D.natDegree → F)) D / glCard F D.natDegree) mu Q := by
    intro Q hQ
    have h := _root_.GlobalTheory.CuspGL.MassMult.mass_mult F (Fin Q.natDegree → F) (fun V _ _ _ => psi s V) hiso Q hQ (by simp)
    have h2 : (fun g : Module.End F (Fin Q.natDegree → F) =>
        ∑ᶠ W : {W : Submodule F (Fin Q.natDegree → F) // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2)) =
        fun g => s (LinearMap.charpoly g) := by
      funext g
      exact (_root_.GlobalTheory.CuspGL.charpoly_eq_finsum_psi F _ s g).symm
    rw [← h]
    rw [h2, mass_comp_charpoly_eq_mul, mu, mul_div_assoc]
  have hc := _root_.GlobalTheory.CuspGL.ConvCancel.conv_cancel F _ _ mu hmu1 (fun Q hQ => (hmul Q hQ).symm.trans (hlog Q hQ)) P hP
  have hV := _root_.GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant F V (fun V _ _ _ => psi s V) hiso P hdeg
  have hg : glCard F P.natDegree ≠ 0 := by
    unfold glCard
    exact_mod_cast (Nat.card_pos (α := GL (Fin P.natDegree) F)).ne'
  rw [hV, mul_div_assoc, ← hc, mul_div_cancel₀ _ hg]

end GlobalTheory.CuspGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEqStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ) (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ k l i : ℕ, k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)] → ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) = ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) := by
  first | exact @GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq | exact GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq | (intros; apply GlobalTheory.CuspGL.ipGL_rootSum_eq_of_modEq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldAbelianByPrimePower
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_abByP : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → AbByP G → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ
  have key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → (∀ g : G, g ^ m = 1) → AbByP G →
      ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro G _ _ hn hG hA χ hχ
      refine _root_.GlobalTheory.BI.isChar_induction L L G (fun a => IsChar K L a) (_root_.GlobalTheory.BI.isChar_zero_and_add K L G).1 ?_ χ hχ
      intro φ c hφ _ hc
      refine (_root_.GlobalTheory.BI.isChar_zero_and_add K L G).2 φ c ?_ hc
      rcases _root_.GlobalTheory.BI.irrChar_linear_or_induced L G φ hA hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have : φ = fun g => (lam g : L) := funext hlam
        rw [this]
        exact _root_.GlobalTheory.BI.isChar_linear K L G m ζ lam hm hζ hG
      · have hlt : Nat.card T < n := by
          rw [← hn]
          exact lt_of_le_of_ne (Subgroup.card_le_card_group T)
            (fun h => hT (Subgroup.eq_top_of_card_eq T h))
        refine _root_.GlobalTheory.BI.isChar_ind K L G T ψ (ih _ hlt T rfl ?_ (_root_.GlobalTheory.BI.AbByP.subgroup G T hA) ψ hψ)
        intro g
        exact Subtype.ext (by simpa using hG g)
  intro G _ _
  exact key _ G rfl
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacter
section
open GlobalTheory.BI
namespace GlobalTheory.BI

private theorem isChar_of_isIrrChar (K L : Type) [Field K] [Field L]
    [Algebra K L] {G : Type} [Group G] (φ : G → L) (hφ : _root_.GlobalTheory.BI.IsIrrChar K L φ) :
    _root_.GlobalTheory.BI.IsChar K L φ := by
  obtain ⟨n, ρ, _, hρ⟩ := hφ
  exact ⟨n, ρ, hρ⟩

theorem _root_.GlobalTheory.BI.isChar_of_isChar_of_mem_virt (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
    (G : Type) [Group G] [Finite G] (χ : G → L) (hχ : _root_.GlobalTheory.BI.IsChar L L χ) (hv : χ ∈ _root_.GlobalTheory.BI.Virt K L G) :
    _root_.GlobalTheory.BI.IsChar K L χ := by
  obtain ⟨a, b, ha, hb, hab⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub K L G χ).1 hv
  obtain ⟨hadd, hnat, hpos, -⟩ := _root_.GlobalTheory.BI.pair_add_nat_pos_symm K L G
  obtain ⟨-, hnatL, -, -⟩ := _root_.GlobalTheory.BI.pair_add_nat_pos_symm L L G
  have key : ∀ c : G → L, _root_.GlobalTheory.BI.IsChar K L c →
      ∀ a : G → L, _root_.GlobalTheory.BI.IsChar K L a → a = χ + c → _root_.GlobalTheory.BI.IsChar K L χ := by
    refine _root_.GlobalTheory.BI.isChar_induction K L G _ ?_ ?_
    · intro a ha h
      rw [add_zero] at h
      exact h ▸ ha
    · intro φ c hφ hc ih a ha h
      have hφc := isChar_of_isIrrChar K L φ hφ
      obtain ⟨n₁, h₁⟩ := hnatL χ φ hχ (_root_.GlobalTheory.BI.isChar_baseChange K L G φ hφc)
      obtain ⟨n₂, hn₂, h₂⟩ := hpos φ hφ
      obtain ⟨n₃, h₃⟩ := hnat c φ hc hφc
      have hne : _root_.GlobalTheory.BI.pair a φ ≠ 0 := by
        rw [h, hadd, hadd, h₁, h₂, h₃]
        exact_mod_cast (by omega : n₁ + (n₂ + n₃) ≠ 0)
      obtain ⟨a', ha', ha'eq⟩ := _root_.GlobalTheory.BI.exists_isChar_eq_add_of_pair_ne_zero K L G φ a hφ ha hne
      refine ih a' ha' ?_
      have : φ + a' = φ + (χ + c) := by
        rw [← ha'eq, h]
        abel
      exact add_left_cancel this
  exact key b hb a ha (by rw [hab]; abel)

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobi
section
open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.PsiPrimitive

open scoped Classical

open Classical in
theorem finsum_sub {α : Type} [Fintype α] (p : α → Prop) (f : {a // p a} → ℂ) :
    ∑ᶠ x, f x = ∑ a, if h : p a then f ⟨a, h⟩ else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : ∀ i : {a // p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = f i := fun i => by
    rw [dite_eq_left i.2]
  have h2 : ∀ i : {a // ¬ p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0 := fun i => by
    rw [dite_eq_right i.2]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]


open Classical in
def res {F : Type} [Field F] (s : F[X] → ℂ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) (k : Module.End F V) : ℂ :=
  if hk : ∀ x ∈ W, k x ∈ W then psi s W (k.restrict hk) else 0

theorem psi_trivial {F : Type} [Field F] (s : F[X] → ℂ) (hs : IsAdditive s) (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Subsingleton V] (g : Module.End F V) :
    psi s V g = 0 := by
  rw [psi_eq s V g]
  have hpoly : LinearMap.charpoly g = 1 := by
    have hdeg : (LinearMap.charpoly g).natDegree = 0 := by
      rw [LinearMap.charpoly_natDegree]
      exact Module.finrank_zero_of_subsingleton
    exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic g) hdeg
  have hs1 : s 1 = 0 := by
    have h11 := hs 1 1 monic_one monic_one
    rw [one_mul] at h11
    linear_combination -h11
  have hempty : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} := by
    refine ⟨fun W => W.2.1 ?_⟩
    refine eq_top_iff.2 fun x _ => ?_
    rw [Subsingleton.elim x 0]
    exact W.1.zero_mem
  rw [hpoly, hs1, finsum_of_isEmpty, sub_zero]

theorem res_top {F : Type} [Field F] (s : F[X] → ℂ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (k : Module.End F V) : res s ⊤ k = psi s V k := by
  have htop : ∀ x ∈ (⊤ : Submodule F V), k x ∈ (⊤ : Submodule F V) := fun _ _ => Submodule.mem_top
  unfold res
  rw [dite_eq_left htop]
  have hconj := _root_.GlobalTheory.CuspGL.psi_conj F s (⊤ : Submodule F V) V Submodule.topEquiv (k.restrict htop)
  rw [← hconj]
  congr 1

theorem step {F : Type} [Field F] [Finite F] (s : F[X] → ℂ) (hs : IsAdditive s) (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ih : ∀ W : Submodule F V, W ≠ ⊤ → IsPrimitive (psi s W)) : IsPrimitive (psi s V) := by
  classical
  have : Finite V := Module.finite_of_finite F
  have : Finite (Module.End F V) :=
    Finite.of_injective (fun f : Module.End F V => (f : V → V)) fun a b h => LinearMap.ext (congrFun h)
  have : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  let _ : Fintype (Module.End F V) := Fintype.ofFinite _
  let _ : Fintype (Submodule F V) := Fintype.ofFinite _
  intro A hA0 hAT g hg
  set H : Finset (Module.End F V) := Finset.univ.filter fun h => h ∈ nilRad A with hH
  have memH : ∀ h, h ∈ H ↔ h ∈ nilRad A := fun h => by simp [hH]
  have sum_H : ∀ f : Module.End F V → ℂ,
      ∑ h ∈ H, f h = ∑ h, if h ∈ nilRad A then f h else 0 := fun f => by
    rw [hH, Finset.sum_filter]
  have card_H : ((Nat.card (nilRad A) : ℕ) : ℂ) = (H.card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have res_bot : ∀ k : Module.End F V, res s (⊥ : Submodule F V) k = 0 := by
    intro k
    unfold res
    split_ifs
    · exact psi_trivial s hs _ _
    · rfl
  have s_cp : ∀ k : Module.End F V, s (LinearMap.charpoly k) = ∑ W : Submodule F V, res s W k := by
    intro k
    exact (_root_.GlobalTheory.CuspGL.charpoly_eq_finsum_psi F V s k).trans
      (finsum_sub (fun W : Submodule F V => ∀ x ∈ W, k x ∈ W) fun W => psi s W.1 (k.restrict W.2))
  have res_le : ∀ h ∈ nilRad A, ∀ W : Submodule F V, W ≤ A → res s W (g + h) = res s W g := by
    intro h hh W hWA
    have hh' : (∀ x, h x ∈ A) ∧ ∀ x ∈ A, h x = 0 := hh
    have h0 : ∀ x ∈ W, h x = 0 := fun x hx => hh'.2 x (hWA hx)
    unfold res
    by_cases hk : ∀ x ∈ W, g x ∈ W
    · have hk' : ∀ x ∈ W, (g + h) x ∈ W := fun x hx => by
        simpa [h0 x hx] using hk x hx
      rw [dite_eq_left hk', dite_eq_left hk]
      congr 1
      ext x
      simp [h0 x.1 x.2]
    · have hk' : ¬ ∀ x ∈ W, (g + h) x ∈ W := fun hk' => hk fun x hx => by
        simpa [h0 x hx] using hk' x hx
      rw [dite_eq_right hk', dite_eq_right hk]
  have res_mixed : ∀ W : Submodule F V, W ≠ ⊤ → W ⊓ A ≠ ⊥ → ¬ W ≤ A →
      ∑ h ∈ H, res s W (g + h) = 0 := by
    intro W hWT hWA hWle
    have key := (finsum_sub (fun h : Module.End F V => h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W)
      fun h => psi s W ((g + h.1).restrict h.2.2)).symm.trans
        (GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace F V A W g hg hWA hWle (psi s W) (ih W hWT))
    rw [← key, sum_H]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hh : h ∈ nilRad A <;> simp [hh, res]
  have sum_le : ∑ W : Submodule F V, (if W ≤ A then res s W g else 0) =
      s (LinearMap.charpoly (g.restrict hg)) := by
    have key := (finsum_sub (fun W : Submodule F V => W ≤ A ∧ ∀ x ∈ W, g x ∈ W)
      fun W => psi s W.1 (g.restrict W.2.2)).symm.trans (_root_.GlobalTheory.CuspGL.finsum_psi_le F V s A g hg)
    rw [← key]
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hW : W ≤ A <;> by_cases hk : ∀ x ∈ W, g x ∈ W <;> simp [hW, hk, res]
  have sum_disj : ∑ W : Submodule F V,
      (if W ⊓ A = ⊥ then ∑ h ∈ H, res s W (g + h) else 0) =
      (H.card : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
    have key := (finsum_sub
      (fun x : Module.End F V × Submodule F V =>
        x.1 ∈ nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2)
      fun x => psi s x.1.2 ((g + x.1.1).restrict x.2.2.2)).symm.trans (GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces F V s A g hg)
    rw [← card_H, ← key, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hW : W ⊓ A = ⊥
    · rw [if_pos hW, sum_H]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases hh : h ∈ nilRad A <;> simp [hh, hW, res]
    · rw [if_neg hW]
      symm
      refine Finset.sum_eq_zero fun h _ => ?_
      simp [hW]
  have split : ∀ W : Submodule F V, W ≠ ⊤ →
      ∑ h ∈ H, res s W (g + h) =
        (if W ⊓ A = ⊥ then ∑ h ∈ H, res s W (g + h) else 0) +
          (if W ≤ A then (H.card : ℂ) * res s W g else 0) := by
    intro W hWT
    by_cases hb : W = ⊥
    · subst hb
      simp [res_bot]
    by_cases hle : W ≤ A
    · have hmeet : W ⊓ A ≠ ⊥ := by rw [inf_eq_left.2 hle]; exact hb
      rw [if_neg hmeet, if_pos hle, zero_add,
        Finset.sum_congr rfl fun h hh => res_le h ((memH h).1 hh) W hle, Finset.sum_const, nsmul_eq_mul]
    by_cases hd : W ⊓ A = ⊥
    · rw [if_pos hd, if_neg hle, add_zero]
    · rw [if_neg hd, if_neg hle, add_zero]
      exact res_mixed W hWT hd hle
  have s_split : s (LinearMap.charpoly g) = s (LinearMap.charpoly (g.restrict hg)) +
      s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
    rw [(_root_.GlobalTheory.CuspGL.charpoly_block F V A g hg).1]
    exact hs _ _ (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _)
  have s_const : ∑ h ∈ H, s (LinearMap.charpoly (g + h)) = (H.card : ℂ) * s (LinearMap.charpoly g) := by
    rw [Finset.sum_congr rfl fun h hh => by rw [(_root_.GlobalTheory.CuspGL.charpoly_block F V A g hg).2 h ((memH h).1 hh)],
      Finset.sum_const, nsmul_eq_mul]
  have psi_expand : ∀ k : Module.End F V, psi s V k =
      s (LinearMap.charpoly k) - ∑ W ∈ Finset.univ.erase ⊤, res s W k := by
    intro k
    rw [s_cp, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⊤), res_top]
    ring
  have proper : ∑ W ∈ Finset.univ.erase ⊤, ∑ h ∈ H, res s W (g + h) =
      (H.card : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) +
        (H.card : ℂ) * s (LinearMap.charpoly (g.restrict hg)) := by
    rw [Finset.sum_congr rfl fun W hW => split W (Finset.ne_of_mem_erase hW), Finset.sum_add_distrib]
    have htop1 : ¬ (⊤ : Submodule F V) ⊓ A = ⊥ := by rw [top_inf_eq]; exact hA0
    have htop2 : ¬ (⊤ : Submodule F V) ≤ A := fun h => hAT (top_le_iff.1 h)
    rw [Finset.sum_erase _ (by rw [if_neg htop1]), Finset.sum_erase _ (by rw [if_neg htop2]),
      sum_disj, ← sum_le, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun W _ => ?_
    split_ifs <;> simp
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  simp only [Set.indicator_apply]
  rw [← sum_H, Finset.sum_congr rfl fun h _ => psi_expand (g + h), Finset.sum_sub_distrib,
    Finset.sum_comm, proper, s_const, s_split]
  ring

end GlobalTheory.CuspGL.PsiPrimitive

namespace GlobalTheory.CuspGL

theorem isPrimitive_psi : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by
  intro F _ _ V _ _ _ s hs
  suffices key : ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
      Module.finrank F V < n → IsPrimitive (psi s V) from key _ V (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro V _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro V _ _ _ h
    exact PsiPrimitive.step s hs V fun W hW =>
      ih W (lt_of_lt_of_le (Submodule.finrank_lt hW) (Nat.lt_succ_iff.1 h))

end GlobalTheory.CuspGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersOfAbelianByPrimePowerStatement
section
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G], (∀ H : Subgroup G, AbByP H → ∀ ψ : H → L, IsChar L L ψ → IsChar K L ψ) → ∀ χ : G → L, IsChar L L χ → χ ∈ Virt K L G := by
  first | exact @GlobalTheory.BI.mem_virt_of_forall_abByP | exact GlobalTheory.BI.mem_virt_of_forall_abByP | (intros; apply GlobalTheory.BI.mem_virt_of_forall_abByP <;> assumption)
end

