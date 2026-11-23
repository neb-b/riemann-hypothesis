module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.Torus2GammaBijective
public import Formalism.GL3MeanSquares.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.BottomMinor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055
public import ReciprocityTheory.GaloisValuations.Global

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
section
open TensorProduct Coalgebra AddMonoidAlgebra

namespace GlobalTheory

section Units

variable {A : Type*} [CommRing A] {X : Type*} [AddCommGroup X]

variable [IsDomain A]

variable [Module.Free ℤ X]


end Units

section Coordinates

variable {X : Type*} [Zero X] {N : Type*} [AddCommGroup N]

theorem coboundary_apply_zero_left (g : X →₀ N) (x : X) :
    (g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) (0, x) = g x := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
    rw [← hf, ← hg]; abel
  | single y m =>
    simp only [Finsupp.mapDomain_single, Finsupp.add_apply, Finsupp.sub_apply,
      Finsupp.single_apply, Prod.mk.injEq]
    by_cases h : y = 0
    · subst h; simp
    · simp [h]

theorem finsupp_two_cocycle_eq_coboundary (f : X × X →₀ N)
    (hf : f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
      f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) = 0)
    (g : X →₀ N) (hg : ∀ x, g x = f (0, x)) :
    g.mapDomain (fun y => ((0 : X), y)) - g.mapDomain (fun y => (y, y)) +
      g.mapDomain (fun y => (y, (0 : X))) = f := by
  classical
  let s : (X × X →₀ N) →+ (X →₀ N) :=
    Finsupp.comapDomain.addMonoidHom (f := fun x => ((0 : X), x)) (Prod.mk_right_injective 0)
  have hs : ∀ f x, s f x = f (0, x) := fun _ _ => rfl
  have key : ∀ (f : X × X →₀ N) (q : X × X),
      (f.mapDomain (fun p => ((0 : X), p.1, p.2)) - f.mapDomain (fun p => (p.1, p.1, p.2)) +
        f.mapDomain (fun p => (p.1, p.2, p.2)) - f.mapDomain (fun p => (p.1, p.2, (0 : X))) :
          X × X × X →₀ N) (0, q) +
      ((s f).mapDomain (fun y => ((0 : X), y)) - (s f).mapDomain (fun y => (y, y)) +
        (s f).mapDomain (fun y => (y, (0 : X))) : X × X →₀ N) q = f q := by
    intro f q
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      simp only [map_add (f := _), Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.sub_apply] at hf hg ⊢
      rw [← hf, ← hg]; abel
    | single p m =>
      obtain ⟨y, z⟩ := p
      by_cases h : y = 0
      · subst h
        have : s (Finsupp.single (0, z) m) = Finsupp.single z m := by
          ext x; simp [hs, Finsupp.single_apply]
        simp [this, Finsupp.single_apply]
      · have : s (Finsupp.single (y, z) m) = 0 := by
          ext x; simp [hs, h]
        simp [this, Finsupp.single_apply, h]
  have e : g = s f := Finsupp.ext hg
  ext q
  rw [← key f q, hf, e]
  simp

end Coordinates

section Ring

variable {X : Type*} [Zero X] {A : Type*} [Ring A]

theorem addMonoidAlgebra_coboundary_eq_iff (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0)
    (g : A[X]) :
    mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f ↔ ∀ x, g.coeff x = f.coeff (0, x) := by
  refine ⟨fun h x => ?_, fun h => coeff_injective
    (finsupp_two_cocycle_eq_coboundary f.coeff (congrArg coeff hf) g.coeff h)⟩
  rw [← h]
  exact (coboundary_apply_zero_left g.coeff x).symm

theorem addMonoidAlgebra_existsUnique_coboundary (f : A[X × X])
    (hf : mapDomain (fun p => ((0 : X), p.1, p.2)) f - mapDomain (fun p => (p.1, p.1, p.2)) f +
      mapDomain (fun p => (p.1, p.2, p.2)) f - mapDomain (fun p => (p.1, p.2, (0 : X))) f = 0) :
    ∃! g : A[X], mapDomain (fun y => ((0 : X), y)) g - mapDomain (fun y => (y, y)) g +
      mapDomain (fun y => (y, (0 : X))) g = f := by
  simp only [addMonoidAlgebra_coboundary_eq_iff f hf]
  exact ⟨ofCoeff (f.coeff.comapDomain (fun x => ((0 : X), x)) (Prod.mk_right_injective 0).injOn),
    fun _ => rfl, fun g hg => coeff_injective (Finsupp.ext hg)⟩

end Ring

section Tensor

variable {R : Type*} [CommRing R] {H : Type*} [Ring H] [Bialgebra R H]
variable {M : Type*} [AddCommGroup M] [Module R M]


variable {X : Type*} [AddMonoid X]


end Tensor

universe u v w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacobiSymNegEqOfThreeModFour
section
namespace GlobalTheory

theorem jacobiSym_neg_eq_of_three_mod_four (q n : ℕ) (hq : q % 4 = 3) (hn : Odd n) :
    jacobiSym (-(q : ℤ)) n = jacobiSym (n : ℤ) q := by
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [jacobiSym.neg _ hn]
  have h4 : n % 4 = 1 ∨ n % 4 = 3 := by omega
  rcases h4 with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four h hqo]
  · rw [ZMod.χ₄_nat_three_mod_four h,
      jacobiSym.quadratic_reciprocity_three_mod_four hq h]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JointHarmonicOfHookNorm
section
noncomputable section

namespace GlobalTheory.JointHarm

open MvPolynomial Matrix

section Minors

variable {R : Type*} [CommRing R]

variable {n l : ℕ}

end Minors

variable {n p q : ℕ}

section Killed

end Killed

section Fock

open Formalism.E

theorem fock_add_left {σ : Type} (P P' Q : MvPolynomial σ ℂ) :
    fock (P + P') Q = fock P Q + fock P' Q := by
  classical
  have key : ∀ (F : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)), F.support ⊆ s →
      fock F Q = ∑ m ∈ s, F.coeff m * star (Q.coeff m) * (Formalism.A.mfact m : ℂ) := by
    intro F s hs
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [notMem_support_iff.mp hm, zero_mul, zero_mul]
  rw [key _ _ support_add, key P _ Finset.subset_union_left, key P' _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fock_monomial_left {σ : Type} (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    fock (monomial α c) Q = c * star (Q.coeff α) * (Formalism.A.mfact α : ℂ) := by
  classical
  unfold fock
  rw [support_monomial]
  split_ifs with hc
  · simp [hc]
  · simp

variable {σ₁ σ₂ τ : Type} {f : σ₁ → τ} {g : σ₂ → τ}

theorem mapDomain_add_inj (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) {α α' : σ₁ →₀ ℕ} {β β' : σ₂ →₀ ℕ}
    (h : α.mapDomain f + β.mapDomain g = α'.mapDomain f + β'.mapDomain g) : α = α' ∧ β = β' := by
  constructor
  · ext x
    have := DFunLike.congr_fun h (f x)
    have hx : f x ∉ Set.range g := fun ⟨y, hy⟩ => hfg x y hy.symm
    simpa [Finsupp.mapDomain_apply_of_injective hf, Finsupp.mapDomain_notin_range _ _ hx] using this
  · ext y
    have := DFunLike.congr_fun h (g y)
    have hy : g y ∉ Set.range f := fun ⟨x, hx⟩ => hfg x y hx
    simpa [Finsupp.mapDomain_apply_of_injective hg, Finsupp.mapDomain_notin_range _ _ hy] using this

theorem coeff_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) (P : MvPolynomial σ₁ ℂ)
    (Q : MvPolynomial σ₂ ℂ) :
    AddMonoidAlgebra.coeff (rename f P * rename g Q) (α.mapDomain f + β.mapDomain g) = AddMonoidAlgebra.coeff P α * AddMonoidAlgebra.coeff Q β := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P P' h h' => simp only [map_add (f := _), add_mul, MvPolynomial.coeff_add, h, h']
  | monomial α' x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q Q' h h' => simp only [map_add (f := _), mul_add, MvPolynomial.coeff_add, h, h']
    | monomial β' y =>
      rw [rename_monomial, rename_monomial, monomial_mul, coeff_monomial, coeff_monomial,
        coeff_monomial]
      by_cases h : α'.mapDomain f + β'.mapDomain g = α.mapDomain f + β.mapDomain g
      · obtain ⟨rfl, rfl⟩ := mapDomain_add_inj hf hg hfg h
        simp
      · rw [if_neg h]
        split_ifs with h1 h2
        · exact absurd (by rw [h1, h2]) h
        all_goals simp

theorem mfact_mapDomain_add (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) :
    Formalism.A.mfact (α.mapDomain f + β.mapDomain g) = Formalism.A.mfact α * Formalism.A.mfact β := by
  classical
  unfold Formalism.A.mfact
  rw [Finsupp.prod_add_index_of_disjoint, Finsupp.prod_mapDomain_index_inj hf,
    Finsupp.prod_mapDomain_index_inj hg]
  rw [Finsupp.mapDomain_support_of_injective hf, Finsupp.mapDomain_support_of_injective hg,
    Finset.disjoint_left]
  intro t h1 h2
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h2
  exact hfg x y hy.symm

theorem fock_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (P P' : MvPolynomial σ₁ ℂ) (Q Q' : MvPolynomial σ₂ ℂ) :
    fock (rename f P * rename g Q) (rename f P' * rename g Q') = fock P P' * fock Q Q' := by
  induction P using MvPolynomial.induction_on' with
  | add P₁ P₂ h h' => simp only [map_add (f := _), add_mul, fock_add_left, h, h']
  | monomial α x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q₁ Q₂ h h' => simp only [map_add (f := _), mul_add, fock_add_left, h, h']
    | monomial β y =>
      rw [rename_monomial, rename_monomial, monomial_mul, fock_monomial_left, fock_monomial_left,
        fock_monomial_left, coeff_rename_mul hf hg hfg, mfact_mapDomain_add hf hg hfg, star_mul']
      push_cast
      ring

end Fock

end GlobalTheory.JointHarm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KaehlerRelationDerivationModIntegralStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_relation_derivationModIntegral : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω), (∀ x ∈ S, IsInt (p := p) x) → (∀ x, ι x ∈ S) →
  ∀ D : Ω → Ω, IsDer S D → ∀ a b c x y z : On p n,
  a • KaehlerDifferential.D (O0 p) (On p n) x = b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z →
  IsInt (p := p) (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  first | exact @GlobalTheory.KumDlog.kaehler_rel_isInt | exact GlobalTheory.KumDlog.kaehler_rel_isInt | (intros; apply GlobalTheory.KumDlog.kaehler_rel_isInt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainCharacterGaloisInvariantClass
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem kum_eq_of_apply {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {N : ℕ} (hN : 0 < N) {ζ θ : Ω}
    (hζ : IsPrimitiveRoot ζ N) (hθ : θ ≠ 0) (g : Ω ≃ₐ[K] Ω) (i : ZMod N) (hg : g θ = ζ ^ i.val * θ) :
    kum ζ θ g = i := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have hex : ∃ j : ZMod N, g θ = ζ ^ j.val * θ := ⟨i, hg⟩
  unfold kum
  rw [dite_eq_left hex]
  have h1 := hex.choose_spec
  have h2 : ζ ^ i.val = ζ ^ hex.choose.val := mul_right_cancel₀ hθ (hg.symm.trans h1)
  have h3 := (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)) h2
  exact (ZMod.val_injective N h3).symm

theorem eta_kummer_galoisInvariant : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) → ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 →
  α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b → ∀ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η →
  (∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g) →
  ∃ θ : Ω, θ ≠ 0 ∧ θ ^ N ∈ IntermediateField.adjoin K {α, β} ∧
    (∀ g ∈ (IntermediateField.adjoin K {α, β}).fixingSubgroup, η g = kum ζ θ g) ∧
    ∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix a b α β ha hb hα hβ η hη hcob
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  set E := IntermediateField.adjoin K ({α, β} : Set Ω) with hE
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hα; exact ha ((map_eq_zero _).mp hα.symm)
  have hβ0 : β ≠ 0 := by
    rintro rfl; rw [zero_pow hN.ne'] at hβ; exact hb ((map_eq_zero _).mp hβ.symm)
  obtain ⟨-, hαapp, hαmul, hαker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hfix hα0 ⟨a, hα.symm⟩
  obtain ⟨-, hβapp, hβmul, hβker⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hfix hβ0 ⟨b, hβ.symm⟩
  let x : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ α g)) (fun g h => by simp [hαmul, ofAdd_add])
  let y : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (kum ζ β g)) (fun g h => by simp [hβmul, ofAdd_add])
  obtain ⟨-, hconj, hhom⟩ := _root_.GlobalTheory.cochain_coboundary_prod_hom_identities (Ω ≃ₐ[K] Ω) N x y η (fun g h => hcob g h)

  have memH : ∀ g : Ω ≃ₐ[K] Ω, g ∈ E.fixingSubgroup ↔ g α = α ∧ g β = β := by
    intro g
    constructor
    · intro hg
      exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg α
          (IntermediateField.subset_adjoin K _ (by simp)),
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg β
          (IntermediateField.subset_adjoin K _ (by simp))⟩
    · rintro ⟨h1, h2⟩
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem w hw =>
        rcases hw with rfl | rfl
        · exact h1
        · exact h2
      | algebraMap r => exact g.commutes r
      | add u v _ _ hu hv => rw [map_add (f := _), hu, hv]
      | inv u _ hu => rw [map_inv₀, hu]
      | mul u v _ _ hu hv => rw [map_mul, hu, hv]
  have kα0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ α g = 0 := fun g hg => (hαker g).2 ((memH g).1 hg).1
  have kβ0 : ∀ g ∈ E.fixingSubgroup, kum (N := N) ζ β g = 0 := fun g hg => (hβker g).2 ((memH g).1 hg).2
  have hηhom : ∀ g ∈ E.fixingSubgroup, ∀ h ∈ E.fixingSubgroup, η (g * h) = η g + η h :=
    fun g hg h _ => hhom g h (kα0 g hg)
  obtain ⟨θ, hθ0, hθE, hθapp⟩ := _root_.GlobalTheory.kummer_generator_of_char K Ω N ζ hN hζ hfix E η hη hηhom
  have hkθ : ∀ g ∈ E.fixingSubgroup, η g = kum ζ θ g := fun g hg =>
    (kum_eq_of_apply hN hζ hθ0 g (η g) (hθapp g hg)).symm
  refine ⟨θ, hθ0, hθE, hkθ, fun s => ?_⟩

  have hconjH : ∀ m ∈ E.fixingSubgroup, s⁻¹ * m * s ∈ E.fixingSubgroup ∧ η (s⁻¹ * m * s) = η m := by
    intro m hm
    obtain ⟨hmα, hmβ⟩ := (memH m).1 hm
    have hsα : m (s α) = s α := by
      rw [hαapp s, map_mul, map_pow, hfix m, hmα]
    have hsβ : m (s β) = s β := by
      rw [hβapp s, map_mul, map_pow, hfix m, hmβ]
    refine ⟨(memH _).2 ⟨?_, ?_⟩, ?_⟩
    · show s⁻¹ (m (s α)) = α
      rw [hsα]; exact s.symm_apply_apply α
    · show s⁻¹ (m (s β)) = β
      rw [hsβ]; exact s.symm_apply_apply β
    · have := hconj s⁻¹ m
      rw [inv_inv] at this
      rw [this]
      simp [x, y, kα0 m hm, kβ0 m hm]
  set u := s θ / θ with hu
  have hsθ0 : s θ ≠ 0 := by simpa using hθ0
  have hu0 : u ≠ 0 := div_ne_zero hsθ0 hθ0
  refine ⟨u, ?_, hu0, ?_⟩
  · rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    intro m hm
    obtain ⟨hmem, hηeq⟩ := hconjH m hm
    have h1 : m θ = ζ ^ (η m).val * θ := hθapp m hm
    have h2 : (s⁻¹ * m * s) θ = ζ ^ (η m).val * θ := by rw [← hηeq]; exact hθapp _ hmem
    have h3 : m (s θ) = ζ ^ (η m).val * s θ := by
      have : s ((s⁻¹ * m * s) θ) = m (s θ) := by
        show s (s⁻¹ (m (s θ))) = m (s θ)
        exact s.apply_symm_apply _
      rw [← this, h2, map_mul, map_pow, hfix s]
    have hz : ζ ^ (η m).val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hN.ne')
    rw [hu, map_div₀, h1, h3, mul_div_mul_left _ _ hz]
  · rw [map_pow, hu, div_pow, mul_div_cancel₀ _ (pow_ne_zero N hθ0)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefr
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem mem_sqSet_iff (g : ℕ) [Fact g.Prime] (N : ℕ) (f : (ZMod g)[X]) :
    f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  unfold sqSet
  rw [Finset.mem_filter, Finset.mem_image, ← and_assoc (a := f.Monic)]
  refine and_congr_left fun _ => ⟨?_, ?_⟩
  · rintro ⟨c, -, rfl⟩
    have hd : (∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X]).degree < N := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hd, ?_⟩
    apply natDegree_eq_of_degree_eq_some
    rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
  · rintro ⟨hm, rfl⟩
    refine ⟨fun i => f.coeff i, Finset.mem_univ _, ?_⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i)]
    exact hm.as_sum.symm

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularLawOfSAndTStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modular_law_of_s_and_t : ∀ (P : (Fin 2 → ℚ) → Prop) (f : (Fin 2 → ℚ) → ℍ → ℂ), (∀ x γ, P x → P (act x γ)) → (∀ x τ, P x → f x (ModularGroup.S • τ) = f (act x ModularGroup.S) τ) → (∀ x τ, P x → f x (ModularGroup.T • τ) = f (act x ModularGroup.T) τ) → ∀ (γ : SL(2, ℤ)) x τ, P x → f x (γ • τ) = f (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.modular_law_of_generators | exact GlobalTheory.Sieg.modular_law_of_generators | (intros; apply GlobalTheory.Sieg.modular_law_of_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NebentypusSlashIntDiagTwoMatrixLevelRaiseStatement
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nebentypus_slash_intDiagTwoMatrix_levelRaise : ∀ (N l : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (B : ℍ → ℂ), 0 < l → ChiInv k N N χ B → ChiInv k N (N * l) χ (B ∣[k] toGL (dg l 1)) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | exact GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg | (intros; apply GlobalTheory.HeckeFamilyMatrices.chiInv_slash_dg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OldformLevelRaisingSlashSlashNebentypusStatement
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oldformLevelRaising_slash_slash_nebentypus : ∀ (N l : ℕ) (k : ℤ) (a b : ℤ), (l : ℤ) * b - N * a = 1 → ∀ (χ : DirichletCharacter ℂ N) (G : ℍ → ℂ), 0 < l → ChiInv k N (N * l) χ G → (G ∣[k] toGL (wOld N l a b)) ∣[k] toGL (wOld N l a b) = ((l : ℂ) ^ (k - 2) * χ (b : ZMod N)) • G := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash | exact GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash | (intros; apply GlobalTheory.HeckeFamilyMatrices.wOld_slash_slash <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShCocQuotCoord
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.KA

theorem shCoc_quot_coord : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω)
    (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ν : G ℚ Ω → (Qbar l)ˣ)
    (Y : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (m : ℕ),
    GlobalTheory.KA.ShCoc ρ (cycMod (F := ℚ) (Ω := Ω) l m)⁻¹ (Y m) →
    (∀ s ∈ Dec (F := ℚ) A, ρ s 1 0 = 0 ∧ ρ s 1 1 = (ν s : Qbar l)) →
    ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
      Y m (s * t) x 1 = Y m s x 1 + (ν s : Qbar l) * Y m t (x * (cycMod ℚ Ω l m s)⁻¹) 1 := by
  intro l _ Ω _ _ A ρ ν Y m hY hρ s hs t _ x
  simpa only [Pi.add_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two, (hρ s hs).1,
    (hρ s hs).2, zero_mul, zero_add, MonoidHom.inv_apply] using congrFun (hY s t x) 1

end GlobalTheory.KA
end

