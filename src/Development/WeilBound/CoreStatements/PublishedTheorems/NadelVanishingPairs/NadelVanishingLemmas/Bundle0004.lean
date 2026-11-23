module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0258
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0003
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteTypeToNumberField
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AlternatingProductIntegral
section
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.alternating_product_integral : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (f : ι → V →+ V) (h : ι → ι → V →+ K) (A : Subring K) (L : Set V) (s : Finset ι), (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), (∀ k, v k ∈ L) → t ⊆ s → ∀ q, q + t.card = a + 1 → alt f h a v t ∈ forms (A : Set K) L q := by
  first | exact @_root_.GlobalTheory.DI.alt_mem_forms | exact _root_.GlobalTheory.DI.alt_mem_forms | (intros; apply _root_.GlobalTheory.DI.alt_mem_forms <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CupProductFiltrationBoundStatement
section
open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.cechZero_of_hypZero_of_cartier : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (N T : ℕ → Finset ι → AddSubgroup E) (Φ : E →+ (Finset ι → E)), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ x, Φ x ∅ = 0) → (∀ x, Dtot d (Φ x) = 0) → (∀ a u t x, u.Nonempty → t ⊆ u → x ∈ N a u → (∀ q, q + t.card = a + 1 → Φ x t ∈ T q u) ∧ (a + 1 < t.card → Φ x t = 0)) → (∀ s, ∀ j ∈ s, CartierAt d (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  first | exact @_root_.GlobalTheory.DI.cechZero_of_hypZero_of_closed_map | exact _root_.GlobalTheory.DI.cechZero_of_hypZero_of_closed_map | (intros; apply _root_.GlobalTheory.DI.cechZero_of_hypZero_of_closed_map <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FiniteTypeToModPSquared
section
open scoped TensorProduct Polynomial

namespace GlobalTheory

theorem exists_ringHom_zmod_prime_sq_isUnit_of_finiteType :
    ∀ (A : Type) [CommRing A] [IsDomain A] [CharZero A], Algebra.FiniteType ℤ A → ∀ a : A, a ≠ 0 → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ χ : A →+* ZMod (p ^ 2), IsUnit (χ a) := by
  intro A _ _ _ hA a ha n
  classical
  obtain ⟨K, _, _, χ₀, hχ⟩ := GlobalTheory.T.finite_type_to_number_field A hA a ha
  obtain ⟨s, hs⟩ := hA.out
  obtain ⟨p, hp, hn, ⟨ψ⟩⟩ := GlobalTheory.T.number_field_to_mod_p_squared K (insert (χ₀ a)⁻¹ (s.image χ₀)) n
  set R := Subring.closure ((insert (χ₀ a)⁻¹ (s.image χ₀) : Finset K) : Set K) with hR
  have hmem : ∀ x : A, χ₀ x ∈ R := by
    intro x
    have hx : x ∈ Algebra.adjoin ℤ (s : Set A) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      apply Subring.subset_closure
      simp only [Finset.coe_insert, Finset.coe_image]
      exact Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact R.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact R.mul_mem hx hy
  have hinv : (χ₀ a)⁻¹ ∈ R := by
    apply Subring.subset_closure
    simp
  refine ⟨p, hp, hn, ψ.comp (χ₀.codRestrict R hmem), ?_⟩
  rw [RingHom.comp_apply]
  apply IsUnit.map
  refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ ?_
  apply Subtype.ext
  simp [hχ]

end GlobalTheory
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ResidueFieldFormallySmooth
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.residue_field_formally_smooth :
    ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k)
      [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U),
      IsClosed ({x} : Set X) →
        (letI : Algebra k (X.presheaf.stalk x) :=
          ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
         Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  intro k _ _ X f _ U x hxU _
  let : Algebra k (X.presheaf.stalk x) :=
    ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  have hgerm : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU =
      (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have hstalk : algebraMap k (X.presheaf.stalk x) =
      (f.stalkMap x).hom.comp (StructureSheaf.toStalk k (f x)).hom := by
    change (X.presheaf.germ U x hxU).hom.comp (cstOn f U) = _
    rw [cstOn, ← CommRingCat.hom_comp, Category.assoc, hgerm, ← Category.assoc,
      Scheme.ΓSpecIso_inv]
    rfl
  have hbase (p : PrimeSpectrum k) : (StructureSheaf.toStalk k p).hom.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.mpr (Algebra.EssFiniteType.of_isLocalization _ p.asIdeal.primeCompl)
  have hresidue : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType :=
    RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
    apply RingHom.essFiniteType_algebraMap.mp
    change ((IsLocalRing.residue (X.presheaf.stalk x)).comp
      (algebraMap k (X.presheaf.stalk x))).EssFiniteType
    rw [hstalk]
    exact ((hbase (f x)).comp (LocallyOfFiniteType.stalkMap f x)).comp hresidue.essFiniteType
  exact Algebra.FormallySmooth.of_perfectField
end

