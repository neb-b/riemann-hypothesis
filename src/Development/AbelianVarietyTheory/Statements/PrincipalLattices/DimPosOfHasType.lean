module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle0001
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.CM.NumInh

variable {K : Type} [Field K] [NumberField K]


variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem dim_pos_of_lieMult {S : Scheme.{0}} {O k : Type} [CommRing O] [Field k] {G : Over S} [GrpObj G] {act : OAct O G}
    {t : Sp k ⟶ S} {τ : O →+* k} (h : LieMult act t τ 1) {g : ℕ} (hg : SmoothOfRelativeDimension g G.hom) : 1 ≤ g := by
  by_contra h0
  obtain rfl : g = 0 := by omega
  have : Etale G.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hg
  obtain ⟨v, hv, hu⟩ := h
  have hs : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) hs
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  have key : ∀ c : k, (v 0).left = spMap (epsScale c) ≫ (v 0).left := fun c => by
    refine FormallyUnramified.hom_ext (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (isNilpotent_ker_specMap _ hnil) G.hom ?_ ?_
    · rw [← Category.assoc, spMap_comp_spMap]
      congr 2
      ext a <;> simp [epsScale]
    · rw [Category.assoc, Over.w (v 0)]
      show spMap _ ≫ t = spMap _ ≫ spMap _ ≫ t
      rw [← Category.assoc, spMap_comp_spMap]
      congr 2
      ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have e : ∀ c : Fin 1 → k, ∃ u : Fin 1 → (epsPt t ⟶ G),
      (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ v 0 = (List.ofFn u).prod := fun c =>
    ⟨v, fun i => by rw [Subsingleton.elim i 0]; exact key _, by simp⟩
  exact zero_ne_one (congrFun ((hu _ (hv 0)).unique (e 0) (e 1)) 0)

theorem exists_char (hs : Splits E K) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) : ∃ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ := by
  obtain ⟨τ⟩ : Nonempty (𝓞 E →+* 𝓞 K) := (Nat.card_pos_iff.1 (hs ▸ Module.finrank_pos)).1
  have e : τ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, hρ]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with e | e
  · exact ⟨τ, e⟩
  · exact ⟨τ.comp H.bar.toRingHom, by
      show τ (H.bar H.rt) = ρ
      rw [Test.bar_rt, map_neg, e, neg_neg]⟩

theorem dim_pos_of_hasType (hs : Splits E K) {ρ : 𝓞 K} (hρ : ρ ^ 2 = -(H.d : 𝓞 K)) (T : PAT H (Sp (𝓞 K))) {q : ℕ}
    (hT : HasType H T.t.act ρ 1 q) : 1 ≤ T.g := by
  obtain ⟨τ, hτ⟩ := exists_char hs hρ
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  exact dim_pos_of_lieMult ((hT ℂ (σ.comp (algebraMap (𝓞 K) K)) (σ.injective.comp RingOfIntegers.coe_injective)
    ((σ.comp (algebraMap (𝓞 K) K)).comp τ)).1 (by rw [RingHom.comp_apply, hτ])) T.dim


end GlobalTheory.CM.NumInh
end
