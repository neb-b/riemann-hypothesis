module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRedPts
section
namespace UpperTheory.Gal.crystallineComparison.Mod

theorem redPts_of : RedPts := by
  intro k H X _ _ _ _ _ C ρ h D
  obtain ⟨s, hs⟩ : ∃ s : H ⧸ C → H, Function.RightInverse s C.mkQ :=
    ⟨Function.surjInv (Submodule.mkQ_surjective C), Function.rightInverse_surjInv _⟩
  let g : H ⧸ C → X := fun q => ρ (s q)
  have hg : ∀ a, ρ a = g (C.mkQ a) := by
    intro a
    refine (h _ _).2 ?_
    have h1 : C.mkQ (s (C.mkQ a)) = C.mkQ a := hs _
    have h2 := (Submodule.Quotient.eq C).1 h1
    have h3 : a - s (C.mkQ a) = -(s (C.mkQ a) - a) := by abel
    rw [h3]
    exact C.neg_mem h2
  have hinj : Function.Injective g := by
    intro q1 q2 hq
    have hm := (h _ _).1 hq
    have e := (Submodule.Quotient.eq C).2 hm
    simpa [Submodule.mkQ_apply, hs q1, hs q2] using
      (show C.mkQ (s q1) = C.mkQ (s q2) from e)
  have himg : ∀ E : Submodule k H, ρ '' (E : Set H) = g '' ((Submodule.map C.mkQ E : Submodule k (H ⧸ C)) : Set (H ⧸ C)) := by
    intro E
    rw [Submodule.map_coe, Set.image_image]
    exact Set.image_congr (fun a _ => hg a)
  have hcard : ∀ V : Submodule k (H ⧸ C), Nat.card V = Nat.card k ^ Module.finrank k V := by
    intro V
    have : Finite (H ⧸ C) := Module.finite_of_finite k
    letI := Fintype.ofFinite k
    letI := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  refine ⟨?_, ?_⟩
  · rw [himg D, Nat.card_image_of_injective hinj]
    exact hcard _
  · intro D' hD
    rw [himg D, himg D', hD]

end UpperTheory.Gal.crystallineComparison.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRepHomog
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private lemma spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  dsimp only [spMap]
  rw [← Spec.map_comp]
  rfl

private lemma spMap_id' (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := by
  simp [spMap]

private lemma spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g := by
  have h' : CommRingCat.ofHom f = CommRingCat.ofHom g := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom h'

private lemma exists_algHom {κ B C : Type} [Field κ] [CommRing B] [CommRing C] [Algebra κ B] [Algebra κ C]
    (f : Sp C ⟶ Sp B) (hf : f ≫ spMap (algebraMap κ B) = spMap (algebraMap κ C)) :
    ∃ φ : B →ₐ[κ] C, spMap φ.toRingHom = f := by
  obtain ⟨φ, rfl⟩ : ∃ φ, f = Spec.map φ := ⟨Spec.preimage f, (Spec.map_preimage f).symm⟩
  have hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ C := by
    apply spMap_inj
    rw [← spMap_comp']
    exact hf
  exact ⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, rfl⟩

private noncomputable def ptOf {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ) :
    𝟙_ (Over (Sp κ)) ⟶ algPt κ B :=
  Over.homMk (spMap ε.toRingHom) (by
    show spMap ε.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _
    rw [spMap_comp', ← spMap_id']
    congr 1
    ext r
    simp)

private lemma ptOf_surj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (y : 𝟙_ (Over (Sp κ)) ⟶ algPt κ B) :
    ∃ ε : B →ₐ[κ] κ, ptOf ε = y := by
  obtain ⟨ε, hε⟩ := exists_algHom (C := κ) y.left (by
    rw [Algebra.algebraMap_self, spMap_id']
    exact Over.w y)
  refine ⟨ε, Over.OverMorphism.ext ?_⟩
  rw [← hε]
  rfl

private lemma ptOf_inj {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] {ε ε' : B →ₐ[κ] κ}
    (h : ptOf ε = ptOf ε') : ε = ε' := by
  have h1 : spMap ε.toRingHom = spMap ε'.toRingHom := congrArg CommaMorphism.left h
  have h2 := spMap_inj h1
  ext x
  exact RingHom.congr_fun h2 x

end UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.repHomog_of :
    RepHomog := by
  intro κ _ A _ P hSub B _ _ i hmono hiff
  haveI : Mono i := hmono
  refine ⟨?_, ?_⟩
  · refine Nat.card_congr (Equiv.ofBijective
      (fun ε => (⟨ptOf ε ≫ i, (hiff _ _).1 ⟨_, rfl⟩⟩ : { g // P (𝟙_ (Over (Sp κ))) g })) ⟨?_, ?_⟩)
    · intro a b h
      apply ptOf_inj
      exact (cancel_mono i).1 (congrArg Subtype.val h)
    · rintro ⟨g, hg⟩
      obtain ⟨y, hy⟩ := (hiff _ _).2 hg
      obtain ⟨ε, rfl⟩ := ptOf_surj y
      exact ⟨ε, Subtype.ext hy⟩
  · obtain ⟨y, hy⟩ := (hiff _ _).2 (hSub (𝟙_ (Over (Sp κ)))).1
    obtain ⟨ε₀, rfl⟩ := ptOf_surj y
    refine ⟨ε₀, ?_, fun ε => ?_⟩
    · show spMap ε₀.toRingHom ≫ i.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left
      rw [← hy]
      rfl
    · let c : algPt κ B ⟶ A := toUnit (algPt κ B) ≫ ptOf ε ≫ i
      have hc : c = toUnit (algPt κ B) ≫ ptOf ε ≫ i := rfl
      have hcP : P _ c := (hiff _ _).1 ⟨toUnit _ ≫ ptOf ε, by rw [hc, Category.assoc]⟩
      have hiP : P _ i := (hiff _ _).1 ⟨𝟙 _, Category.id_comp _⟩
      have hcinvP : P _ c⁻¹ := by
        have h' := (hSub (algPt κ B)).2 1 c (hSub _).1 hcP
        simpa using h'
      have hm : P _ (i * c) := by
        have h' := (hSub (algPt κ B)).2 i c⁻¹ hiP hcinvP
        simpa using h'
      have hm' : P _ (i * c⁻¹) := (hSub _).2 i c hiP hcP
      obtain ⟨s, hs⟩ := (hiff _ _).2 hm
      obtain ⟨s', hs'⟩ := (hiff _ _).2 hm'
      have hsc : ∀ t : algPt κ B ⟶ algPt κ B, t ≫ c = c := by
        intro t
        rw [hc, ← Category.assoc, comp_toUnit]
      have h1 : s ≫ s' = 𝟙 _ := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs', comp_mul, hs, GrpObj.comp_inv, hsc, Category.id_comp,
          mul_inv_cancel_right]
      have h2 : s' ≫ s = 𝟙 _ := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs, comp_mul, hs', hsc, Category.id_comp, inv_mul_cancel_right]
      have hpt : ptOf ε₀ ≫ s = ptOf ε := by
        apply (cancel_mono i).1
        rw [Category.assoc, hs, comp_mul, hy, _root_.one_mul, hc, ← Category.assoc,
          toUnit_unique (ptOf ε₀ ≫ toUnit _) (𝟙 _), Category.id_comp]
      obtain ⟨τ, hτ⟩ := exists_algHom (C := B) s.left (Over.w s)
      obtain ⟨τ', hτ'⟩ := exists_algHom (C := B) s'.left (Over.w s')
      have e1 : τ.comp τ' = AlgHom.id κ B := by
        have h' : spMap (τ.comp τ').toRingHom = spMap (RingHom.id B) := by
          rw [spMap_id']
          show spMap (τ.toRingHom.comp τ'.toRingHom) = _
          rw [← spMap_comp', hτ, hτ']
          exact congrArg CommaMorphism.left h1
        exact AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x
      have e2 : τ'.comp τ = AlgHom.id κ B := by
        have h' : spMap (τ'.comp τ).toRingHom = spMap (RingHom.id B) := by
          rw [spMap_id']
          show spMap (τ'.toRingHom.comp τ.toRingHom) = _
          rw [← spMap_comp', hτ, hτ']
          exact congrArg CommaMorphism.left h2
        exact AlgHom.ext fun x => RingHom.congr_fun (spMap_inj h') x
      refine ⟨AlgEquiv.ofAlgHom τ τ' e1 e2, ?_⟩
      rw [AlgEquiv.coe_algHom_ofAlgHom]
      apply ptOf_inj
      apply Over.OverMorphism.ext
      show spMap (ε₀.toRingHom.comp τ.toRingHom) = (ptOf ε).left
      rw [← hpt]
      show _ = spMap ε₀.toRingHom ≫ s.left
      rw [← hτ, spMap_comp']
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MResClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.resClosed_of :
    ResClosed := by
  intro V _ _ _ _
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hm hirr
  have hsurj : Function.Surjective (IsLocalRing.residue V) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue V) :=
    Polynomial.mem_lifts _ |>.2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨P, hP, hdeg, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hpos : 0 < P.natDegree := hdeg ▸ hirr.natDegree_pos
  have hd : (P.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    exact (Polynomial.natDegree_pos_iff_degree_pos.1 hpos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral V x := by
    refine ⟨P, hPm, ?_⟩
    simpa [Polynomial.IsRoot.def, Polynomial.eval_map] using hx
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hy : P.eval y = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
    exact hx
  refine ⟨IsLocalRing.residue V y, ?_⟩
  rw [← hP, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRingHomog
section
noncomputable section

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_algHom_ker (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B]
    [Module.Finite κ B] (p : PrimeSpectrum B) :
    ∃ ε : B →ₐ[κ] κ, RingHom.ker ε.toRingHom = p.asIdeal := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
  letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
  have hb : Function.Bijective (algebraMap κ (B ⧸ p.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := AlgEquiv.ofBijective (Algebra.ofId κ (B ⧸ p.asIdeal)) hb
  refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[κ] κ).comp (Ideal.Quotient.mkₐ κ p.asIdeal), ?_⟩
  ext x
  change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem ringHomog_of : RingHomog := by
  intro κ B _ _ _ _ _ ε₀ _ hτ
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI hfin : Module.Finite κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) :=
    Module.Finite.of_surjective
      (Algebra.algHom κ B (Localization.AtPrime (RingHom.ker ε₀.toRingHom))).toLinearMap
      (IsArtinianRing.localization_surjective (RingHom.ker ε₀.toRingHom).primeCompl
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)))
  have hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) =
        (Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) : ℕ∞) := by
    intro p
    obtain ⟨ε, hε⟩ := exists_algHom_ker κ B p
    obtain ⟨τ, hτε⟩ := hτ ε
    rw [GlobalTheory.FinSchemeRank.finrank_eq_length_of_isLocalRing κ]
    have hmap : p.asIdeal.primeCompl.map τ.toRingEquiv.toMonoidHom =
        (RingHom.ker ε₀.toRingHom).primeCompl := by
      ext y
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, ← hε, RingHom.mem_ker, ← hτε]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        refine ⟨τ.symm y, ?_, ?_⟩
        · simpa using hy
        · simp
    exact GlobalTheory.FinSchemeRank.length_self_eq_of_ringEquiv
      (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) τ.toRingEquiv hmap)
  have h := GlobalTheory.FinSchemeRank.finrank_eq_card_mul κ B _ hm
  rw [← GlobalTheory.FinSchemeRank.card_algHom_eq_card_primeSpectrum κ B] at h
  exact_mod_cast h

end UpperTheory.Gal.crystallineComparison.Mod
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSplitAlg
section
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.splitAlg_of :
    SplitAlg := by
  classical
  intro κ B Λ _ _ _ _ _ _ _ hcard ε g
  have hli := linearIndependent_toLinearMap κ B κ
  haveI : Finite (B →ₐ[κ] κ) := hli.finite
  letI := Fintype.ofFinite (B →ₐ[κ] κ)
  have hspan : Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank'
    rw [← Nat.card_eq_fintype_card, hcard]
    exact (Subspace.dual_finrank_eq).symm
  have h0 : ∀ x : B, (∀ φ : B →ₐ[κ] κ, φ x = 0) → x = 0 := by
    intro x hx
    rw [← Module.forall_dual_apply_eq_zero_iff κ x]
    intro f
    have hf : f ∈ Submodule.span κ (Set.range (AlgHom.toLinearMap : (B →ₐ[κ] κ) → B →ₗ[κ] κ)) := by
      rw [hspan]; exact Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φ, rfl⟩ := hy
      exact hx φ
    | zero => rfl
    | add y z _ _ hy hz => simp [hy, hz]
    | smul a y _ hy => simp [hy]
  have hunit : ∀ y : Λ, ε y ≠ 0 → IsUnit y := by
    intro y hy
    by_contra h
    have hym : y ∈ IsLocalRing.maximalIdeal Λ := h
    have hk : RingHom.ker ε.toRingHom ≤ IsLocalRing.maximalIdeal Λ :=
      IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
    have hd : y - algebraMap κ Λ (ε y) ∈ RingHom.ker ε.toRingHom := by
      rw [RingHom.mem_ker]
      simp
    have hm : algebraMap κ Λ (ε y) ∈ IsLocalRing.maximalIdeal Λ := by
      have := Ideal.sub_mem _ hym (hk hd)
      simpa using this
    exact hm ((isUnit_iff_ne_zero.mpr hy).map (algebraMap κ Λ))
  ext b
  simp only [AlgHom.comp_apply, Algebra.ofId_apply]
  set S : Finset κ := Finset.univ.image (fun φ : B →ₐ[κ] κ => φ b) with hS
  set c := ε (g b) with hc
  have hqb : Polynomial.aeval b (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    apply h0
    intro φ
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (i := φ b) (by simp [hS])
    simp
  have hq : Polynomial.aeval (g b) (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) = 0 := by
    rw [Polynomial.aeval_algHom_apply, hqb, map_zero]
  have hcS : c ∈ S := by
    have h1 := congrArg ε hq
    rw [← Polynomial.aeval_algHom_apply, map_zero, Polynomial.coe_aeval_eq_eval,
      Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
    obtain ⟨s, hs, hs0⟩ := h1
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hs0
    rw [hc, hs0]
    exact hs
  rw [← Finset.mul_prod_erase S _ hcS, map_mul] at hq
  have hr : IsUnit (Polynomial.aeval (g b) (∏ s ∈ S.erase c, (Polynomial.X - Polynomial.C s))) := by
    apply hunit
    rw [← Polynomial.aeval_algHom_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_prod,
      Finset.prod_ne_zero_iff]
    intro s hs
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  have h2 := hr.mul_left_eq_zero.mp hq
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h2
  exact sub_eq_zero.mp h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MValPtsX
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.valPtsX_of :
    ValPtsX := by
  intro S K h hp V _ _ _ z
  have : IsProper h := hp
  constructor
  · intro g g' hg hg' e
    have c : CommSq (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ g)
        (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z :=
      ⟨by rw [Category.assoc, hg]⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, _, z, c⟩
    have hs : Subsingleton Q.commSq.LiftStruct := IsSeparated.valuativeCriterion h Q
    let l₁ : Q.commSq.LiftStruct := ⟨g, rfl, hg⟩
    let l₂ : Q.commSq.LiftStruct := ⟨g', e.symm, hg'⟩
    exact congrArg CommSq.LiftStruct.l (Subsingleton.elim l₁ l₂)
  · intro g hg
    have c : CommSq g (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) h z := ⟨hg⟩
    let Q : ValuativeCommSq h := ⟨V, FractionRing V, g, z, c⟩
    have hu : (ValuativeCriterion.Existence ⊓ @QuasiCompact) h := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    obtain ⟨l, h₁, h₂⟩ := (hu.1 Q).exists_lift
    exact ⟨l, h₂, h₁⟩
end

