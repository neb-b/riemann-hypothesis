module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2121
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1817
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2152
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2472

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirationalModelTotallyOrderedFamily
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_model_list (k : Type) [CommRing k] (D : ℕ) (L : ℕ) :
    ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), IsArithVar p D →
    ∀ (g : List X.functionField), g.length = L → (∀ h ∈ g, h ≠ 0) →
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField),
      IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ ∀ h ∈ g, ∀ y : Y, RegAt y (φ h) ∨ RegAt y (φ h)⁻¹ := by
  induction L with
  | zero =>
    intro X _ p hp g hg _
    obtain rfl := List.length_eq_zero_iff.1 hg
    refine ⟨X, inferInstance, 𝟙 X, RingHom.id _, by simpa using hp, (_root_.GlobalTheory.HSNef.isModel_id_and_comp X X X (𝟙 X) (𝟙 X)
      (RingHom.id _) (RingHom.id _)).1, by simp⟩
  | succ n ih =>
    intro X _ p hp g hg hne
    obtain ⟨a, g', rfl⟩ : ∃ a g', g = a :: g' := by
      cases g with
      | nil => simp at hg
      | cons a g' => exact ⟨a, g', rfl⟩
    obtain ⟨Y₁, hY₁, π₁, φ₁, hA₁, hM₁, hR₁⟩ :=
      ih X p hp g' (by simpa using hg) (fun h hh => hne h (List.mem_cons_of_mem _ hh))
    have ha : φ₁ a ≠ 0 := (map_ne_zero φ₁).2 (hne a List.mem_cons_self)
    obtain ⟨Y₂, hY₂, π₂, φ₂, hA₂, hM₂, hR₂⟩ := _root_.GlobalTheory.RegOrInvModel.exists_model_regAt_or_regAt_inv k Y₁ (π₁ ≫ p) D hA₁ (φ₁ a) ha
    refine ⟨Y₂, hY₂, π₂ ≫ π₁, φ₂.comp φ₁, by simpa [Category.assoc] using hA₂,
      (_root_.GlobalTheory.HSNef.isModel_id_and_comp X Y₁ Y₂ π₁ π₂ φ₁ φ₂).2 hM₁ hM₂, ?_⟩
    have hreg := (_root_.GlobalTheory.HSNef.model_regAt_unitAt_values k Y₁ Y₂ (π₁ ≫ p) (π₂ ≫ π₁ ≫ p) π₂ rfl φ₂ hM₂).1
    intro h hh y
    rcases List.mem_cons.1 hh with rfl | hh
    · simpa using hR₂ y
    · rcases hR₁ h hh (π₂ y) with h1 | h1
      · exact Or.inl (by simpa using hreg y _ h1)
      · exact Or.inr (by simpa [map_inv₀] using hreg y _ h1)

end GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_model_total : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (J : Type) [Finite J] (f : J → X.functionField), (∀ j, f j ≠ 0) → ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (π : Y ⟶ X) (φ : X.functionField →+* Y.functionField), IsArithVar (π ≫ p) D ∧ IsModel π φ ∧ Total (fun j => φ (f j)) := by
  intro k _ X _ p D hp J _ f hf
  have := Fintype.ofFinite J
  let g : List X.functionField := (Finset.univ : Finset (J × J)).toList.map (fun q => f q.1 / f q.2)
  have hg : ∀ j l, f j / f l ∈ g := fun j l => by
    simp only [g, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    exact ⟨(j, l), rfl⟩
  obtain ⟨Y, hY, π, φ, hA, hM, hR⟩ := exists_model_list k D g.length X p hp g rfl (by
    intro h hh
    simp only [g, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hh
    obtain ⟨q, rfl⟩ := hh
    exact div_ne_zero (hf q.1) (hf q.2))
  refine ⟨Y, hY, π, φ, hA, hM, fun j => (map_ne_zero φ).2 (hf j), fun y j l => ?_⟩
  rcases hR _ (hg j l) y with h | h
  · exact Or.inl (by simpa [map_div₀] using h)
  · exact Or.inr (by simpa [map_div₀, inv_div] using h)

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCentredPureFiniteExtensionDeeperModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep

theorem exists_centred_ext_tower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V), IsCN V → IsLocalHom ev → RegAt X₁ z₁ ev → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), IsCN V' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ (∀ I : Ideal V, (I.map io).comap io = I) ∧ 𝔗.Ext ev io ev₂ := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act _ 𝔗 z₂ hz V _ _ _ ev hV hev _
  subst hz

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ := (X₁.M.stalkHom (𝔗.p z₂)).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ (𝔗.p z₂)
  letI : Algebra (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := (𝔗.X₂.M.stalkHom z₂).toAlgebra
  obtain ⟨hdom₂, hfr₂, hic₂, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i 𝔗.X₂ z₂
  haveI := 𝔗.fd
  haveI := 𝔗.gal
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.Poinc.integralClosure_galois_finite_invariants (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom (𝔗.p z₂))).toAlgebra
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI := hdom; haveI := hfr; haveI := hic; haveI := hdom₂; haveI := hfr₂; haveI := hic₂
  haveI : Algebra.IsInvariant (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) :=
    ⟨fun b hb => hfix b hb⟩
  haveI : Module.Finite (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfin
  haveI : Finite (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) := hfinA
  have hcard : Nat.card (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) = Module.finrank X₁.Ω₁ 𝔗.X₂.Ω₁ := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (galRestrict (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) X₁.Ω₁ 𝔗.X₂.Ω₁ (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)).toEquiv).symm

  have hn1 : IsUnit ((X₁.ρ.n : ℕ) : X₁.o₁) := by
    have hu := X₁.S.unit
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [X₁.ρ.N_eq]
      exact Dvd.dvd.mul_left (dvd_pow (dvd_pow_self _ (by have := X₁.ρ.two_le; omega)) two_ne_zero) _
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul] at hu
    exact isUnit_of_mul_isUnit_left hu
  have hnA : IsUnit ((X₁.ρ.n : ℕ) : (X₁.M.Z.presheaf.stalk (𝔗.p z₂))) := by
    obtain ⟨u, hu⟩ := hn1
    have hm : algebraMap X₁.o₁ X₁.Ω₁ (↑u⁻¹) ∈ X₁.M.O (𝔗.p z₂) := Subalgebra.algebraMap_mem _ _
    refine IsUnit.of_mul_eq_one ((X₁.M.stalkEquiv _).symm ⟨_, hm⟩) (X₁.M.stalkHom_injective _ ?_)
    rw [map_mul, map_one, map_natCast, ← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    change ((X₁.ρ.n : ℕ) : X₁.Ω₁) * algebraMap X₁.o₁ X₁.Ω₁ (↑u⁻¹) = 1
    rw [← map_natCast (algebraMap X₁.o₁ X₁.Ω₁), ← hu, ← map_mul, Units.mul_inv, map_one]
  have hnV : IsUnit ((X₁.ρ.n : ℕ) : V) := by simpa using hnA.map ev
  have hdegV : IsUnit ((Module.finrank X₁.Ω₁ 𝔗.X₂.Ω₁ : ℕ) : V) := by
    obtain ⟨e, he⟩ := 𝔗.deg
    rw [he, Nat.cast_pow]
    exact hnV.pow e

  haveI : CharZero V := hV.2.2.2
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨K', _, _, β, hK'fd, hK'dvd, hβ⟩ := _root_.GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) hinj (FractionRing V)
    ((algebraMap V (FractionRing V)).comp ev)
  haveI := hK'fd
  have hK'u : IsUnit ((Module.finrank (FractionRing V) K' : ℕ) : V) := by
    rw [hcard] at hK'dvd
    obtain ⟨c, hc⟩ := hK'dvd
    rw [hc, Nat.cast_mul] at hdegV
    exact isUnit_of_mul_isUnit_left hdegV
  obtain ⟨V', _, _, _, io, j, hV', hioi, hiof, hiol, hcon, hjinj, hj, hjr⟩ := _root_.GlobalTheory.LocExt.exists_isCN_integralClosure_of_isUnit_finrank V hV K' hK'u
  have hβmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, β b ∈ j.range := by
    intro b
    obtain ⟨P, hPm, hP⟩ := integralClosure.isIntegral b
    obtain ⟨y, hy⟩ := hjr (β b) ⟨P.map ev, hPm.map ev, by
      rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hβ, ← Polynomial.hom_eval₂, hP, map_zero]⟩
    exact ⟨y, hy⟩
  let jr : V' ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hjinj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let β' : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* V' := jr.symm.toRingHom.comp (β.codRestrict j.range hβmem)
  have hβ' : ∀ b, j (β' b) = β b := fun b => congrArg Subtype.val (jr.apply_symm_apply ⟨β b, hβmem b⟩)

  letI : Algebra (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) := (𝔗.p.stalkMap z₂).hom.toAlgebra
  have hg1 : ∀ x : (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), 𝔗.X₂.M.stalkHom z₂ ((𝔗.p.stalkMap z₂).hom x) = algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁ (X₁.M.stalkHom (𝔗.p z₂) x) :=
    fun x => (_root_.GlobalTheory.ZH.RatModel.stalkHom_stalkMap_algebraMap X₁.o₁ X₁.Ω₁ 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ X₁.M 𝔗.X₂.M 𝔗.p 𝔗.p_pt z₂ x)
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (𝔗.X₂.M.Z.presheaf.stalk z₂) 𝔗.X₂.Ω₁ := IsScalarTower.of_algebraMap_eq fun x => (hg1 x).symm
  have hinj₂ := 𝔗.X₂.M.stalkHom_injective z₂
  have hBmem : ∀ b : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, (b : 𝔗.X₂.Ω₁) ∈ (𝔗.X₂.M.stalkHom z₂).range := fun b => by
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := (𝔗.X₂.M.Z.presheaf.stalk z₂)) (K := 𝔗.X₂.Ω₁)).1
      (IsIntegral.tower_top (A := (𝔗.X₂.M.Z.presheaf.stalk z₂)) b.2)
    exact ⟨y, hy⟩
  let e₂ : (𝔗.X₂.M.Z.presheaf.stalk z₂) ≃+* (𝔗.X₂.M.stalkHom z₂).range := RingEquiv.ofBijective (𝔗.X₂.M.stalkHom z₂).rangeRestrict
    ⟨fun a b h => hinj₂ (congrArg Subtype.val h), (𝔗.X₂.M.stalkHom z₂).rangeRestrict_surjective⟩
  let f : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →+* (𝔗.X₂.M.Z.presheaf.stalk z₂) :=
    e₂.symm.toRingHom.comp (((integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁).val : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ →ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] 𝔗.X₂.Ω₁).toRingHom.codRestrict _ hBmem)
  have hf : ∀ b, 𝔗.X₂.M.stalkHom z₂ (f b) = b := fun b => congrArg Subtype.val (e₂.apply_symm_apply ⟨_, hBmem b⟩)
  have hfB : ∀ (t : (𝔗.X₂.M.Z.presheaf.stalk z₂)) (h : 𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁), f ⟨_, h⟩ = t :=
    fun t h => hinj₂ (hf _)
  have hloc : IsLocalHom (f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁))) := by
    have h : f.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = (𝔗.p.stalkMap z₂).hom :=
      RingHom.ext fun a => hinj₂ (by rw [RingHom.comp_apply, hf, hg1]; rfl)
    rw [h]; infer_instance
  have hint : ∀ t : (𝔗.X₂.M.Z.presheaf.stalk z₂), (∃ P : Polynomial (X₁.M.Z.presheaf.stalk (𝔗.p z₂)), P.Monic ∧ P.eval₂ (𝔗.p.stalkMap z₂).hom t = 0) →
      𝔗.X₂.M.stalkHom z₂ t ∈ integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ := by
    rintro t ⟨P, hPm, hP⟩
    refine ⟨P, hPm, ?_⟩
    have h : algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ = (𝔗.X₂.M.stalkHom z₂).comp (𝔗.p.stalkMap z₂).hom := RingHom.ext fun x => (hg1 x).symm
    rw [h, ← Polynomial.hom_eval₂, hP, map_zero]
  have hsurj : ∀ y : (𝔗.X₂.M.Z.presheaf.stalk z₂), ∃ b s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ y * f s = f b := by
    intro y
    obtain ⟨b, s, hs, hys, hb, hs'⟩ := _root_.GlobalTheory.Poinc.finite_stalk_quot_integral _ _ 𝔗.p 𝔗.p_fin z₂ y
    refine ⟨⟨_, hint b hb⟩, ⟨_, hint s hs'⟩, ?_, ?_⟩
    · rw [hfB]; exact hs
    · rw [hfB, hfB]; exact hys
  have hker : ∀ b, f b = 0 → ∃ s : integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁, IsUnit (f s) ∧ s * b = 0 := fun b hb =>
    ⟨1, by rw [map_one]; exact isUnit_one, by
      rw [_root_.one_mul]; exact Subtype.ext (by rw [← hf b, hb, map_zero]; rfl)⟩
  haveI := hiol; haveI := hev
  have hβ'A : β'.comp (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁)) = io.comp ev := RingHom.ext fun a =>
    hjinj ((hβ' _).trans ((RingHom.congr_fun hβ a).trans (RingHom.congr_fun hj (ev a)).symm))
  obtain ⟨ev₂, hev₂, hcomp⟩ := _root_.GlobalTheory.twisted_lift_to_localisation (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) (𝔗.X₂.M.Z.presheaf.stalk z₂)
    (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁ ≃ₐ[(X₁.M.Z.presheaf.stalk (𝔗.p z₂))] integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) f hloc hsurj hker V' (io.comp ev) β' inferInstance hβ'A
  refine ⟨V', inferInstance, inferInstance, inferInstance, io, ev₂, hV', hioi, hiof, hiol, hcon, hev₂, fun x x₂ hx => ?_⟩
  have h : x₂ = f (algebraMap (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) (integralClosure (X₁.M.Z.presheaf.stalk (𝔗.p z₂)) 𝔗.X₂.Ω₁) x) := hinj₂ (by rw [hf]; exact hx)
  rw [h]
  exact RingHom.congr_fun hcomp x

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedAlgebraicFormFderivUniformised
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem clm_eq_sum_single_smul_proj {g : ℕ} (f : (Fin g → ℂ) →L[ℂ] ℂ) :
    f = ∑ a, f (Pi.single a 1) • (ContinuousLinearMap.proj a : (Fin g → ℂ) →L[ℂ] ℂ) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  conv_lhs => rw [pi_eq_sum_univ' v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, mul_comm]

theorem fderiv_partial_symm {g : ℕ} {s : Set (Fin g → ℂ)} (hs : IsOpen s) {h : (Fin g → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h s) {k : Fin g → (Fin g → ℂ) → ℂ} (hk : ∀ a, DifferentiableOn ℂ (k a) s)
    (e : ∀ a, ∀ z ∈ s, fderiv ℂ h z (Pi.single a 1) = k a z) (a b : Fin g) {z : Fin g → ℂ} (hz : z ∈ s) :
    fderiv ℂ (k b) z (Pi.single a 1) = fderiv ℂ (k a) z (Pi.single b 1) := by
  have hn : s ∈ 𝓝 z := hs.mem_nhds hz
  have h1 : ∀ᶠ y in 𝓝 z, HasFDerivAt h (fderiv ℂ h y) y := by
    filter_upwards [hn] with y hy using (hh.differentiableAt (hs.mem_nhds hy)).hasFDerivAt
  have h2 : fderiv ℂ h =ᶠ[𝓝 z]
      fun y ↦ ∑ c, k c y • (ContinuousLinearMap.proj c : (Fin g → ℂ) →L[ℂ] ℂ) := by
    filter_upwards [hn] with y hy
    rw [clm_eq_sum_single_smul_proj (fderiv ℂ h y)]
    exact Finset.sum_congr rfl fun c _ ↦ by rw [e c y hy]
  have h3 : DifferentiableAt ℂ (fderiv ℂ h) z := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ h2
    exact DifferentiableAt.fun_sum fun c _ ↦ ((hk c).differentiableAt hn).smul_const _
  have h4 : ∀ c v, fderiv ℂ (k c) z v = fderiv ℂ (fderiv ℂ h) z v (Pi.single c 1) := by
    intro c v
    have h5 : k c =ᶠ[𝓝 z] fun y ↦ fderiv ℂ h y (Pi.single c 1) := by
      filter_upwards [hn] with y hy using (e c y hy).symm
    rw [h5.fderiv_eq, fderiv_clm_apply h3 (differentiableAt_const _)]
    simp
  rw [h4, h4]
  exact second_derivative_symmetric_of_eventually h1 h3.hasFDerivAt _ _

theorem exists_closed_form_fderiv_eq (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g)
    (hA : IsAbelianScheme A) (U : A.left.affineOpens) (h : (Fin g → ℂ) → ℂ) (hh : DifferentiableOn ℂ h (pre u.ex U.1))
    (hr : ∀ a, IsReg u.ex U.1 fun z => fderiv ℂ h z (Pi.single a 1)) :
    ∃ ξ : Ω[Sec (str A) U.1⁄ℂ], dOne ℂ _ ξ = 0 ∧ ∀ z ∈ pre u.ex U.1, fderiv ℂ h z = evForm u.ex U.1 z ξ := by
  obtain ⟨hop, hdiff, -, -, -, -, -, -, -, halg, -, -⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  obtain ⟨d, ω, hcomm, hd, hdual, hspan, hev⟩ := _root_.GlobalTheory.CechPer.kaehler_frame A g L u hA U
  choose k₀ hk₀ using hr
  let k : Fin g → Sec (str A) U.1 := k₀
  have hk : ∀ a, ∀ z ∈ pre u.ex U.1, fderiv ℂ h z (Pi.single a 1) = val u.ex U.1 (k a) z := hk₀
  refine ⟨∑ a, k a • ω a, _root_.GlobalTheory.CechPer.dOne_eq_zero_of_frame_of_symm _ g d ω hcomm hdual hspan k fun a b ↦ ?_, fun z hz ↦ ?_⟩
  · have h0 : d a (k b) - d b (k a) = 0 := by
      refine _root_.GlobalTheory.ValInj.eq_zero_of_val_eq_zero A g L u hA U.1 _ fun z hz ↦ ?_
      obtain ⟨e, he⟩ := halg U.1 z hz
      have h1 := he (d a (k b) - d b (k a))
      rw [map_sub, ← he (d a (k b)), ← he (d b (k a)), hd a _ z hz, hd b _ z hz,
        fderiv_partial_symm (hop U.1) hh (fun c ↦ hdiff U.1 (k c)) hk a b hz, sub_self] at h1
      exact h1
    exact sub_eq_zero.mp h0
  · rw [clm_eq_sum_single_smul_proj (fderiv ℂ h z), clm_eq_sum_single_smul_proj (evForm u.ex U.1 z _)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have h1 : (d a).liftKaehlerDifferential (∑ c, k c • ω c) = k a := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, hdual]
    rw [hev a _ z hz, h1, hk a z hz]

end GlobalTheory.CechPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonGenericFibreDiagonalEndEighthPower
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GenCmp

theorem diagEnd_unique_comm {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (u' : T' ⟶ F.X) (h : T ⟶ T') (hu : h ≫ u' = u)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A))
    (hS : IsDiagEnd F W P u ε) (hS' : IsDiagEnd F W P' u' ε') :
    ∃ α : P.A.left ⟶ P'.A.left, IsGrpPullback P.A P'.A h α ∧ LBIso P.L (P'.L.pull α) ∧
      ∀ E, (ε E).left ≫ α = α ≫ (ε' E).left := by
  subst hu
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩ := hS
  obtain ⟨c', hc', pr', hpr', huniv', hbun', hdiag'⟩ := hS'
  obtain ⟨κ, κ₂, hκ, hsq, hw, -⟩ := GlobalTheory.SiegelPullComp.pb_cancel hc' hc
  have hκw : κ ≫ c'.A.hom = c.A.hom ≫ h := hκ.1.w
  obtain ⟨x₀, hx₀, -⟩ := huniv' (Over.mk (P.A.hom ≫ h)) (fun a => pushPt hκw (pr a))
  let α : P.A.left ⟶ P'.A.left := x₀.left
  have hα : ∀ a, α ≫ (pr' a).left = (pr a).left ≫ κ := fun a => congrArg (fun q => q.left) (hx₀ a)
  have hαw : α ≫ P'.A.hom = P.A.hom ≫ h := Over.w x₀
  have ext' : ∀ {T₁ : Over T'} (v w : T₁ ⟶ P'.A), (∀ a, (v ≫ pr' a).left = (w ≫ pr' a).left) → v = w := by
    intro T₁ v w e
    obtain ⟨_, -, hu⟩ := huniv' T₁ (fun a => w ≫ pr' a)
    exact (hu v fun a => Over.OverMorphism.ext (e a)).trans (hu w fun _ => rfl).symm
  have key : ∀ {Z : Scheme.{0}} (z₁ : Z ⟶ P'.A.left) (z₂ : Z ⟶ T), z₁ ≫ P'.A.hom = z₂ ≫ h →
      ∃! m : Z ⟶ P.A.left, m ≫ α = z₁ ∧ m ≫ P.A.hom = z₂ := by
    intro Z z₁ z₂ e
    have ea : ∀ a, (z₁ ≫ (pr' a).left) ≫ c'.A.hom = z₂ ≫ h := fun a => by
      rw [Category.assoc, Over.w (pr' a), e]
    let ya : Fin 8 → (Over.mk z₂ ⟶ c.A) := fun a =>
      Over.homMk (hκ.1.lift (z₁ ≫ (pr' a).left) z₂ (ea a)) (hκ.1.lift_snd _ _ _)
    have hya : ∀ a, (ya a).left ≫ κ = z₁ ≫ (pr' a).left := fun a => hκ.1.lift_fst _ _ _
    obtain ⟨x, hx, hxu⟩ := huniv (Over.mk z₂) ya
    have hxw : x.left ≫ P.A.hom = z₂ := Over.w x
    refine ⟨x.left, ⟨?_, hxw⟩, fun m ⟨hm₁, hm₂⟩ => ?_⟩
    · have w₁ : (x.left ≫ α) ≫ P'.A.hom = z₂ ≫ h := by rw [Category.assoc, hαw, ← Category.assoc, hxw]
      have := ext' (T₁ := Over.mk (z₂ ≫ h)) (Over.homMk (x.left ≫ α) w₁) (Over.homMk z₁ e) fun a => by
        show (x.left ≫ α) ≫ (pr' a).left = z₁ ≫ (pr' a).left
        rw [Category.assoc, hα, ← Category.assoc, ← hya a, ← hx a]; rfl
      exact congrArg (fun q => q.left) this
    · have := hxu (Over.homMk m hm₂) fun a => Over.OverMorphism.ext (hκ.1.hom_ext (by
        show (m ≫ (pr a).left) ≫ κ = (ya a).left ≫ κ
        rw [Category.assoc, ← hα, ← Category.assoc, hm₁, hya]) (by
        show (m ≫ (pr a).left) ≫ c.A.hom = (ya a).left ≫ c.A.hom
        rw [Category.assoc, Over.w (pr a), hm₂]; exact (Over.w (ya a)).symm))
      exact congrArg (fun q => q.left) this
  have hpb : IsPullback α P.A.hom P'.A.hom h := by
    refine ⟨⟨hαw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => (key s.fst s.snd s.condition).exists.choose)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.1)
      (fun s => (key s.fst s.snd s.condition).exists.choose_spec.2)
      (fun s m h₁ h₂ => (key s.fst s.snd s.condition).unique ⟨h₁, h₂⟩
        (key s.fst s.snd s.condition).exists.choose_spec)⟩⟩
  have hmul : ∀ (T₀ : Over T) (x y : T₀ ⟶ P.A) (x₁ y₁ : Over.mk (T₀.hom ≫ h) ⟶ P'.A),
      x₁.left = x.left ≫ α → y₁.left = y.left ≫ α → (x₁ * y₁).left = (x * y).left ≫ α := by
    intro T₀ x y x₁ y₁ hx hy
    have wz : ((x * y).left ≫ α) ≫ P'.A.hom = (Over.mk (T₀.hom ≫ h)).hom := by
      rw [Category.assoc, hαw, ← Category.assoc, Over.w (x * y)]; rfl
    have := ext' (x₁ * y₁) (Over.homMk ((x * y).left ≫ α) wz) fun a => by
      haveI := hpr a
      haveI := hpr' a
      rw [MonObj.mul_comp]
      have e := hκ.2 T₀ (x ≫ pr a) (y ≫ pr a) (x₁ ≫ pr' a) (y₁ ≫ pr' a)
        (by show x₁.left ≫ (pr' a).left = x.left ≫ (pr a).left ≫ κ; rw [hx, Category.assoc, hα])
        (by show y₁.left ≫ (pr' a).left = y.left ≫ (pr a).left ≫ κ; rw [hy, Category.assoc, hα])
      rw [e, ← MonObj.mul_comp]
      show ((x * y).left ≫ (pr a).left) ≫ κ = ((x * y).left ≫ α) ≫ (pr' a).left
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (hα a).symm).trans (Category.assoc _ _ _).symm)
    exact congrArg (fun q => q.left) this
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr ab.1) (pr ab.2)).left ≫ κ₂ = α ≫ (lift (pr' ab.1) (pr' ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (α ≫ P'.A.hom)) (T' := P.A)
      (𝟙 P.A.left) (pr ab.1) (pr ab.2) (Z := P'.A) α (pr' ab.1) (pr' ab.2)
      ((Category.id_comp _).trans (hα ab.1).symm) ((Category.id_comp _).trans (hα ab.2).symm))
  let wt : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
  let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
  let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
  have l0 : (LB.LinComb c'.P q' wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' wt
  have l1 : (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB _ wt
  have l2 : (LB.LinComb (c'.P.pull κ₂) q wt).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c'.P.pull κ₂) (pull_isLB c'.isLB κ₂) q wt
  have l3 : (LB.LinComb c.P q wt).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q wt
  have refl1 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) :=
    ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
  have i2 : LBIso (P'.L.pull α) ((LB.LinComb c'.P q' wt).pull α) := GlobalTheory.SiegelPullComp.iso_pull α hbun'
  have i3 : LBIso ((LB.LinComb c'.P q' wt).pull α) (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) :=
    LBIso.chartPull (chartPullOut c'.P q' wt α _ fun _ => rfl) (chartPullId _) refl1
  have i4 : LBIso (LB.LinComb c'.P (fun ab => α ≫ q' ab) wt) (LB.LinComb (c'.P.pull κ₂) q wt) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb c'.P κ₂ q (fun ab => α ≫ q' ab) wt (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
  have i5 : LBIso (LB.LinComb (c'.P.pull κ₂) q wt) (LB.LinComb c.P q wt) :=
    GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q wt
  have h1 := pull_isLB P'.isLB α
  have h2 := pull_isLB l0 α
  have chain : LBIso (P'.L.pull α) (LB.LinComb c.P q wt) :=
    LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5))
  refine ⟨α, ⟨hpb, hmul⟩, LBIso.trans P.isLB l3 h1 hbun chain.symm, fun E => ?_⟩

  have w1 : ((ε E).left ≫ α) ≫ P'.A.hom = P.A.hom ≫ h := by
    rw [Category.assoc, hαw, ← Category.assoc, Over.w (ε E)]
  let v : Over.mk (P.A.hom ≫ h) ⟶ P'.A := Over.homMk ((ε E).left ≫ α) w1
  have hvl : v.left = (ε E).left ≫ α := rfl
  have hpl : ∀ x : P.A ⟶ c.A, (pushPt hκw x).left = x.left ≫ κ := fun _ => rfl
  have e : v = x₀ ≫ ε' E := ext' v (x₀ ≫ ε' E) fun a => by
    have l : v ≫ pr' a = pushPt hκw (ε E ≫ pr a) := by
      apply Over.OverMorphism.ext
      rw [Over.comp_left, hvl, hpl, Over.comp_left, Category.assoc, hα]
      exact (Category.assoc _ _ _).symm
    rw [l, Category.assoc x₀, hdiag E a, hdiag' E a]
    have r1 : pushPt hκw (((List.finRange 8).map fun b => pr b ^ E a b).prod) =
        pushHom hκ P.A (((List.finRange 8).map fun b => pr b ^ E a b).prod) := rfl
    have r2 : x₀ ≫ ((List.finRange 8).map fun b => pr' b ^ E a b).prod =
        diagPrecomp (M := c'.A) x₀ (((List.finRange 8).map fun b => pr' b ^ E a b).prod) := rfl
    rw [r1, r2, map_list_prod, map_list_prod, List.map_map, List.map_map]
    congr 2
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, map_zpow]
    congr 1
    exact (hx₀ b).symm
  exact congrArg (fun q => q.left) e

end GlobalTheory.Poinc.GenCmp

namespace GlobalTheory.Poinc

theorem exists_common_fibre_diagEnd : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (R R' K : Type) [CommRing R] [CommRing R'] [Field K] (f : R →+* K) (f' : R' →+* K) (P : PolAV (Sp R)) (u : Sp R ⟶ F.X) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)) (P' : PolAV (Sp R')) (u' : Sp R' ⟶ F.X), IsDiagEnd F W P u ε → SharpOver F W P' u' → spMap f ≫ u = spMap f' ≫ u' → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A), IsDiagEnd F W P' u' ε' ∧ ∃ (P₀ : PolAV (Sp K)) (a : P₀.A.left ⟶ P.A.left) (a' : P₀.A.left ⟶ P'.A.left) (ε₀ : Matrix (Fin 8) (Fin 8) ℤ → (P₀.A ⟶ P₀.A)), IsGrpPullback P₀.A P.A (spMap f) a ∧ IsGrpPullback P₀.A P'.A (spMap f') a' ∧ LBIso P₀.L (P.L.pull a) ∧ LBIso P₀.L (P'.L.pull a') ∧ ∀ E, (ε₀ E).left ≫ a = a ≫ (ε E).left ∧ (ε₀ E).left ≫ a' = a' ≫ (ε' E).left := by
  intro g n F W R R' K _ _ _ f f' P u ε P' u' hD hS' he
  obtain ⟨P₀, a, -, ha, hLa⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f) P
  obtain ⟨ε₀, hD₀, hc₀⟩ := isDiagEnd_pullback F W P P₀ u (spMap f) a ε hD ha hLa
  obtain ⟨ε', hD', -⟩ := exists_diagEnd_isMonHom g n F W _ P' u' hS'
  obtain ⟨a', ha', hLa', hc'⟩ :=
    GenCmp.diagEnd_unique_comm F W P₀ P' (spMap f ≫ u) u' (spMap f') he.symm ε₀ ε' hD₀ hD'
  exact ⟨ε', hD', P₀, a, a', ε₀, ha, ha', hLa, hLa', fun E => ⟨hc₀ E, hc' E⟩⟩

end GlobalTheory.Poinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.MumRig.exists_common_pull_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, Nonempty (IsPullDeg φ D₁.toPre D') → Nonempty (IsPullDeg φ D₂.toPre D') → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₃ : DegData R' (maximalIdeal R')), FinExt ρ ∧ Nonempty (IsPullDeg ρ D₁.toPre D₃.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₃.toPre) := by
  intro R _ _ _ hR D₁ D₂ W _ _ φ hφ D' ⟨h₁⟩ ⟨h₂⟩
  obtain ⟨E₁, E₂, L, _, β, E', ⟨e₁⟩, ⟨e₂⟩, ⟨f₁⟩, ⟨f₂⟩⟩ := _root_.GlobalTheory.Mum.exists_generic_common_pull R hR D₁ D₂ W φ hφ D' h₁ h₂
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨K', _, io, E₃, hio, ⟨g₁⟩, ⟨g₂⟩⟩ := _root_.GlobalTheory.FieldDesc.exists_finite_common_pull (FractionRing R) L β E₁ E₂ E' f₁ f₂
  obtain ⟨R', _, _, _, ρ, E, hfin, hloc, ⟨k₁⟩, ⟨k₂⟩⟩ := _root_.GlobalTheory.CommonCover.exists_common_pull R hR D₁.toPre D₂.toPre E₁ E₂ e₁ e₂ K' io E₃ hio g₁ g₂
  obtain ⟨D₃, ⟨p⟩⟩ := GlobalTheory.MumPull.exists_pull R R' ρ hfin.2.1 hloc D₁
  exact ⟨R', _, _, _, ρ, D₃, hfin, ⟨p⟩, _root_.GlobalTheory.Mum.isPullDeg_of_generic R R' ρ hfin.1 hfin.2.1 D₁.toPre D₂.toPre D₃.toPre E p k₁ k₂⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonScalingDescendsToFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_scaling_descends_to_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))) (N : ℕ) (Ix : Type) (T : Ix → SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) (a : (Kb R →ₐ[FractionRing R] Kb R) → (Kb R)ˣ), (∀ σ i, ∃ t', SecTw σ (T i) t' ∧ ∀ j, t'.f j = liftFun A.A _ (fnF (Kb R) (a σ).val) * (T i).f j) → ∃ c : (Kb R)ˣ, ∀ i, ∃ Φ : H0 A.L N, ∀ t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N, (∀ j, t''.f j = liftFun A.A _ (fnF (Kb R) c.val) * (T i).f j) → Agree A.L t'' Φ := by
  first | exact @GlobalTheory.Mum.exists_common_scale_descends | exact GlobalTheory.Mum.exists_common_scale_descends | (intros; apply GlobalTheory.Mum.exists_common_scale_descends <;> assumption)
end

