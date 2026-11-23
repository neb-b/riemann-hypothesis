module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLocalModelOverDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

private theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel_exists {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

theorem locMod_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (T : CDVR) (iK : z.K →+* T.Fr), ((∀ a : 𝓞 z.K, iK (a : z.K) ∈ Set.range (algebraMap T.V T.Fr)) → Nonempty (LocMod z T iK)) ∧ ∀ (M : LocMod z T iK) (T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∃ (M' : LocMod z T' (i.comp iK)) (n : SABMap M'.G.t M.G.t (spMap ψ)) (n' : SABMap M'.t'.t M.t'.t (spMap i)), M'.m1.φ = n'.φ ≫ M.m1.φ ∧ M'.m2.φ ≫ n.φ = n'.φ ≫ M.m2.φ := by
  intro E _ _ _ H Dw l Xo c _ z T iK
  refine ⟨fun h => ?_, fun M T' ψ i hψ => ?_⟩
  · have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let e : T.V ≃+* (algebraMap T.V T.Fr).range := RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
      ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
    let ρ : 𝓞 z.K →+* T.V := e.symm.toRingHom.comp
      ((iK.comp (algebraMap (𝓞 z.K) z.K)).codRestrict (algebraMap T.V T.Fr).range fun a => h a)
    have hρ : (algebraMap T.V T.Fr).comp ρ = iK.comp (algebraMap (𝓞 z.K) z.K) := by
      ext a
      exact congrArg Subtype.val (e.apply_symm_apply ⟨_, h a⟩)
    obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ρ z.B).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ iK z.Φ.T).1
    obtain ⟨m1, h1⟩ := sab_comp_exists n' z.Φ.m _ rfl
    obtain ⟨k, hk⟩ := sab_comp_exists n' z.m' _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T.V T.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hρ])
    exact ⟨⟨ρ, hρ, G, t', n, n', m1, m2, h1, h2.trans hk⟩⟩
  · obtain ⟨G, n, -⟩ := (pat_pullback E H _ _ ψ M.G).1
    obtain ⟨t', n', -⟩ := (pat_pullback E H _ _ i M.t').1
    obtain ⟨N, hN⟩ := sab_comp_exists n M.n _ (spectrumMap_comp M.ρ ψ)
    obtain ⟨N', hN'⟩ := sab_comp_exists n' M.n' _ (spectrumMap_comp iK i)
    obtain ⟨m1, h1⟩ := sab_comp_exists n' M.m1 (spMap (i.comp iK) ≫ z.x)
      (by rw [spectrumMap_comp, Category.assoc])
    obtain ⟨k, hk⟩ := sab_comp_exists n' M.m2 _ rfl
    obtain ⟨m2, h2⟩ := sab_cancel_exists n k (spMap (algebraMap T'.V T'.Fr))
      (by rw [← spectrumMap_comp, ← spectrumMap_comp, hψ])
    refine ⟨⟨ψ.comp M.ρ, ?_, G, t', N, N', m1, m2, ?_, ?_⟩, n, n', h1, h2.trans hk⟩
    · rw [← RingHom.comp_assoc, hψ, RingHom.comp_assoc, M.hρ, RingHom.comp_assoc]
    · rw [h1, hN', M.h1, Category.assoc]
    · rw [hN, hN', ← Category.assoc, h2, hk, Category.assoc, M.h2, Category.assoc]

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsInverseIsogenyRingOfIntegers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_isGrpPullback_polAV (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), P'.g = P.g ∧ IsGrpPullback P'.A P.A f φ := by
  obtain ⟨P', g, hg, hd, hm, -⟩ := hB S S' f P
  refine ⟨P', g, hd, hg, fun T x y x₀ y₀ hx hy => ?_⟩
  have ex : x₀ = Out.toBase hg.w x := Over.OverMorphism.ext hx
  have ey : y₀ = Out.toBase hg.w y := Over.OverMorphism.ext hy
  rw [ex, ey, ← hm]
  rfl

theorem IsGrpPullback.id_pow_left {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (N : ℕ) :
    (𝟙 G' ^ N).left ≫ φ = φ ≫ (𝟙 G ^ N).left := by
  obtain ⟨E, hE⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h G'
  have h1 : (E (𝟙 G')).left = φ := by rw [hE]; exact Category.id_comp _
  have h2 : E (𝟙 G' ^ N) = E (𝟙 G') ≫ 𝟙 G ^ N := by
    rw [map_pow, MonObj.comp_pow, Category.comp_id]
  rw [← hE, h2, Over.comp_left, h1]

theorem exists_inverse_isogeny_ringOfIntegers :
    ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (P P' : Out.PolAV (Sp (𝓞 K))) (Φ : P.A ⟶ P'.A), P.g = P'.g → IsMonHom Φ → (∀ y : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P'.A, ∃ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ P.A, y = x ≫ Φ) → ∃ (N : ℕ) (ψ : P'.A ⟶ P.A), 0 < N ∧ IsMonHom ψ ∧ Φ ≫ ψ = 𝟙 P.A ^ N ∧ ψ ≫ Φ = 𝟙 P'.A ^ N := by
  intro hT hL hE K _ _ σ P P' Φ hg hΦ honto
  obtain ⟨Q, φ, hQ, hφ⟩ := exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) P
  obtain ⟨Q', φ', hQ', hφ'⟩ := exists_isGrpPullback_polAV hL.polBaseChange (spMap (algebraMap (𝓞 K) K)) P'
  obtain ⟨⟨Φ₀, hΦ₀, -⟩, hmon⟩ := existsUnique_hom_of_isGrpPullback _ _ _ P.A P'.A Q.A Q'.A φ φ' hφ hφ' Φ
  have hm₀ : IsMonHom Φ₀ := hmon Φ₀ hΦ₀ hΦ
  have hs : Surjective Φ.left :=
    (GlobalTheory.OntoSurj.surjective_of_onto_complex_points (𝓞 K) (σ.comp (algebraMap (𝓞 K) K))
      (σ.injective.comp (IsFractionRing.injective (𝓞 K) K)) P'.A P.A Φ P'.isAb P.isAb honto).1
  have hpb : IsPullback φ Φ₀.left Φ.left φ' := by
    refine IsPullback.of_bot ?_ hΦ₀.symm hφ'.1
    rw [Over.w Φ₀, Over.w Φ]
    exact hφ.1
  have hs₀ : Surjective Φ₀.left := MorphismProperty.of_isPullback (P := @Surjective) hpb hs
  obtain ⟨N, ψ₀, hN, hψ₀, e₁, e₂⟩ := _root_.GlobalTheory.exists_inverse_isogeny_polAV hT hL K σ Q Q' Φ₀ (hQ.trans (hg.trans hQ'.symm)) hm₀ hs₀
  obtain ⟨ψ, hψ, eψ, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P'.A P.A Q'.A Q.A φ' φ
    P'.isAb P.isAb hφ' hφ ψ₀ hψ₀
  refine ⟨N, ψ, hN, hψ, ?_, ?_⟩
  · obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P.A P.A Q.A Q.A φ φ
      P.isAb P.isAb hφ hφ (Φ₀ ≫ ψ₀) inferInstance
    refine (hF _ ?_).trans (hF _ ?_).symm
    · rw [Over.comp_left, Over.comp_left, Category.assoc, eψ, ← Category.assoc, hΦ₀, Category.assoc]
    · rw [e₁]; exact IsGrpPullback.id_pow_left hφ N
  · obtain ⟨F, -, -, hF⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hE (𝓞 K) K P'.A P'.A Q'.A Q'.A φ' φ'
      P'.isAb P'.isAb hφ' hφ' (ψ₀ ≫ Φ₀) inferInstance
    refine (hF _ ?_).trans (hF _ ?_).symm
    · rw [Over.comp_left, Over.comp_left, Category.assoc, hΦ₀, ← Category.assoc, eψ, Category.assoc]
    · rw [e₂]; exact IsGrpPullback.id_pow_left hφ' N

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamLettersIsGood
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_lieComb_image {R R' : Type} [CommRing R] [CommRing R'] (A B : Out.PolAV (Sp R)) (x y : KeyIn R')
    (f : Sp R' ⟶ Sp R) (φ : x.P.A.left ⟶ A.A.left) (ψ : y.P.A.left ⟶ B.A.left)
    (hx : IsFibreOf A x f φ) (hy : IsFibreOf B y f ψ) (F : A.A ⟶ B.A) (hF : IsMonHom F) (i : Fin x.P.g) :
    ∃ (u : Fin y.P.g → R') (w : epsR R' ⟶ y.P.A), w.left ≫ ψ = (x.v i).left ≫ φ ≫ F.left ∧ IsLieComb u y.v w := by
  obtain ⟨⟨F', hF', -⟩, hmon⟩ := existsUnique_hom_of_isGrpPullback _ _ f A.A B.A x.P.A y.P.A φ ψ hx.1 hy.1 F
  have hm : IsMonHom F' := hmon F' hF' hF
  have ht : IsTangent (x.v i ≫ F') :=
    ((GlobalTheory.LieCombHom.lieComb_add_pow_map R' x.P.A y.P.A x.P.g x.v x.basis.1).2.2.2 F' hm).1 i
  obtain ⟨u, hu, -⟩ := y.basis.2 _ ht
  exact ⟨u, x.v i ≫ F', by rw [Over.comp_left, Category.assoc, hF'], hu⟩

def blockEquiv {T : Type} (p : T → Prop) [DecidablePred p] (a b : ℕ) {α β : Type} (s : α ≃ {t // p t})
    (s' : β ≃ {t // ¬ p t}) : (Σ t, Fin (if p t then a else b)) ≃ (Fin a × α) ⊕ (Fin b × β) where
  toFun z := if h : p z.1 then Sum.inl (z.2.cast (if_pos h), s.symm ⟨z.1, h⟩)
    else Sum.inr (z.2.cast (if_neg h), s'.symm ⟨z.1, h⟩)
  invFun
    | Sum.inl q => ⟨(s q.2).1, q.1.cast (if_pos (s q.2).2).symm⟩
    | Sum.inr q => ⟨(s' q.2).1, q.1.cast (if_neg (s' q.2).2).symm⟩
  left_inv := by
    rintro ⟨t, i⟩
    by_cases h : p t
    · simp only [dif_pos h]
      refine Sigma.ext (by simp) ?_
      exact (Fin.heq_ext_iff (by simp)).2 rfl
    · simp only [dif_neg h]
      refine Sigma.ext (by simp) ?_
      exact (Fin.heq_ext_iff (by simp)).2 rfl
  right_inv := by
    rintro (q | q)
    · simp [dif_pos (s q.2).2]
    · simp [dif_neg (s' q.2).2]

theorem exists_lamLetters_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∃ L : LamLetters o, L.IsGood ∧ ∀ b : E →+* ℂ, (b (H.rt : E) = H.rt0 → L.m b = nΨ) ∧ (b (H.rt : E) ≠ H.rt0 → L.m b = n') := by
  intro E _ _ _ _ H l c nΨ n' f o La hg
  classical
  obtain ⟨-, -, -, hB, hΨ, h', g1, g2, g3, -, -, -, -, ⟨m1, m2, -⟩, -⟩ := hg
  let p : (E →+* ℂ) → Prop := fun b => b (H.rt : E) = H.rt0
  let ε := blockEquiv p nΨ n' o.τΨ o.τ'
  have hc : Fintype.card ((Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g)) = o.xB.P.g := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [g1, g2, g3]; ring
  let κ := Fintype.equivFinOfCardEq hc
  have hU : ∀ q : (Fin nΨ × Fin o.xΨ.P.g) ⊕ (Fin n' × Fin o.x'.P.g),
      ∃ (u : Fin o.xB.P.g → o.K₁) (w : epsR o.K₁ ⟶ o.xB.P.A),
        (match q with
          | Sum.inl q => w.left ≫ o.φB = (o.xΨ.v q.2).left ≫ o.φΨg ≫ (o.φΨ q.1).left
          | Sum.inr q => w.left ≫ o.φB = (o.x'.v q.2).left ≫ o.φ'g ≫ (o.φ' q.1).left) ∧ IsLieComb u o.xB.v w := by
    rintro (q | q)
    · exact exists_lieComb_image _ _ _ _ _ _ _ hΨ hB _ (m1 q.1) q.2
    · exact exists_lieComb_image _ _ _ _ _ _ _ h' hB _ (m2 q.1) q.2
  choose u w hw hu using hU
  refine ⟨⟨fun b => if p b then nΨ else n', ε.trans κ, κ.symm, fun k => u (κ.symm k),
    fun k => Sum.elim (fun q => o.ℓΨ q.2) (fun q => o.ℓ' q.2) (κ.symm k)⟩, ⟨κ.symm.bijective, ?_, ?_, ?_⟩, ?_⟩
  · intro b i
    have : κ.symm ((ε.trans κ) ⟨b, i⟩) = ε ⟨b, i⟩ := by simp
    simp only [this]
    by_cases h : p b
    · have e1 : ε ⟨b, i⟩ = Sum.inl (i.cast (if_pos h), o.τΨ.symm ⟨b, h⟩) := dif_pos h
      rw [e1]; simp
    · have e1 : ε ⟨b, i⟩ = Sum.inr (i.cast (if_neg h), o.τ'.symm ⟨b, h⟩) := dif_neg h
      rw [e1]; simp
  · intro k
    refine ⟨w (κ.symm k), ?_, hu _⟩
    have := hw (κ.symm k)
    unfold LamLetters.IsLetter
    dsimp only
    generalize κ.symm k = q at this ⊢
    cases q <;> exact this
  · intro k
    dsimp only
    generalize κ.symm k = q
    cases q <;> rfl
  · intro b
    exact ⟨fun h => if_pos h, fun h => if_neg h⟩

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraSquaredLengthCompPairingHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.NormHom

section
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A C : Over S} {A' C' : Over S'}
  [GrpObj A] [GrpObj C] [GrpObj A'] [GrpObj C'] {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left}

theorem push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y :=
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_comp (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) {p : A ⟶ C} {p' : A' ⟶ C'}
    (e : p'.left ≫ ψ = φ ≫ p.left) {T : Over S'} (x : T ⟶ A') :
    pushHom h' T (x ≫ p') = pushHom h T x ≫ p :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, e, Category.assoc])

theorem exists_monHom_lift (h : IsGrpPullback A' A f φ) (h' : IsGrpPullback C' C f ψ) (p : A ⟶ C) [IsMonHom p] :
    ∃ p' : A' ⟶ C', IsMonHom p' ∧ p'.left ≫ ψ = φ ≫ p.left := by
  obtain ⟨p', e⟩ : ∃ p' : A' ⟶ C', p'.left ≫ ψ = φ ≫ p.left :=
    ⟨Over.homMk (h'.1.lift (φ ≫ p.left) A'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h'.1.lift_snd _ _ _),
      h'.1.lift_fst _ _ _⟩
  refine ⟨p', ?_, e⟩
  have h1 : (1 : 𝟙_ (Over S') ⟶ A') ≫ p' = 1 := by
    apply push_inj h'
    rw [push_comp h h' e, map_one, map_one, MonObj.one_comp]
  have h2 : (fst A' A' * snd A' A') ≫ p' = (fst A' A' ≫ p') * (snd A' A' ≫ p') := by
    apply push_inj h'
    rw [push_comp h h' e, map_mul, map_mul, MonObj.mul_comp, push_comp h h' e, push_comp h h' e]
  constructor
  · simpa [Hom.one_def] using h1
  · rw [Hom.mul_def, Hom.mul_def] at h2
    have e1 : lift (fst A' A' ≫ p') (snd A' A' ≫ p') = p' ⊗ₘ p' := by ext <;> simp
    simpa [e1] using h2
end

theorem isVecOver_comp {R R' : Type} [CommRing R] [CommRing R'] {s : R →+* R'} {A C : Over (Sp R)}
    {A' C' : Over (Sp R')} {φ : A'.left ⟶ A.left} {ψ : C'.left ⟶ C.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    (hv : IsVecOver s φ v v') {p : A ⟶ C} {p' : A' ⟶ C'} (e : p'.left ≫ ψ = φ ≫ p.left) :
    IsVecOver s ψ (v ≫ p) (v' ≫ p') := by
  unfold IsVecOver at hv ⊢
  rw [Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hv, Category.assoc]

theorem lieNormSq_comp : ThetaUnifAV → Out.Laws → ∀ (R : Type) [CommRing R] (P P' : Out.PolAV (Sp R)) (f : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (v : epsR R ⟶ P.A) (a : R) (s : R →+* ℂ) (r r' : ℝ), IsMonHom f → IsMonHom g → LamEq P'.L f f P.L g (𝟙 P.A) → IsTangent v → IsLieComb ![a] ![v] (v ≫ g) → IsLieNormSq P v s r → IsLieNormSq P' (v ≫ f) s r' → r' = (s a).re * r := by
  rintro hU hL R _ P P' f g v a s r r' hf hg hlam hv hc ⟨Q, φ, v₁, u, Hm, χ, w, hφ, hv₁, hA, hw, rfl⟩
    ⟨Q', φ', v₁', u', Hm', χ', w', hφ', hv₁', hA', hw', rfl⟩
  obtain ⟨f₁, hf₁, ef⟩ := exists_monHom_lift hφ.2.1 hφ'.2.1 f
  obtain ⟨g₁, hg₁, eg⟩ := exists_monHom_lift hφ.2.1 hφ.2.1 g
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := _root_.GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := _root_.GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨F, hF, -, hFd, -⟩ :=
    GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' f₁ hf₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    GlobalTheory.HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have ht : IsTangent v₁ := hv₁.isTangent hφ.2.1 hv
  have hlam₁ : LamEq Q'.L f₁ f₁ Q.L g₁ (𝟙 Q.A) :=
    _root_.GlobalTheory.CM.lamEq_baseChange _ _ (spMap s) P.A P.A P'.A P.A Q.A Q.A Q'.A Q.A φ φ φ' φ hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      P'.L P.L Q'.L Q.L P'.isLB P.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 f f g (𝟙 _) f₁ f₁ g₁ (𝟙 _) ef ef eg
      (by simp) hlam
  have hweil := _root_.GlobalTheory.CM.weilEq_of_lamEq hL ℂ Q Q Q' Q f₁ f₁ g₁ (𝟙 _) hf₁ hf₁ hg₁ inferInstance hlam₁
  have hherm := (_root_.GlobalTheory.CM.weilEq_iff_hermForm_eq hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA f₁ f₁ g₁ (𝟙 _) F F G LinearMap.id
    hF hF hG (fun z => by simp)).1 hweil w w
  have e₁ : v₁' = v₁ ≫ f₁ :=
    (existsUnique_isVecOver hφ'.2.1.1 (v ≫ f)).unique hv₁' (isVecOver_comp hv₁ ef)
  subst e₁
  have e₂ : w' = F w := (t₁' _ (hFd w v₁ ht hw).1).unique hw' (hFd w v₁ ht hw).2
  have hc₁ := (GlobalTheory.lieComb_baseChange R ℂ s P.A Q.A φ hφ.2.1 1 ![v] (v ≫ g) ![a] ![v₁] (v₁ ≫ g₁)
    (fun j => by fin_cases j; exact hv₁) hc).1 (isVecOver_comp hv₁ eg)
  have hd := GlobalTheory.UnifDifferential.isDiff_of_isLieComb Q.A Q.L Q.g 1 u ![w] ![v₁] _ _
    (fun j => by fin_cases j; exact ht) (fun j => by fin_cases j; exact hw) hc₁
  have e₃ : G w = s a • w := by
    have := (t₁ _ (hGd w v₁ ht hw).1).unique (hGd w v₁ ht hw).2 hd
    simpa using this
  have him : (hermForm Hm w w).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    have hH : ∀ i j, (starRingEnd ℂ) (Hm i j) = Hm j i := fun i j => hA.1.apply j i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj, hH]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e₂, hherm, e₃, LinearMap.id_apply]
  have e₄ : hermForm Hm (s a • w) w = s a * hermForm Hm w w := by
    rw [hermForm, hermForm, smul_dotProduct, smul_eq_mul]
  rw [e₄, Complex.mul_re, him]
  ring

end GlobalTheory.NormHom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.LieLattice

theorem exists_smul_eq_sum_rows {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {g : ℕ} (M : Matrix (Fin g) (Fin g) K) (hM : M.det ≠ 0) (c : Fin g → K) :
    ∃ d : O, d ≠ 0 ∧ ∃ a : Fin g → O, d • c = ∑ j, a j • M j := by
  obtain ⟨x, hx⟩ : ∃ x : Fin g → K, Matrix.vecMul x M = c :=
    ⟨Matrix.vecMul c M⁻¹, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.vecMul_one]⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose a ha using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, a, ?_⟩
  rw [← hx, Matrix.vecMul_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_assoc, ← ha j, algebraMap_smul]

theorem fg_and_span_eq_top {O K : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {g n : ℕ} (L : Submodule O (Fin g → K)) (r : Fin n → O)
    (M : Fin n → Matrix (Fin g) (Fin g) K) (hr : Ideal.span (Set.range r) = ⊤) (hM : ∀ i, (M i).det ≠ 0)
    (hL : ∀ c, c ∈ L ↔ ∀ i, ∃ (k : ℕ) (a : Fin g → O), r i ^ k • c = ∑ j, a j • M i j) :
    L.FG ∧ Submodule.span K (L : Set (Fin g → K)) = ⊤ := by
  constructor
  · let N : Submodule O (Fin g → K) := Submodule.span O (Set.range fun p : Fin n × Fin g => M p.1 p.2)
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine Submodule.FG.of_le hN fun c hc => ?_
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem N (Set.range r) hr c ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨k, a, h⟩ := (hL c).1 hc i
    refine ⟨k, ?_⟩
    change r i ^ k • c ∈ N
    rw [h]
    exact N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  · classical
    rw [eq_top_iff]
    intro c _
    choose d hd a ha using fun i => exists_smul_eq_sum_rows (O := O) (M i) (hM i) c
    have hD : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hd i
    have hmem : (∏ i, d i) • c ∈ L := by
      refine (hL _).2 fun i => ⟨0, fun j => (∏ l ∈ Finset.univ.erase i, d l) * a i j, ?_⟩
      rw [pow_zero, one_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, ha, Finset.smul_sum]
      simp only [mul_smul]
    have hK : algebraMap O K (∏ i, d i) ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    have e : c = (algebraMap O K (∏ i, d i))⁻¹ • ((∏ i, d i) • c) := by
      rw [← algebraMap_smul K (∏ i, d i) c, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem lieLat_fg_and_span_eq_top :
    ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P),
      F.lieLat.FG ∧ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) = ⊤ := by
  intro K _ _ P F
  obtain ⟨n, r, M, hr, hM, hL, -⟩ := _root_.GlobalTheory.CM.LieGlue.exists_cover_lieLat K P F
  exact fg_and_span_eq_top F.lieLat r M hr (fun i => (hM i).2) hL

end GlobalTheory.CM.LieLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataBaseChangeKeyPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem fibKey_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
  intro E _ _ _ H Dw l Xo S S' _ _ hS φ x x' Φ Φ' s s' hx ht ht' hs
  obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ x x' (spMap φ) Φ.m Φ'.m hx).1
  obtain ⟨hg, -, w, hw⟩ := (pat_pullback E H S S' φ Φ.T).2 Φ'.T n hS
  obtain ⟨θ, hθ⟩ := GlobalTheory.ArcQBC.exists_pullSec n.φ Φ.th
  have hm : IsoMaps w Φ'.th θ := ((TieCalc.secTie_calc E H Dw l Xo S x Φ.T.t Φ.m Φ.th s ht).2 S' φ x' Φ'.T.t Φ'.m n s' w θ
    Φ'.th hx hn.symm hs hw hθ).1 ht'
  obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange S S' φ Φ.T.t.G Φ'.T.t.G n.φ n.cart Φ.T.t.semi.smooth Φ.T.g Φ.v Φ.basis
  have hb : ∀ (k : ℕ) (hk : k = Φ.T.g), IsLieBasis fun i : Fin k => u (i.cast hk) := by
    rintro _ rfl
    exact hu
  have hv : ∀ i : Fin Φ'.T.g, (u (i.cast hg)).left ≫ n.φ = spMap (Formalism.L2.Pj.dualMap φ) ≫ (Φ.v (i.cast hg)).left :=
    fun i => huv _
  have he : eSec Φ'.T.t.G ≫ n.φ = spMap φ ≫ eSec Φ.T.t.G := n.cm.e_comm.trans (congrArg (· ≫ eSec Φ.T.t.G) n.base)
  have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec Φ'.T.t.G ≫ n.φ = e ≫ eSec Φ.T.t.G),
      rigPullOf n.φ e he Φ.T.t.PP.L Φ.T.t.PP.rig = n.cm.rigPull Φ.T.t.PP.L Φ.T.t.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨hg, fun i => u (i.cast hg), hb _ hg, ⟨n.φ, he, w, hg, Formalism.L2.Pj.dualMap φ, n.cart, hw.1, ?_, fun j i h => ?_,
    fun a => ?_, ?_, hv⟩, fun i => ?_⟩
  · exact (hr _ n.base he).symm ▸ hw.2
  · refine Eq.trans ?_ (hm j i)
    have le : (Φ.T.t.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ Φ.T.t.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
    rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  · ext <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Formalism.L2.Pj.dualMap]
  · rw [← hn, ← Category.assoc, hv, Category.assoc]

end GlobalTheory.LamT
end

