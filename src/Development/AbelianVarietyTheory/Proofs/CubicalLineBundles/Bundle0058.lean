module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomFamilyOfPureTypeComplexTriple
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodModelOfPowQuotient
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.PowQuotient

variable {S S' : Scheme.{0}}

theorem isMonHom_prod {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj H] {n : ℕ} (a : Fin n → (G ⟶ H))
    (ha : ∀ i, IsMonHom (a i)) : IsMonHom (∏ i, a i) :=
  Finset.prod_induction a (fun z => IsMonHom z) (fun x y _ _ => isMonHom_mul x y) isMonHom_one fun i _ => ha i

end GlobalTheory.PowQuotient

namespace GlobalTheory

open PowQuotient

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLamObjGoodOfCmObj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF

theorem prod_ofFn_sum {M : Type} [Monoid M] {p q : ℕ} (f : Fin p ⊕ Fin q → M) :
    (List.ofFn fun i : Fin (p + q) => f (finSumFinEquiv.symm i)).prod =
      (List.ofFn fun i => f (Sum.inl i)).prod * (List.ofFn fun i => f (Sum.inr i)).prod := by
  rw [List.ofFn_add, List.prod_append]
  congr 2
  · congr 1
    funext i
    exact congrArg f (finSumFinEquiv_symm_apply_castAdd i)
  · congr 1
    funext i
    exact congrArg f (finSumFinEquiv_symm_apply_natAdd i)

theorem lamEq_adj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} (t : SAB H S)
    (a : 𝓞 E) : LamEq t.PP.L (t.act.act a) (𝟙 t.G) t.PP.L (𝟙 t.G) (t.act.act (H.bar a)) := by
  have := t.adj a
  unfold LamEq
  rw [Category.comp_id, Category.comp_id]
  exact this

theorem exists_lamObjGood_of_cmObj : Out.SecTwistSt → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l), (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q) (La : ℝ), (∀ τ, τ ∈ psiSet H ↔ labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → ∀ (xB : KeyIn K) (φB : xB.P.A.left ⟶ X.B.pol.A.left), IsFibreOf X.B.pol xB (gmap K) φB → ∃ (oa : X.B.pol.OAct (𝓞 E)) (oaΨ : (X.A true).pol.OAct (𝓞 E)) (oa' : (X.A false).pol.OAct (𝓞 E)) (xΨ x' : KeyIn K) (φΨ : xΨ.P.A.left ⟶ (X.A true).pol.A.left) (φ' : x'.P.A.left ⟶ (X.A false).pol.A.left) (τΨ : Fin xΨ.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}) (τ' : Fin x'.P.g ≃ {τ : E →+* ℂ // τ (H.rt : E) ≠ H.rt0}) (ℓΨ : Fin xΨ.P.g → MLine K) (ℓ' : Fin x'.P.g → MLine K) (Tl LamL : MLine K), oa.act = X.B.t.act.act ∧ oaΨ.act = (X.A true).t.act.act ∧ oa'.act = (X.A false).t.act.act ∧ LamObjGood (LamObj.mk (c := c) (nΨ := p) (n' := q) K X.B.pol oa (X.A true).pol oaΨ (X.A false).pol oa' (fun i => X.φ (Sum.inl i)) (fun i => X.φ (Sum.inr i)) (fun i => X.hh (Sum.inl i)) (fun i => X.hh (Sum.inr i)) xB xΨ x' φB φΨ φ' τΨ τ' ℓΨ ℓ' Tl LamL) (Module.finrank ℚ E / 2) La := by
  intro hS hU hL hX E _ _ _ _ H l c hstar K _ _ _ ρ σ₁ p q X La hρ hLa xB φB hB
  obtain ⟨hbij, -, -, ρ', -, h₁, h₂, hc, -⟩ := labK_spec E H l c K
  have hfpos : 0 < Module.finrank ℚ E / 2 := by
    have e := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at e
    have : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  have hρρ : ρ' = ρ := by
    have : Nonempty (psiSet H) := (Nat.card_pos_iff.1 (hc ▸ hfpos)).1
    obtain ⟨τ, hτ⟩ := this
    exact Subtype.ext (((h₁ τ).1 hτ).symm.trans ((hρ τ).1 hτ))
  subst hρρ
  obtain ⟨oa, hoa, hR⟩ := _root_.GlobalTheory.LamF.exists_oAct_rosatiConj hL E H hstar K X.B
  obtain ⟨oaΨ, hoaΨ, hRΨ⟩ := _root_.GlobalTheory.LamF.exists_oAct_rosatiConj hL E H hstar K (X.A true)
  obtain ⟨oa', hoa', hR'⟩ := _root_.GlobalTheory.LamF.exists_oAct_rosatiConj hL E H hstar K (X.A false)
  obtain ⟨xΨ, φΨ, τΨ, hFΨ, hgΨ, hTΨ⟩ := _root_.GlobalTheory.LamF.exists_eigenbasis_fibre hS hL E H K (X.A true) oaΨ (psiSet H) (labK c K) ρ' hoaΨ hbij
    X.ρ_sq hρ X.typeP
  obtain ⟨x', φ', τ', hF', hg', hT'⟩ := _root_.GlobalTheory.LamF.exists_eigenbasis_fibre hS hL E H K (X.A false) oa' (psiSet H)ᶜ (labK c K) (-ρ') hoa' hbij
    (by rw [neg_sq, X.ρ_sq]) h₂ ((hasType_neg_iff E H _ _ _ ρ' 0 1 X.ρ_sq).1 X.typeM)
  choose ℓΨ hℓΨ using _root_.GlobalTheory.LamF.exists_isVecLine hS hU hL K _ xΨ φΨ hFΨ
  choose ℓ' hℓ' using _root_.GlobalTheory.LamF.exists_isVecLine hS hU hL K _ x' φ' hF'
  obtain ⟨Tl, LamL, k₁, k₂, k₃, k₄, k₅⟩ := GlobalTheory.LamF.exists_keyLines hS hU hL hX K _ xB φB hB
  have pB := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ xB φB).1 hB
  have pΨ := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ xΨ φΨ).1 hFΨ
  have p' := (isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) _ x' φ').1 hF'
  have gB : X.B.g = Module.finrank ℚ E / 2 * (p + q) :=
    (_root_.GlobalTheory.CM.EigDec.eigen_decomposition E H K ρ' X.B ⟨xB.P, φB, pB, xB.v, xB.basis⟩ p q X.split X.typeB X.ρ_sq).2.2.2.1
  have gA : ∀ b, (X.A b).g = Module.finrank ℚ E / 2 := fun b => by
    cases b
    · exact p'.1.symm.trans hg'
    · exact pΨ.1.symm.trans hgΨ
  have hlam : ∀ j, LamEq X.B.pol.L (X.φ j) (X.φ j) (X.A j.isLeft).pol.L ((X.A j.isLeft).t.act.act (X.hh j))
      (𝟙 (X.A j.isLeft).pol.A) := fun j =>
    (_root_.GlobalTheory.PairingFibre.lamEq_weilEq_over_ring hL (𝓞 K) (X.A j.isLeft).pol (X.A j.isLeft).pol X.B.pol (X.A j.isLeft).pol _ _ _ _
      (X.lin j).isMonHom (X.lin j).isMonHom ((X.A j.isLeft).t.act.hom _) inferInstance ℂ
      (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance
      (σ₁.injective.comp (IsFractionRing.injective (𝓞 K) K)) (X.weil j)
  have hsym : ∀ j, star (X.hh j) = X.hh j := fun j => (hstar _).trans
    (GlobalTheory.LamF.bar_eq_of_lamEq_multiplier hL E H K (X.A j.isLeft).pol X.B.pol (X.A j.isLeft).t.act (X.φ j) (X.hh j)
      (by change 1 ≤ (X.A j.isLeft).g; rw [gA]; exact hfpos) (lamEq_adj _) (hlam j))
  have hpol := fun j : Fin p ⊕ Fin q => _root_.GlobalTheory.LamF.weilIs_iff_of_lamEq_id hL K (X.A j.isLeft).pol X.B.pol (X.φ j) ((X.A j.isLeft).t.act.act (X.hh j))
    (X.lin j).isMonHom ((X.A j.isLeft).t.act.hom (X.hh j)) (hlam j)
  refine ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, hoaΨ, hoa', ?_⟩
  refine ⟨hR, hRΨ, hR', hB, hFΨ, hF', hgΨ, hg', pB.1.trans gB, hTΨ, hT', fun i a => ?_, fun i a => ?_,
    ⟨fun i => (X.lin (Sum.inl i)).isMonHom, fun i => (X.lin (Sum.inr i)).isMonHom, ?_⟩,
    ⟨fun i => hsym (Sum.inl i), fun i => hsym (Sum.inr i), fun i => ?_, fun i => ?_⟩,
    ⟨fun i => hLa (Sum.inl i), fun i => hLa (Sum.inr i)⟩, hℓΨ, hℓ', k₁, k₂, k₃, k₄, k₅⟩
  · dsimp only
    rw [hoa, hoaΨ]
    exact (X.lin (Sum.inl i)).comm a
  · dsimp only
    rw [hoa, hoa']
    exact (X.lin (Sum.inr i)).comm a
  · refine _root_.GlobalTheory.LamF.exists_inverse_isogeny_of_sum hU hL hX K σ₁ (X.A true).pol (X.A false).pol X.B.pol p q _ _
      (fun i => (X.lin (Sum.inl i)).isMonHom) (fun i => (X.lin (Sum.inr i)).isMonHom) ?_ fun y => ?_
    · change X.B.g = p * (X.A true).g + q * (X.A false).g
      rw [gB, gA, gA]
      ring
    · obtain ⟨x, hx⟩ := X.onto y
      exact ⟨fun i => x (Sum.inl i), fun i => x (Sum.inr i), hx.trans (prod_ofFn_sum fun j => x j ≫ X.φ j)⟩
  · dsimp only
    rw [hoaΨ]
    exact hpol (Sum.inl i)
  · dsimp only
    rw [hoa']
    exact hpol (Sum.inr i)

end GlobalTheory.LamF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorDecompositionPureTypeCmTriple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.Recog

theorem ontoAt_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {I : Type} {B A : Over S} {B' A' : Over S'}
    [GrpObj A] [GrpObj A'] {φ : B'.left ⟶ B.left} {χ : A'.left ⟶ A.left} (hφ : φ ≫ B.hom = B'.hom ≫ f)
    (hχ : IsGrpPullback A' A f χ) {ψ : I → (B ⟶ A)} {ψ' : I → (B' ⟶ A')}
    (hψ : ∀ i, (ψ' i).left ≫ χ = φ ≫ (ψ i).left) {k : Type} [Field k] {t' : Sp k ⟶ S'} {t : Sp k ⟶ S}
    (ht : t = t' ≫ f) (h : OntoAt (B := fun _ => B') ψ' t') : OntoAt (B := fun _ => B) ψ t := by
  intro y
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hχ t' t ht
  obtain ⟨n, i, x, hx⟩ := h (e.symm y)
  refine ⟨n, i, fun m => Over.homMk ((x m).left ≫ φ) ?_, ?_⟩
  · have hw := Over.w (x m)
    simp only [Over.mk_hom] at hw ⊢
    rw [Category.assoc, hφ, ← Category.assoc, hw, ht]
  · calc y = e (e.symm y) := (e.apply_symm_apply y).symm
      _ = (List.ofFn fun m => e (x m ≫ ψ' (i m))).prod := by
        rw [hx, map_list_prod, List.map_ofFn]; rfl
      _ = _ := by
        congr 1
        refine List.ofFn_inj.mpr (funext fun m => ?_)
        apply Over.OverMorphism.ext
        rw [he, Over.comp_left, Over.comp_left, Category.assoc, hψ]
        rfl

private lemma spMap_comp_moduli_spaces {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_isTen_of_hasType : ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [NumberField k] (ω : 𝓞 k) (C : Ell H (𝓞 k) ω) (T : PAT H (Sp (𝓞 k))) (r : ℕ), C.IsPrincipalAt ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) → HasType H T.t.act (2 * ω - 1) r 0 →
  ∃ (k₁ : IntermediateField ℚ ℂ) (_ : NumberField k₁) (hk : k ≤ k₁) (ω₁ : 𝓞 k₁) (C₁ : Ell H (𝓞 k₁) ω₁) (φ : C₁.P.A.left ⟶ C.P.A.left) (T₁ : PAT H (Sp (𝓞 k₁))) (_ : SABMap T₁.t T.t (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom))) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), EllMap C₁ C (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) φ ∧ D.p + D.q = r ∧ IsKForm D ε h ∧ (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) ∧ Nonempty (IsTen C₁ D h T₁) := by
  intro hU hL hD E _ _ _ H k _ ω C T r hP hT
  have hB : Out.PolBaseChangeSt := hL.polBaseChange

  obtain ⟨Ck, φk, hCk⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k) ω C k (algebraMap (𝓞 k) k)
  obtain ⟨Tk, mk, -⟩ := _root_.GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (algebraMap (𝓞 k) k)) T
  obtain ⟨Cc, φc, hCc⟩ := GlobalTheory.CM.exists_ellMap hB E H k _ Ck ℂ (algebraMap k ℂ)
  obtain ⟨Tc, mc, -⟩ := _root_.GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (algebraMap k ℂ)) Tk
  have hPk : Ck.IsPrincipalAt (algebraMap k ℂ) :=
    (GlobalTheory.CM.EllComp.ellMap_comp E H (𝓞 k) ω C k _ Ck (algebraMap (𝓞 k) k) φk hCk).2.1 _ hP
  have hPc : Cc.IsPrincipalAt (RingHom.id ℂ) :=
    (GlobalTheory.CM.EllComp.ellMap_comp E H k _ Ck ℂ _ Cc (algebraMap k ℂ) φc hCc).2.1 _ (by rwa [RingHom.id_comp])
  obtain ⟨nc, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp mk mc
  rw [spMap_comp_moduli_spaces] at nc
  have hinj : Function.Injective ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) := by
    rw [RingHom.coe_comp]
    exact (algebraMap k ℂ).injective.comp (IsFractionRing.injective (𝓞 k) k)
  have hTc := (GlobalTheory.CM.hasType_baseChange E H (𝓞 k) ℂ _ T.t Tc.t nc (2 * ω - 1) r 0).1 hinj hT
  have hωc : ((algebraMap k ℂ).comp (algebraMap (𝓞 k) k)) (2 * ω - 1) =
      2 * algebraMap k ℂ (algebraMap (𝓞 k) k ω) - 1 := by
    simp only [map_sub, map_mul, map_ofNat, map_one, RingHom.comp_apply]
  rw [hωc] at hTc

  obtain ⟨D, ε, h, ψc, hpq, hK, hpos, hFc, hOc⟩ := _root_.GlobalTheory.CM.exists_isFam_of_pureType hU hL E H _ Cc Tc r hPc hTc

  obtain ⟨k₁, hfin, hk, huniv⟩ := _root_.GlobalTheory.CM.isFam_descends_to_numberField hU hL E H k _ Ck D h Tk ⊤ _ Cc φc Tc mc ψc hCc hFc
  have : FiniteDimensional ℚ k₁ := hfin
  have : NumberField k₁ := ⟨⟩
  obtain ⟨C₁, φ₁, hC₁⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k) ω C (𝓞 k₁)
    (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom)
  obtain ⟨T₁, m₁, -⟩ := _root_.GlobalTheory.CM.PAT.exists_pullback E H _ _
    (spMap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom)) T
  obtain ⟨C₂, φa, hC₂⟩ := GlobalTheory.CM.exists_ellMap hB E H (𝓞 k₁) _ C₁ k₁ (algebraMap (𝓞 k₁) k₁)
  obtain ⟨T₂, ma, -⟩ := _root_.GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (algebraMap (𝓞 k₁) k₁)) T₁
  have hring : (algebraMap (𝓞 k₁) k₁).comp
      (RingOfIntegers.mapRingHom (IntermediateField.inclusion hk).toRingHom) =
      (IntermediateField.inclusion hk).toRingHom.comp (algebraMap (𝓞 k) k) := by
    ext x; rfl
  have hring' : (algebraMap k₁ ℂ).comp (IntermediateField.inclusion hk).toRingHom = algebraMap k ℂ := by
    ext x; rfl
  have h21 := (GlobalTheory.CM.EllComp.ellMap_comp E H (𝓞 k) ω C (𝓞 k₁) _ C₁ _ φ₁ hC₁).1 k₁ _ C₂ _ φa hC₂
  rw [hring] at h21
  obtain ⟨φ₂, hφ₂, -⟩ := GlobalTheory.CM.Factor.ellMap_cancel hCk h21
  have hCc' : EllMap Cc Ck ((algebraMap k₁ ℂ).comp (IntermediateField.inclusion hk).toRingHom) φc := by
    rw [hring']; exact hCc
  obtain ⟨φ₃, hφ₃, hφ₃c⟩ := GlobalTheory.CM.Factor.ellMap_cancel hφ₂ hCc'
  obtain ⟨n21, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ ma
  obtain ⟨m₂, -⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H k k k₁ (RingHom.id k)
    (IntermediateField.inclusion hk).toRingHom).2 _ _ _ T.t Tk.t T₂.t mk n21
    (by rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, hring])
  obtain ⟨m₃, hm₃⟩ := (GlobalTheory.CM.Factor.ellMap_cancel_and_sabMap_cancel E H k₁ k₁ ℂ (RingHom.id k₁)
    (algebraMap k₁ ℂ)).2 _ _ _ Tk.t T₂.t Tc.t m₂ mc (by rw [spMap_comp_moduli_spaces, hring'])
  obtain ⟨ψ₂, hF₂, hψ₂⟩ := huniv k₁ hk le_rfl _ C₂ φ₂ φ₃ T₂ m₂ m₃ hφ₂ hφ₃ hφ₃c hm₃

  obtain ⟨ψ₁, hF₁, hψ₁⟩ := _root_.GlobalTheory.isFam_extends_dedekind hL hD E H (𝓞 k₁) k₁ _ C₁ D h T₁ ⊤ _ C₂ φa T₂ ma ψ₂ hC₂ hF₂

  obtain ⟨n1, hn1⟩ := GlobalTheory.ObjMaps.exists_sab_comp ma m₃
  obtain ⟨-, ⟨-, ⟨hsq3, -⟩, -⟩, -⟩ := hφ₃
  obtain ⟨-, ⟨-, ⟨hsqa, -⟩, -⟩, -⟩ := hC₂
  have hOnto : OntoAt ψ₁ (spMap ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁))) := by
    refine ontoAt_of_isGrpPullback (φ := φ₃ ≫ φa) (χ := n1.φ) ?_ n1.cart (fun a => ?_) ?_ hOc
    · rw [Category.assoc, hsqa.w, ← Category.assoc, hsq3.w, Category.assoc]
    · rw [hn1, ← Category.assoc, hψ₂ a, Category.assoc, hψ₁ a, Category.assoc]
    · rw [spMap_comp_moduli_spaces, spMap_comp_moduli_spaces, RingHom.id_comp]
  have hinj₁ : Function.Injective ((algebraMap k₁ ℂ).comp (algebraMap (𝓞 k₁) k₁)) := by
    rw [RingHom.coe_comp]
    exact (algebraMap k₁ ℂ).injective.comp (IsFractionRing.injective (𝓞 k₁) k₁)
  exact ⟨k₁, inferInstance, hk, _, C₁, φ₁, T₁, m₁, D, ε, h, hC₁, hpq, hK, hpos,
    _root_.GlobalTheory.CM.nonempty_isTen_of_isFam_top hL E H (𝓞 k₁) _ _ C₁ D ε h T₁ ψ₁ hinj₁ hK hpos hF₁ hOnto⟩

end GlobalTheory.CM.Recog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamLenOfIsHerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem lamLen_of_isHerm : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] (H : Host E) (l : Level H) (c : Coeff l) (nΨ n' f : ℕ) (o : LamObj c nΨ n') (La : ℝ), LamObjGood o f La → ∀ L : LamLetters o, L.IsGood → ∀ (hf : IsPolFibre (algebraMap (𝓞 o.K₁) o.K₁) o.B o.xB.P o.φB) (h : HermFam o.K₁ (Fin o.xB.P.g → o.K₁)), (GenFib.mk o.xB.P o.φB hf o.xB.v o.xB.basis : GenFib o.B).IsHerm h → ∀ (σ : o.K₁ →+* ℂ), o.LamL.n σ = Real.sqrt (h.gram σ (fun i : Fin o.xB.P.g => Pi.single i 1)).det.re ∧ ∀ k, (h.form σ (L.U k) (L.U k)).re ≤ (La * (L.ℓ k).n σ) ^ 2 := by
  intro hU hL E _ _ _ _ H l c nΨ n' f o La hG L hLg hp h Hh σ
  obtain ⟨-, -, -, -, hΨ, hA', -, -, -, tΨ, t', -, -, hI, hP, hb, vΨ, v', -, hgood, -, harch, -⟩ := hG
  refine ⟨?_, fun k => ?_⟩
  · have := GlobalTheory.CM.TopLieVector.sq_eq_det_gram hU hL o.K₁ o.B o.xB o.φB hp h Hh o.Tl o.LamL σ (harch σ)
    exact ((congrArg Real.sqrt this).symm.trans (Real.sqrt_sq (hgood.2 σ).le)).symm
  · obtain ⟨w, hw1, hw2⟩ := hLg.2.2.1 k
    have h4 := hLg.2.2.2 k
    unfold LamLetters.IsLetter at hw1
    cases hs : L.src k with
    | inl q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.AΨ o.B o.oaΨ o.xΨ o.φΨg (S := psiSet H) o.τΨ _ hΨ tΨ
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φΨ q.1) (hI.1 _) (o.hΨ q.1) (hP.2.2.1 q.1) La
        (hb.1 q.1) q.2 _ (vΨ q.2) _ w hw2 hw1 σ
    | inr q =>
      rw [hs] at hw1 h4
      simp only at hw1 h4
      rw [h4]
      exact form_letter_le hU hL o.A' o.B o.oa' o.x' o.φ'g (S := (psiSet H)ᶜ) o.τ' _ hA' t'
        (GenFib.mk o.xB.P o.φB hp o.xB.v o.xB.basis) h Hh (o.φ' q.1) (hI.2.1 _) (o.h' q.1) (hP.2.2.2 q.1) La
        (hb.2 q.1) q.2 _ (v' q.2) _ w hw2 hw1 σ

end GlobalTheory.LamF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIsogenousDedekind
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.AmpleDedekind

theorem range_spMap_fractionRing (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Set.range (spMap (algebraMap R K)) = {genericPoint (Sp R)} := by
  have h : ∀ p : Sp K, spMap (algebraMap R K) p = genericPoint (Sp R) := fun p => by
    rw [genericPoint_eq_bot_of_affine]
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap R K) (PrimeSpectrum.asIdeal p) = ⊥
    have hp : PrimeSpectrum.asIdeal p = ⊥ := Ideal.eq_bot_of_prime (K := K) _ (h := p.isPrime)
    rw [hp]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  exact Set.eq_singleton_iff_unique_mem.2
    ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), h _⟩, by rintro _ ⟨p, rfl⟩; exact h p⟩

theorem relAmple_of_generic_of_isogenous : Out.Laws → Out.Laws2 → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (P : Out.PolAV (Sp R)) (B : Over (Sp R)) [GrpObj B] (Ψ : P.A ⟶ B) (M : LB B.left) (B₀ : Over (Sp K)) [GrpObj B₀] (φ : B₀.left ⟶ B.left) (M₀ : LB B₀.left), IsAbelianScheme B → M.IsLB → M₀.IsLB → IsFinite Ψ.left → Flat Ψ.left → Surjective Ψ.left → IsGrpPullback B₀ B (spMap (algebraMap R K)) φ → LBIso M₀ (M.pull φ) → Out.RelAmple B₀ M₀ → Out.RelAmple B M := by
  intro h₁ h₂ R K _ _ _ _ _ P B _ Ψ M B₀ _ φ M₀ hB hM hM₀ hfin hfl hsurj hpb hiso hamp
  have := hB.proper
  have := P.isAb.proper
  have hsq := hpb.1
  have : IsProper B₀.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq inferInstance
  have : IsLocallyNoetherian (Sp R) := inferInstance
  have a₀ : IsAmpleLB (M.pull φ) :=
    (isAmpleLB_congr hM₀ (LB.isLB_pull hM φ) hiso).1 ((relAmple_iff_isAmpleLB_of_isAffine B₀ hM₀).1 hamp)
  let x := spMap (algebraMap R K)
  let g : pullback P.A.hom x ⟶ B₀.left :=
    hsq.lift (pullback.fst P.A.hom x ≫ Ψ.left) (pullback.snd P.A.hom x)
      (by rw [Category.assoc, Over.w Ψ]; exact pullback.condition)
  have e₁ : g ≫ φ = pullback.fst P.A.hom x ≫ Ψ.left := hsq.lift_fst _ _ _
  have e₂ : g ≫ B₀.hom = pullback.snd P.A.hom x := hsq.lift_snd _ _ _
  have sq : IsPullback (pullback.fst P.A.hom x) g Ψ.left φ := by
    refine IsPullback.of_bot ?_ e₁.symm hsq
    rw [e₂, Over.w Ψ]
    exact IsPullback.of_hasPullback _ _
  have : IsFinite g := MorphismProperty.of_isPullback (P := @IsFinite) sq hfin
  have hΨ := LB.isLB_pull hM Ψ.left
  have a₁ : IsAmpleLB ((M.pull Ψ.left).pull (pullback.fst P.A.hom x)) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hM φ) g) (LB.isLB_pull hΨ _)
      (FiniteAmple.lbIso_pull_pull φ hM e₁)).1 (a₀.pull_of_isFinite g)
  have : IsProper ((Over.pullback x).obj P.A).hom :=
    inferInstanceAs (IsProper (pullback.snd P.A.hom x))
  have a₂ : Out.RelAmple P.A (M.pull Ψ.left) :=
    AmpleSpecialisation.relAmple_of_genericFibre h₁ h₂ (Sp R) P (M.pull Ψ.left) K x hΨ (range_spMap_fractionRing R K)
      ((relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback x).obj P.A) (LB.isLB_pull hΨ _)).2 a₁)
  exact (relAmple_finite_pow_iso (Sp R) P.A B Ψ M 1 one_pos P.isAb hB hM hfin).2.2.1 hfl hsurj a₂

end GlobalTheory.AmpleDedekind
end
end

