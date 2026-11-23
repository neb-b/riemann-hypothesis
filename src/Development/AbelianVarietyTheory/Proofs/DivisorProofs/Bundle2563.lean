module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2423
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalSiegelObjectDeterminedOverArtinianPinch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2180
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelClassifiedAtPrimeSpreadsBasicOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegSpread

theorem spread_point : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := _root_.GlobalTheory.SpreadPoint.exists_away

theorem spread_iso : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (d : SiegPre g n ζ (spMap β)) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) [LocallyOfFinitePresentation sY] (u : SiegPre g n ζ sY) (r₀ : R) (ι₀ : Localization.Away r₀ →+* Localization.AtPrime 𝔭) (h : Sp (Localization.Away r₀) ⟶ Y) (e : SiegPre g n ζ (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))), r₀ ∉ 𝔭 → ι₀.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.AtPrime 𝔭) → h ≫ sY = spMap ((algebraMap R (Localization.Away r₀)).comp β) → SiegPB e d (spMap (algebraMap R (Localization.AtPrime 𝔭))) → SiegPB e u (spMap ι₀ ≫ h) → ∃ r ∉ 𝔭, ∃ (κ : Localization.Away r₀ →+* Localization.Away r) (d' : SiegPre g n ζ (spMap ((algebraMap R (Localization.Away r)).comp β))), κ.comp (algebraMap R (Localization.Away r₀)) = algebraMap R (Localization.Away r) ∧ SiegPB d' d (spMap (algebraMap R (Localization.Away r))) ∧ SiegPB d' u (spMap κ ≫ h) := _root_.GlobalTheory.SiegelSpreadLocal.exists_spread_of_pullbacks

theorem spMap_comp_eq {A C D : Type} [CommRing A] [CommRing C] [CommRing D] (a : A →+* C) (b : C →+* D) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem classified_basicOpen : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)) (𝔭 : Ideal R) [𝔭.IsPrime], c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) → ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧ SiegPB c' F.univ f) → ∃ r ∉ 𝔭, ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.Away r)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.Away r))) → ∃ f : Sp (Localization.Away r) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ SiegPB c' F.univ f := by
  intro g n hg hn hodd F R _ _ β c 𝔭 _ hc H
  obtain ⟨c₀, hc₀⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _)
    (Sp R) (Sp (Localization.AtPrime 𝔭)) (spMap β) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β))
    (spMap (algebraMap R (Localization.AtPrime 𝔭))) rfl (by rw [spMap_comp_eq, spMap_comp_eq, RingHom.comp_id])).1 c
  obtain ⟨f₀, hf₀s, hf₀⟩ := H c₀ hc₀
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI : LocallyOfFinitePresentation F.s := inferInstance
  obtain ⟨r₀, hr₀, ι₀, f₁, hι₀, hf₁s, hf₁⟩ := spread_point (cycAway n) F.X F.s R β 𝔭 f₀ hf₀s
  obtain ⟨r, hr, κ, d', hκ, hd'c, hd'u⟩ := spread_iso g n (cycAway n) (zetaAway n) R β 𝔭 c F.X F.s F.univ r₀ ι₀ f₁ c₀
    hr₀ hι₀ hf₁s hc₀ (hf₁ ▸ hf₀)
  refine ⟨r, hr, fun c' hc' => ⟨spMap κ ≫ f₁, ?_, ?_⟩⟩
  · rw [Category.assoc, hf₁s, spMap_comp_eq, ← RingHom.comp_assoc, hκ]
  · have h₁ : SiegPB c' c (𝟙 _ ≫ spMap (algebraMap R (Localization.Away r))) := by rwa [Category.id_comp]
    have h₂ := GlobalTheory.SiegelPullComp.pb_cancel hd'c h₁
    have h₃ := GlobalTheory.SiegelPullComp.pb_comp hd'u h₂
    rwa [Category.id_comp] at h₃

end GlobalTheory.SiegSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliIntegralNormalLocallyNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelIntegral

theorem exists_complexPoint_mem : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) [LocallyOfFiniteType s] (U : X.Opens),
    (U : Set X).Nonempty → ∃ p : Sp ℂ ⟶ X, p ≫ s = spMap (RingHom.id ℂ) ∧ ∀ z : Sp ℂ, p z ∈ U := by
  intro X s _ U ⟨x, hx⟩
  obtain ⟨a, ha, haU⟩ := GlobalTheory.ConeOnto.exists_rat_pt s U.isOpen.isLocallyClosed hx
  refine ⟨a, ?_, haU⟩
  rw [ha]
  exact (Spec.map_id _).symm

theorem exists_ptAt : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (F : SFam h k ζ), 1 ≤ h → 3 ≤ k →
    Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → ∀ p : Sp ℂ ⟶ F.X, p ≫ F.s = spMap σ →
    ∃ τ : Matrix (Fin h) (Fin h) ℂ, KeyFam.PtAt F.univ p τ := _root_.GlobalTheory.SiegelPtAt.exists_ptAt

noncomputable def conjEmb (n : ℕ) : cycAway n →+* ℂ := (starRingEnd ℂ).comp (cycAway n).subtype

theorem conjEmb_injective (n : ℕ) : Function.Injective (conjEmb n) :=
  (RingHom.injective (starRingEnd ℂ)).comp Subtype.val_injective

theorem conjEmb_zeta (n : ℕ) :
    conjEmb n (zetaAway n) = Complex.exp (-(2 * Real.pi * Complex.I) / n) := by
  simp only [conjEmb, RingHom.coe_comp, Function.comp_apply, Subring.coe_subtype, zetaAway, zeta]
  rw [← Complex.exp_conj]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]

theorem preconnected_of_complex (g n : ℕ) (hg : 1 ≤ g) (hn : 3 ≤ n) (hodd : Odd n)
    (F : SFam g n (conjEmb n (zetaAway n))) : PreconnectedSpace F.X := by
  have hL := GlobalTheory.abelianSchemeLaws_all
  haveI := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  rw [preconnectedSpace_iff_clopen]
  intro W hW
  by_contra hne
  push_neg at hne
  obtain ⟨p, hp, hpW⟩ := exists_complexPoint_mem F.X F.s ⟨W, hW.isOpen⟩ hne.1
  obtain ⟨q, hq, hqW⟩ := exists_complexPoint_mem F.X F.s ⟨Wᶜ, hW.compl.isOpen⟩
    (by simpa [Set.nonempty_compl] using hne.2)
  have hζ : RingHom.id ℂ (conjEmb n (zetaAway n)) = Complex.exp (-(2 * Real.pi * Complex.I) / n) := conjEmb_zeta n
  obtain ⟨τ, hτ⟩ := exists_ptAt g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ p hp
  obtain ⟨τ', hτ'⟩ := exists_ptAt g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ q hq
  obtain ⟨hp', hq', H⟩ := GlobalTheory.SiegelConnected.sameComp_of_ptAt hL.1 hL.2 GlobalTheory.thetaUnifAV_all GlobalTheory.torusAlgebraic_holds
    g n ℂ _ (RingHom.id ℂ) F hg hn hodd hζ τ τ' p q hp hq hτ hτ'
  obtain ⟨z⟩ : Nonempty (Sp ℂ) := inferInstance
  have h1 := (pullback.fst F.s (spMap (RingHom.id ℂ))).continuous.image_connectedComponent_subset
    (pullback.lift q (𝟙 _) hq' z) ⟨_, H z, rfl⟩
  have e : ∀ (r : Sp ℂ ⟶ F.X) (hr : r ≫ F.s = 𝟙 _ ≫ spMap (RingHom.id ℂ)),
      pullback.fst F.s (spMap (RingHom.id ℂ)) (pullback.lift r (𝟙 _) hr z) = r z := fun r hr => by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [e, e] at h1
  exact hW.compl.connectedComponent_subset (hqW z) h1 (hpW z)

end GlobalTheory.SiegelIntegral


open GlobalTheory.SiegelIntegral in
theorem GlobalTheory.SiegelIntegral.integral_normal_noetherian : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    IsIntegral F.X ∧ Geo.Tor.IsNormalScheme F.X ∧ IsLocallyNoetherian F.X := by
  intro g n hg hn hodd F
  have hn0 : n ≠ 0 := by omega
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have hB : Geo.Tor.IsNormalScheme (Sp (cycAway n)) := GlobalTheory.ZJ.isNormalScheme_sp _
  haveI := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  have hN : Geo.Tor.IsNormalScheme F.X :=
    GlobalTheory.SmoothNormal.isNormalScheme_of_smoothOfRelativeDimension _ _ F.s (g * (g + 1) / 2) hB
  haveI hLN : IsLocallyNoetherian F.X := LocallyOfFiniteType.isLocallyNoetherian F.s
  refine ⟨?_, hN, hLN⟩
  haveI : GlobalTheory.IsNormalScheme F.X := GlobalTheory.IsNormalScheme.of_pred hN
  obtain ⟨F', π, hpb, -⟩ := F.exists_baseChange (conjEmb n) (conjEmb_injective n) rfl
  haveI := preconnected_of_complex g n hg hn hodd F'
  have hgen : {x : F.X | (F.s x).asIdeal = ⊥} ⊆ Set.range π := by
    intro x hx
    have hx' : x ∈ Set.range (pullback.fst F.s (spMap (conjEmb n))) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      change (⊥ : Ideal ℂ).comap (conjEmb n) = (F.s x).asIdeal
      rw [hx]
      exact Ideal.comap_bot_of_injective _ (conjEmb_injective n)
    obtain ⟨y, rfl⟩ := hx'
    exact ⟨hpb.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]⟩
  have hpre : _root_.IsPreconnected (Set.univ : Set F.X) :=
    (isPreconnected_range π.continuous).subset_closure (Set.subset_univ _) (by
      rw [← F.isReduced_and_dense.2.closure_eq]
      exact closure_mono hgen)
  obtain ⟨c, hc, -⟩ := GlobalTheory.exists_principal_siegPre_complex g n (Nat.pos_of_ne_zero hn0) (cycAway n)
    (cycAway n).subtype (zetaAway n) (Complex.isPrimitiveRoot_exp n hn0)
  haveI := F.nonempty _ Subtype.val_injective c hc
  haveI : ConnectedSpace F.X := { toPreconnectedSpace := ⟨hpre⟩, toNonempty := inferInstance }
  exact GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace F.X
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectTangentShiftConstancyDirectionIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegTanShift

theorem spMap_comp_spMap' {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (g : A' →+* A) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := Spec.map_id _

theorem isLocalRing_sq (K : Type) [Field K] : IsLocalRing (TrivSqZeroExt K (K × K)) :=
  haveI : Nontrivial (TrivSqZeroExt K (K × K)) := TrivSqZeroExt.inl_injective.nontrivial
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simp only [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_one]
    exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem isArtinianRing_sq (K : Type) [Field K] : IsArtinianRing (TrivSqZeroExt K (K × K)) := by
  haveI : Module.Finite K (TrivSqZeroExt K (K × K)) := inferInstanceAs (Module.Finite K (K × (K × K)))
  exact IsArtinianRing.of_finite K _

theorem pbEq {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S S' : Scheme.{0}}
    {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {c' : SiegPre h k ζ' s'} {c : SiegPre h k ζ s} {f f' : S' ⟶ S}
    (hc : SiegPB c' c f) (e : f = f') : SiegPB c' c f' := e ▸ hc

theorem shift : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (K : Type) [Field K] (r : ℕ) (β : cycAway n →+* K) (G : SiegPre g n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), G.Principal → ∀ (lam κ κ' : (Fin r → K) →ₗ[K] K) (t : K) (c₃ c₁ : SiegPre g n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), κ = κ' + t • lam → SiegPB c₃ G (spMap (dirMap lam)) → SiegPB c₃ G (constPt (spMap (dirMap lam))) → SiegPB c₁ G (spMap (dirMap κ)) → SiegPB c₁ G (spMap (dirMap κ')) := by
  intro g n h3 hodd K _ r β G hG lam κ κ' t c₃ c₁ hκ h₁ h₂ h₃
  subst hκ
  have pull : ∀ {S S' : Scheme.{0}} (s : S ⟶ Sp (cycAway n)) (s' : S' ⟶ Sp (cycAway n)) (f : S' ⟶ S), f ≫ s = s' →
      ∀ c : SiegPre g n (zetaAway n) s, c.Principal →
        ∃ c' : SiegPre g n (zetaAway n) s', SiegPB c' c f ∧ c'.Principal := by
    intro S S' s s' f hf c hc
    have hf' : f ≫ s = s' ≫ spMap (RingHom.id (cycAway n)) := by rw [spMap_id', Category.comp_id]; exact hf
    have pr := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange g n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n)
      (RingHom.id _) S S' s s' f rfl hf'
    obtain ⟨c', hcc⟩ := pr.1 c
    exact ⟨c', hcc, pr.2.1 c c' hcc hc⟩
  have base : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra K R] [Algebra K R'] (f : R →ₐ[K] R'),
      spMap f.toRingHom ≫ spMap ((algebraMap K R).comp β) = spMap ((algebraMap K R').comp β) := by
    intro R R' _ _ _ _ f
    rw [spMap_comp_spMap', ← RingHom.comp_assoc]
    congr 2
    ext x
    simp
  let Φ := TrivSqZeroExt.map (LinearMap.prod κ' (t • lam))
  let p₁ := TrivSqZeroExt.map (LinearMap.fst K K K)
  let p₂ := TrivSqZeroExt.map (LinearMap.snd K K K)
  let ι₁ := TrivSqZeroExt.map (LinearMap.inl K K K)
  let sm := TrivSqZeroExt.map (LinearMap.fst K K K + LinearMap.snd K K K)
  let mt := TrivSqZeroExt.map (t • LinearMap.id : K →ₗ[K] K)
  let cst : TrivSqZeroExt K (Fin r → K) →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K (Fin r → K)).toRingHom
  let cD : DualNumber K →+* DualNumber K := (algebraMap K (DualNumber K)).comp (TrivSqZeroExt.fstHom K K K).toRingHom
  have e1 : p₁.toRingHom.comp Φ.toRingHom = dirMap κ' := by
    ext x <;> simp [p₁, Φ, dirMap]
  have e2 : p₂.toRingHom.comp Φ.toRingHom = dirMap (t • lam) := by
    ext x <;> simp [p₂, Φ, dirMap]
  have e3 : mt.toRingHom.comp (dirMap lam) = dirMap (t • lam) := by
    ext x <;> simp [mt, dirMap]
  have e4 : mt.toRingHom.comp cst = cst := by
    ext x <;> simp [mt, cst]
  have e6 : p₁.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [p₁, ι₁]
  have e7 : p₂.toRingHom.comp ι₁.toRingHom = cD := by
    ext x <;> simp [p₂, ι₁, cD]
  have e8 : sm.toRingHom.comp Φ.toRingHom = dirMap (κ' + t • lam) := by
    ext x <;> simp [sm, Φ, dirMap]
  have e9 : sm.toRingHom.comp ι₁.toRingHom = RingHom.id _ := by
    ext x <;> simp [sm, ι₁]
  have e10 : cD.comp (dirMap κ') = cst := by
    ext x <;> simp [cD, cst, dirMap]
  have hconst : constPt (spMap (dirMap lam)) = spMap cst := by
    simp only [constPt, spMap_comp_spMap']
    congr 1
  obtain ⟨c', hc', hc'p⟩ := pull _ _ (spMap (dirMap κ')) (base (TrivSqZeroExt.map κ')) G hG
  obtain ⟨H, hH, hHp⟩ := pull _ _ (spMap Φ.toRingHom) (base Φ) G hG
  obtain ⟨H'', hH'', hH''p⟩ := pull _ _ (spMap ι₁.toRingHom) (base ι₁) c' hc'p
  obtain ⟨C1, hC1, -⟩ := pull _ (spMap p₁.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₁.toRingHom) rfl H hHp
  obtain ⟨C2, hC2, -⟩ := pull _ (spMap p₂.toRingHom ≫ spMap ((algebraMap K (TrivSqZeroExt K (K × K))).comp β))
    (spMap p₂.toRingHom) rfl H hHp
  have hC1G : SiegPB C1 G (spMap (dirMap κ')) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC1) (by rw [spMap_comp_spMap', e1])
  have hC1c' : SiegPB C1 c' (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq hC1G (by rw [Category.id_comp]))
  have hC1H'' : SiegPB C1 H'' (spMap p₁.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC1c' (by rw [spMap_comp_spMap', e6, spMap_id']))
  have hC2G : SiegPB C2 G (spMap (dirMap (t • lam))) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH hC2) (by rw [spMap_comp_spMap', e2])
  have h₂' : SiegPB c₃ G (spMap cst) := pbEq h₂ hconst
  have hC2m : SiegPB C2 c₃ (spMap mt.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel h₁ (pbEq hC2G (by rw [spMap_comp_spMap', e3]))
  have hC2Gc : SiegPB C2 G (spMap cst) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp h₂' hC2m) (by rw [spMap_comp_spMap', e4])
  have hC2c₃ : SiegPB C2 c₃ (𝟙 _) := GlobalTheory.SiegelPullComp.pb_cancel h₂' (pbEq hC2Gc (by rw [Category.id_comp]))
  have hc₃c' : SiegPB c₃ c' (spMap cD) :=
    GlobalTheory.SiegelPullComp.pb_cancel hc' (pbEq h₂' (by rw [spMap_comp_spMap', e10]))
  have hC2c' : SiegPB C2 c' (spMap cD) := pbEq (GlobalTheory.SiegelPullComp.pb_comp hc₃c' hC2c₃) (by rw [Category.id_comp])
  have hC2H'' : SiegPB C2 H'' (spMap p₂.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH'' (pbEq hC2c' (by rw [spMap_comp_spMap', e7]))
  have hpb := _root_.GlobalTheory.SqZeroPb.isPullback_trivSqZeroExt K (K × K) K K (LinearMap.fst K K K) (LinearMap.snd K K K)
    ⟨fun a b hab => by simpa using hab, fun y => ⟨y, by simp⟩⟩
  have hsurj : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hHH : SiegPB H'' H (𝟙 _) :=
    _root_.GlobalTheory.SiegPinch.siegPB_of_pinch g n h3 hodd (CommRingCat.of (TrivSqZeroExt K (K × K))) (CommRingCat.of (DualNumber K))
      (CommRingCat.of (DualNumber K)) (CommRingCat.of K) _ _ _ _ hpb (isLocalRing_sq K) (isArtinianRing_sq K)
      hsurj hsurj (CommRingCat.ofHom ((algebraMap K (TrivSqZeroExt K (K × K))).comp β)) H H'' C1 C2 hHp hH''p
      hC1 hC1H'' hC2 hC2H''
  have hc₁H : SiegPB c₁ H (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hH (pbEq h₃ (by rw [spMap_comp_spMap', e8]))
  have hc₁H'' : SiegPB c₁ H'' (spMap sm.toRingHom) :=
    GlobalTheory.SiegelPullComp.pb_cancel hHH (pbEq hc₁H (by rw [Category.comp_id]))
  have hc₁c' : SiegPB c₁ c' (𝟙 _) :=
    pbEq (GlobalTheory.SiegelPullComp.pb_comp hH'' hc₁H'') (by rw [spMap_comp_spMap', e9, spMap_id'])
  exact pbEq (GlobalTheory.SiegelPullComp.pb_comp hc' hc₁c') (by rw [Category.id_comp])

end GlobalTheory.SiegTanShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalPolChartsOfSteps5
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.SiegJoin.siegelToroidalPolCharts_of_steps5
    (hF : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n))) (hMin : GlobalTheory.SiegJoin.MinSt5)
    (hPoin : GlobalTheory.Poinc.PoinSt) (hChart : GlobalTheory.SiegJoin.ChartSt5) (hDesc : GlobalTheory.SiegJoin.DescSt5) :
    GlobalTheory.Published.SiegelToroidalPolCharts := by
  intro g hg φ hφ hφ' n hn ho
  have hn0 : n ≠ 0 := by omega
  haveI : IsNoetherianRing (cycAway n) := by haveI := (GlobalTheory.SiegelTor.arBase_cycAway n hn0).1; infer_instance
  obtain ⟨F⟩ := hF g n hg hn ho
  obtain ⟨Z, z, i, OZ, hMA⟩ := hMin g hg n hn ho F
  have hMA' := hMA
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N', ⟨hTh, hZp, hZn, hiz, hid, hOZ, hOZa⟩, -⟩ := hMA'
  obtain ⟨d, J, S, π, j, BD, hd, hJ, hV, hBl, hP, hj, hjd, hji, hjpre, hBD, hVj, k₀, hk₀⟩ :=
    hPoin g hg n hn ho F Z z i hTh OZ hOZ hOZa φ hφ
  haveI := hj
  have hBlow : BlowAt F z i φ d π j BD := ⟨J, hd, hJ, hV, hBl, hP, hjd, hji, hjpre, hBD, hVj⟩
  obtain ⟨hsm, hpre⟩ := hChart g hg φ hφ hφ' n hn ho F Z z i OZ d S π j BD hMA hBlow
  obtain ⟨G, _, e, hGs, hGd, hGe, hGab⟩ :=
    hDesc g hg φ n hn ho F Z z i d S π j BD hBlow hpre
  haveI := hsm
  haveI : Smooth (π ≫ z) := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) _
  haveI : QuasiSeparated G.hom := by haveI := hGs.separated; infer_instance
  obtain ⟨a, N, ha, hN, hiso⟩ := _root_.GlobalTheory.HodgeMin.hodge_pow_iso_pull_pow_of_minimal_compactification g n F Z z i OZ S π j G e hMA
    (fun x => ⟨hBl.1.isDomain_stalk x, hBl.1.isIntegrallyClosed_stalk x⟩) hP hjd hji hGs hGd hGe
  obtain ⟨N'', hN'', hgen, k, hk⟩ := _root_.GlobalTheory.PullPowGen.exists_isGenerated_and_isAmpleLB (cycAway n) Z S z π OZ (hodge G g) (GlobalTheory.CechPic.dual BD.lb) a N
    hZp hOZ hOZa (isLB_hodge G g) (GlobalTheory.CechPic.isLB_dual BD.isLB_lb) ha hN hiso ⟨k₀, hk₀⟩
  refine ⟨F, S, π ≫ z, j, hj, G, inferInstance, e, BD, d, N'', hP, hsm, by rw [← Category.assoc, hji, hiz], ?_,
    hGs, hGd, hGe, hGab, hd, ?_, hN'', hgen, k, hk⟩
  · intro x
    exact _root_.GlobalTheory.FibreDense.mem_closure_fibre F (π ≫ z) j φ BD d x (hpre x)
  · intro x
    exact _root_.GlobalTheory.PolDeg.hasPolChart_of_preChart_of_extension F (π ≫ z) j G e φ BD d x hn0 hGs hGd hGe hGab (hpre x)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoefficientFormsClosedUnderOperations
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem smooth_coeff_closure : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  intro n v
  have hc : ∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v) :=
    fun γ S => contDiffAt_const
  have hs : ∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v) := by
    intro J s α h S
    have heq : (fun x => (bas n).repr (∑ j ∈ s, α j x) S) =
        (fun x => ∑ j ∈ s, (bas n).repr (α j x) S) := by
      funext x
      rw [map_sum]
      exact Finset.sum_apply' (s := s) (f := fun j => (bas n).repr (α j x)) (i := S)
    rw [heq]
    exact ContDiffAt.sum fun j hj => h j hj S
  have hg : ∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v) := by
    intro g α h1 h2 S
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact h1.mul (h2 S)
  refine ⟨hc, hs, hg, ?_⟩
  intro α β ha hb U
  have key : ∀ x, α x * β x = ∑ S, (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T) := by
    intro x
    conv_lhs => rw [← (bas n).sum_repr (α x), ← (bas n).sum_repr (β x)]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [smul_mul_assoc, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [mul_smul_comm]
  simp only [key]
  refine hs _ Finset.univ (fun S x => (bas n).repr (α x) S • ∑ T, (bas n).repr (β x) T • (bas n S * bas n T)) (fun S _ => ?_) U
  refine hg _ _ (ha S) ?_
  refine hs _ Finset.univ (fun T x => (bas n).repr (β x) T • (bas n S * bas n T)) (fun T _ => ?_)
  exact hg _ (fun _ => bas n S * bas n T) (hb T) (hc _)

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfEighthPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowDim

theorem smoothOfRelativeDimension_of_eighthPower : ∀ {S : Scheme.{0}} [IsIntegral S] (G H : Over S) [GrpObj G] [GrpObj H] (g : ℕ) (pr : Fin 8 → (H ⟶ G)) (huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ G)), ∃! x : T ⟶ H, ∀ u, x ≫ pr u = y u) (hG : IsSemiAbelian G) (hH : SmoothOfRelativeDimension (8 * g) H.hom), SmoothOfRelativeDimension g G.hom := by
  intro S _ G H _ _ g pr huniv hG hH
  have hlim : IsLimit (Fan.mk H pr) :=
    mkFanLimit _ (fun s => (huniv s.pt s.proj).choose) (fun s i => (huniv s.pt s.proj).choose_spec.1 i)
      (fun s m hm => (huniv s.pt s.proj).choose_spec.2 m hm)
  let e : H ≅ powObj G 8 := hlim.conePointUniqueUpToIso (powIsLimit G 8)
  have hw : H.hom = e.hom.left ≫ (powObj G 8).hom := (Over.w e.hom).symm
  haveI : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  haveI : Smooth G.hom := hG.smooth
  haveI : GeometricallyConnected G.hom := hG.geomConnected
  haveI : ConnectedSpace S := inferInstance
  haveI : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨s⟩ : Nonempty S := inferInstance
  obtain ⟨n, hn⟩ := Geo.Tor.exists_dim_of_preconnected G.hom (eSec G s)
  have h8 := smoothOfRelativeDimension_powObj G n hn 8
  have h2 : SmoothOfRelativeDimension (0 + 8 * n) H.hom := by
    rw [hw]; infer_instance
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ hH h2 (eSec H s)
  have hgn : g = n := by omega
  subst hgn
  exact hn

end GlobalTheory.PowDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureMapEqOfSameGenericImageModuli
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.baseEq_of_sameImage : ∀ {o R V : Type} [CommRing o] [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {X : Scheme.{0}} (sX : X ⟶ Sp o) (y : Sp (FractionRing R) ⟶ X) (b : o →+* R), y ≫ sX = jK R ≫ spMap b → ∀ (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → θ₁.comp b = θ₂.comp b := by
  intro o R V _ _ _ _ _ X sX y b hy θ₁ θ₂ κ₁ κ₂ h₁ h₂ hκ
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp b) = κ ≫ y ≫ sX := by
    intro θ κ h
    rw [hy, ← Category.assoc, h, Category.assoc]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl
  have e : jK V ≫ spMap (θ₁.comp b) = jK V ≫ spMap (θ₂.comp b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hκ, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this
end

