module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafRetractOfCoinduced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleInjectiveHomFreeEtaleSheafInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoChainsCechOfIsLocallySurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem quasiIso_chains_cech_of_isLocallySurjective : ∀ (R : Type) [CommRing R] (P Q : PSh) (f : P ⟶ Q),
    Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} f →
    QuasiIso ((chains R).map (show ((Arrow.mk f).cechNerve : Spc) ⟶ disc.obj Q from
      (Arrow.mk f).augmentedCechNerve.hom)) := by
  intro R _ P Q f hf
  exact GlobalTheory.T.quasiIso_cechNerveChains_of_etaleLocallySurjective R f (fun U y => ⟨Presheaf.imageSieve f y, hf.imageSieve_mem y, fun V g hg => hg⟩)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCosetSumUnimodularityOfFiniteIndex
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem finsum_quotient_subgroupOf {A : Type} [Group A] (Γ W : Subgroup A) (F : A → ℂ)
    (hΓ : ∀ a, F a ≠ 0 → a ∈ Γ) (hF : ∀ w ∈ W, ∀ a, F (a * w) = F a) :
    ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y : Γ ⧸ W.subgroupOf Γ, F (y.out : Γ) := by
  have hout : ∀ a : A, F (QuotientGroup.mk a : A ⧸ W).out = F a := by
    intro a
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W a
    rw [hw, hF w w.2]
  let e : Γ ⧸ W.subgroupOf Γ → A ⧸ W := fun y => QuotientGroup.mk ((y.out : Γ) : A)
  have hinj : Function.Injective e := by
    intro y z h
    have h1 : ((y.out : Γ) : A)⁻¹ * ((z.out : Γ) : A) ∈ W := QuotientGroup.eq.1 h
    have h2 : (QuotientGroup.mk y.out : Γ ⧸ W.subgroupOf Γ) = QuotientGroup.mk z.out :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (by simpa using h1))
    simpa using h2
  have hsupp : (Function.support fun y : A ⧸ W => F y.out) ⊆ Set.range e := by
    intro y hy
    have hm : y.out ∈ Γ := hΓ _ hy
    refine ⟨QuotientGroup.mk ⟨y.out, hm⟩, ?_⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (W.subgroupOf Γ) ⟨y.out, hm⟩
    have hw' : ((w : Γ) : A) ∈ W := Subgroup.mem_subgroupOf.1 w.2
    show (QuotientGroup.mk _ : A ⧸ W) = y
    rw [hw, Subgroup.coe_mul, QuotientGroup.mk_mul_of_mem _ hw']
    exact QuotientGroup.out_eq' y
  calc ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y ∈ Set.range e, F y.out := by
        rw [← finsum_mem_univ]
        apply finsum_mem_inter_support_eq
        rw [Set.univ_inter, Set.inter_eq_right.2 hsupp]
    _ = ∑ᶠ y, F (e y).out := finsum_mem_range hinj
    _ = _ := finsum_congr fun y => hout _

theorem unimod_of_unimodFin : UnimodFin → Unimod := by
  intro H A _ Γ U V f _ _ hUi hVi hΓ hfV hfU
  have h := H Γ (U.subgroupOf Γ) (V.subgroupOf Γ) (fun a => f a) hUi hVi
    (fun v hv a => hfV _ (Subgroup.mem_subgroupOf.1 hv) _)
    (fun u hu a => hfU _ (Subgroup.mem_subgroupOf.1 hu) _)
  rw [finsum_quotient_subgroupOf Γ U f hΓ hfU,
    finsum_quotient_subgroupOf Γ V (fun a => f a⁻¹) (fun a ha => (inv_mem_iff.1 (hΓ _ ha)))
      (fun w hw a => by rw [mul_inv_rev, hfV _ (inv_mem hw)])]
  exact h

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsInjectiveSheafAcyclic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.restr_injective_acyclic : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I]
    (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) ((restr φ).obj I) n) := by
  intro R S _ _ φ I _ P n hn
  obtain ⟨J, hJ, i, r, hir⟩ := _root_.GlobalTheory.EtC.CoindRetract.coind_retract R S φ I
  obtain ⟨C, ε, hC0, hCi, hqi, hCz⟩ := GlobalTheory.T.exists_coinducedSheaf_injectiveResolution_freeExact R S φ J (_root_.GlobalTheory.EtC.HomInj.hom_free_injective R J)
  have h1 : Subsingleton (HK R (sgl ((free R).obj P)) ((restr φ).obj ((coind φ).obj J)) n) := by
    obtain ⟨e⟩ := _root_.GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution R _ C ε hC0 hCi hqi (sgl ((free R).obj P)) n
    have := hCz P n hn
    exact e.injective.subsingleton
  have h2 : Subsingleton (HK R (sgl ((free R).obj P)) ((restr φ).obj I) n) :=
    _root_.GlobalTheory.EtC.RetractAcyc.subsingleton_of_retract R _ _ ((restr φ).map i) ((restr φ).map r)
      (by rw [← Functor.map_comp, hir]; exact (restr φ).map_id I) _ n h1
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  exact (GlobalTheory.T.quasiIso_hypercohomology_bijective R (e P).hom ((restr φ).obj I) n).1.subsingleton
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

open scoped nonZeroDivisors

theorem GlobalTheory.UCls.selfDual_latOf_translate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → ∃ L : Submodule (𝓞 E) (Fin r → E), (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) ∧ (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) ∧ SelfDualLat G L := by
  intro E _ _ _ r G Λ g0 hΛ hua
  obtain ⟨hG, hdet, hfg, hspan, hsd⟩ := hΛ
  obtain ⟨hunit, hpres⟩ := hua
  let g : GL (Fin r) (RA (maximalRealSubfield E) E) := Matrix.nonsingInvUnit g0 hunit
  have hg : (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) = g0 := rfl
  obtain ⟨L, hL, hLfg, hLspan, hLhat⟩ :=
    GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield E) E r Λ g hfg hspan
  rw [hg] at hL hLhat
  have hmem : ∀ x : E, x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ IsIntegral ℤ x := by
    intro x
    rw [FractionalIdeal.mem_one_iff]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.isIntegral_coe
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hsd' : ∀ v : Fin r → E, (∀ y ∈ Λ, (∑ a, ∑ b, v a * G a b * (IsCMField.complexConj E) (y b)) ∈
      (1 : FractionalIdeal (𝓞 E)⁰ E)) ↔ v ∈ Λ := by
    intro v
    simp only [hmem]
    exact hsd v
  have key := GlobalTheory.AdLat.latOf_selfDual (maximalRealSubfield E) E r Λ (IsCMField.complexConj E) G 1 g
    hfg hspan (IsCMField.complexConj_apply_apply E) hG hdet one_ne_zero hsd' (by rw [hg]; exact hpres)
  rw [hg] at key
  refine ⟨L, hL, hLhat, hG, hdet, hLfg, hLspan, fun x => ?_⟩
  have := key x
  rw [← hL] at this
  simp only [hmem, SetLike.mem_coe] at this
  exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallerUnitaryEmbeddingPreservesIntegralParts
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem embMem : EmbMem := by
  intro L _ _ σ n r e β γ ι hσ hD hι g
  obtain ⟨he, -, -, -, -, hβγ⟩ := hD
  obtain ⟨h1, h2⟩ := hι g
  have hcases : ∀ a b : Fin n, (∃ i j, a = e i ∧ b = e j) ∨ (a ∉ Set.range e ∨ b ∉ Set.range e) := by
    intro a b
    by_cases ha : a ∈ Set.range e
    · by_cases hb : b ∈ Set.range e
      · obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        exact Or.inl ⟨i, j, rfl, rfl⟩
      · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl ha)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_KU_iff hσ, mem_KU_iff hσ]
    refine ⟨fun h i j => h1 i j ▸ h (e i) (e j), fun h a b => ?_⟩
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | hab
    · rw [h1]; exact h i j
    · rw [h2 a b hab, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · rw [h1]
      exact hg i j fun hij => hab ((hβγ i j).2 hij)
    · rw [h2 a b h]
      exact Matrix.one_apply_ne fun h' => hab (h' ▸ rfl)
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · have hji : j ≤ i := he.le_iff_le.1 hab
      rw [h1, hg i j hji, Matrix.one_apply, Matrix.one_apply]
      simp only [he.injective.eq_iff]
    · exact h2 a b h

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadTorsorToEtaleAlgebra
section
open IsLocalRing Polynomial CategoryTheory Limits
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocAcyc

theorem spread_torsor_to_etale : ∀ (T O : Type) [CommRing T] [CommRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale φ →
    ∀ (q : ℕ), 0 < q → ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib T O) D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[GlobalTheory.LocAcyc.GenFib T O] D)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T O) D q act →
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra T E)
      (_ : IsScalarTower T (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E)
      (ψ : E →ₐ[Polynomial T] O) (DE : Type) (_ : CommRing DE)
      (_ : Algebra (GlobalTheory.LocAcyc.GenFib T E) DE)
      (actE : Multiplicative (ZMod q) →* (DE ≃ₐ[GlobalTheory.LocAcyc.GenFib T E] DE)),
      GlobalTheory.LocAcyc.IsZModTorsor (GlobalTheory.LocAcyc.GenFib T E) DE q actE ∧
      ∀ s : DE →+* GlobalTheory.LocAcyc.GenFib T O,
        (∀ e : E, s (algebraMap (GlobalTheory.LocAcyc.GenFib T E) DE (algebraMap E _ e)) =
          algebraMap O (GlobalTheory.LocAcyc.GenFib T O) (ψ e)) →
        Nonempty (D →ₐ[GlobalTheory.LocAcyc.GenFib T O] GlobalTheory.LocAcyc.GenFib T O) := by
  intro T O _ _ _ _ _ P _ φ hφ hind q hq D _ _ act hD
  classical

  obtain ⟨j, Dj, _, _, actj, hDj, ⟨e⟩⟩ := GlobalTheory.T.exists_zmodTorsor_model_of_filtered_colimit _ _ _ (GlobalTheory.FiniteTypeColimit.isColimit
    (CommRingCat.of (GenFib T O))) q hq D act hD
  let U := (GlobalTheory.FiniteTypeColimit.diagram (CommRingCat.of (GenFib T O))).obj j
  let u : U →+* GenFib T O := ((GlobalTheory.FiniteTypeColimit.inclusions (CommRingCat.of (GenFib T O))).app j).hom
  haveI : Algebra.FiniteType ℤ U := GlobalTheory.FiniteTypeColimit.finiteType _ j

  have hfact := _root_.GlobalTheory.IndEtFactorLoc.exists_etale_factor_of_indEt_atPrime (Polynomial T) O P φ hφ hind
  have hl := _root_.GlobalTheory.GenFibLift.exists_etale_genFib_lift T (Polynomial T) O hfact U u
  obtain ⟨W, _, _, _, _, _, ψ, uW, hcomp⟩ := hl
  letI : Algebra U (GenFib T W) := uW.toAlgebra
  obtain ⟨actE, hE⟩ := _root_.GlobalTheory.LocAcyc.exists_isZModTorsor_tensorBase U (GenFib T W) q Dj actj hq hDj
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ψ,
    TensorProduct U (GenFib T W) Dj, inferInstance, inferInstance, actE, hE, ?_⟩
  intro s hs
  have hs' : s.comp (algebraMap (GenFib T W) (TensorProduct U (GenFib T W) Dj)) =
      genFibMap (ψ.restrictScalars T) := by
    refine genFib_ringHom_ext (fun w => ?_)
    rw [RingHom.comp_apply, hs, genFibMap_algebraMap]
    rfl
  letI : Algebra U (GenFib T O) := u.toAlgebra
  let σ : Dj →ₐ[U] GenFib T O :=
    { s.comp (Algebra.TensorProduct.includeRight (R := U) (A := GenFib T W) (B := Dj)).toRingHom with
      commutes' := fun x => by
        change s (Algebra.TensorProduct.includeRight (algebraMap U Dj x)) = u x
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply U (GenFib T W)]
        rw [← RingHom.comp_apply s, hs', ← hcomp]
        rfl }
  let L : TensorProduct U (GenFib T O) Dj →ₐ[GenFib T O] GenFib T O :=
    Algebra.TensorProduct.lift (AlgHom.id (GenFib T O) (GenFib T O)) σ
      (fun _ _ => Commute.all _ _)
  exact ⟨L.comp e.symm.toAlgHom⟩

end GlobalTheory.LocAcyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSpMapFst
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.InvFieldRing

attribute [local instance] Over.cartesianMonoidalCategory

section Val

variable {A : Type} [CommRing A] {Y : Scheme.{0}}

theorem valR_of (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, V)) :
    valR x V f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE V ⊤ h).hom f) := by
  unfold valR
  rw [dite_eq_left h]

theorem valR_add (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f g : Γ(Y, V)) :
    valR x V (f + g) = valR x V f + valR x V g := by
  simp only [valR_of x V h, map_add (f := _)]

theorem valR_mul (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f g : Γ(Y, V)) :
    valR x V (f * g) = valR x V f * valR x V g := by
  simp only [valR_of x V h, map_mul]

theorem valR_appLE {Z : Scheme.{0}} (x : Sp A ⟶ Z) (g : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ g ⁻¹ᵁ V)
    (h : ⊤ ≤ x ⁻¹ᵁ W) (f : Γ(Y, V)) : valR x W ((g.appLE V W e).hom f) = valR (x ≫ g) V f := by
  have h' : ⊤ ≤ (x ≫ g) ⁻¹ᵁ V := h.trans (x.preimage_mono e)
  rw [valR_of x W h, valR_of (x ≫ g) V h', ← Scheme.Hom.appLE_comp_appLE x g V W ⊤ e h]
  rfl

theorem valR_constFn {B : Type} [CommRing B] (x : Sp A ⟶ Y) (p : Y ⟶ Sp B) (ψ : B →+* A) (hx : x ≫ p = spMap ψ)
    (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : B) : valR x V (constFn p V a) = ψ a := by
  unfold constFn
  refine (valR_appLE x p ⊤ V (fun _ _ => trivial) h _).trans ?_
  rw [hx, valR_of _ _ le_rfl]
  have n := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  have e' : ((spMap ψ).appLE ⊤ ⊤ le_rfl) = (spMap ψ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (ψ a) =
    (spMap ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a) at n
  rw [e', ← n]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem valR_spMap_comp {A' : Type} [CommRing A'] (ψ : A →+* A') (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(Y, V)) : valR (spMap ψ ≫ x) V f = ψ (valR x V f) := by
  have h' : ⊤ ≤ (spMap ψ ≫ x) ⁻¹ᵁ V := fun y _ => h (Set.mem_univ ((spMap ψ) y))
  rw [valR_of _ V h', valR_of x V h]
  have e : (spMap ψ ≫ x).appLE V ⊤ h' = x.appLE V ⊤ h ≫ (spMap ψ).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap ψ) x V ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ)
  change ((spMap ψ ≫ x).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom).hom f =
    (x.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom ψ).hom f
  rw [e, Category.assoc, n]

end Val

section Geo

theorem surjective_spMap_fst (R : Type) [CommRing R] : Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber R)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

theorem spMap_fst_comp (R : Type) [CommRing R] :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem appLE_eq_of_eq {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (hg : g = g') (V : Y.Opens) (W : Z.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W ≤ g' ⁻¹ᵁ V) : g.appLE V W e = g'.appLE V W e' := by
  subst hg
  rfl

theorem appLE_appLE {Y Z Q : Scheme.{0}} (g : Z ⟶ Y) (k : Q ⟶ Z) (V : Y.Opens) (W : Z.Opens) (W' : Q.Opens)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ k ⁻¹ᵁ W) (f : Γ(Y, V)) :
    (k.appLE W W' e').hom ((g.appLE V W e).hom f) = ((k ≫ g).appLE V W' (e'.trans (k.preimage_mono e))).hom f := by
  rw [← Scheme.Hom.appLE_comp_appLE k g V W W' e e']
  rfl

theorem appLE_res {Y Z : Scheme.{0}} (g : Z ⟶ Y) {V V' : Y.Opens} {W W' : Z.Opens} (h : V' ≤ V) (h' : W' ≤ W)
    (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ g ⁻¹ᵁ V') (f : Γ(Y, V)) :
    (g.appLE V' W' e').hom (resG Y h f) = resG Z h' ((g.appLE V W e).hom f) := by
  change (Y.presheaf.map (homOfLE h).op ≫ g.appLE V' W' e').hom f = (g.appLE V W e ≫ Z.presheaf.map (homOfLE h').op).hom f
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem appLE_constFn {R : Type} [CommRing R] {Z Q : Scheme.{0}} (p : Z ⟶ Sp R) (k : Q ⟶ Z) (W : Z.Opens)
    (W' : Q.Opens) (e' : W' ≤ k ⁻¹ᵁ W) (a : R) : (k.appLE W W' e').hom (constFn p W a) = constFn (k ≫ p) W' a := by
  unfold constFn
  exact appLE_appLE p k ⊤ W W' _ e' _

theorem constFn_spMap {R S : Type} [CommRing R] [CommRing S] {Y : Scheme.{0}} (q : Y ⟶ Sp S) (φ : R →+* S)
    (O : Y.Opens) (a : R) : constFn (q ≫ spMap φ) O a = constFn q O (φ a) := by
  have h : (spMap φ).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]; rfl
  have h2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3 := congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE q (spMap φ) ⊤ ⊤ O (fun _ _ => trivial) (fun _ _ => trivial))
  rw [h] at h3
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2 h3
  unfold constFn
  rw [← h3, h2]

theorem constFn_eps_sq {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp (DualNumber R)) (O : Y.Opens) :
    constFn p O DualNumber.eps * constFn p O DualNumber.eps = 0 := by
  simp only [constFn, ← map_mul, DualNumber.eps_mul_eps, map_zero]

theorem res_constFn {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) {V W : Y.Opens} (h : W ≤ V) (a : R) :
    resG Y h (constFn f V a) = constFn f W a :=
  congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem res_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V W : Y.Opens} (h : W ≤ V) (h' : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ V) (a : Γ(Y, V)) :
    resG Z h' ((f.app V).hom a) = (f.app W).hom (resG Y h a) := by
  change (f.app V ≫ Z.presheaf.map (homOfLE h').op).hom a = (Y.presheaf.map (homOfLE h).op ≫ f.app W).hom a
  rw [Scheme.Hom.naturality]
  rfl

end Geo

section Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  (U : X.affineOpens) (u : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)

def tanPt (hu : IsTanAtG t (chart U) u) : tEpsG (chart U) ⟶ t.G := Over.homMk u hu.1

def transl (hu : IsTanAtG t (chart U) u) : tEpsG (chart U) ⊗ t.G ⟶ t.G :=
  snd _ t.G * (fst _ t.G ≫ tanPt t U u hu)

end Group

section Group2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
  (U : X.affineOpens) (u : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)

end Group2

end GlobalTheory.InvFieldRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulIsTensorPairingStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_mul_isTensorPairing : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ) := by
  first
  | exact @GlobalTheory.EtC.TwMul.tw_mul_isTensor
  | exact GlobalTheory.EtC.TwMul.tw_mul_isTensor
  | (intros; apply GlobalTheory.EtC.TwMul.tw_mul_isTensor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistOneSectionsEqRootsOfUnityStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistOne_sections_eq_rootsOfUnity : ∀ (q : ℕ) [NeZero q], ∃ e : ∀ (C : Type) [CommRing C], IsUnit (q : C) → (onRings (tw q 1)).obj (CommRingCat.of C) ≃+ Additive (rootsOfUnity q C), ∀ (C D : Type) [CommRing C] [CommRing D] (φ : C →+* D) (hC : IsUnit (q : C)) (hD : IsUnit (q : D)) (x : (onRings (tw q 1)).obj (CommRingCat.of C)), ((Additive.toMul (e D hD (((onRings (tw q 1)).map (CommRingCat.ofHom φ)).hom x)) : rootsOfUnity q D) : Dˣ) = Units.map φ.toMonoidHom ((Additive.toMul (e C hC x) : rootsOfUnity q C) : Cˣ) := by
  first | (exact @GlobalTheory.EtC.tw_one_mu) | (exact GlobalTheory.EtC.tw_one_mu) | (intros; apply GlobalTheory.EtC.tw_one_mu  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionCohomologyMapUniqueStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistReduction_cohomology_map_unique : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (i : ℤ) (ρ ρ' : SemiMap (res _ (tw Q i)) (res _ (tw q i))), (∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), ρ.app U 0 (resGen i ζ) = ρ'.app U 0 (resGen i ζ)) → ∀ (E : Spc) (n : ℤ) (x : Ht Q E n i), ρ.op.app E n x = ρ'.op.app E n x := by
  first
  | exact @GlobalTheory.EtC.RedUniq.op_eq
  | exact GlobalTheory.EtC.RedUniq.op_eq
  | (intros; apply GlobalTheory.EtC.RedUniq.op_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistReductionResolutionMap_generator : ∀ (Q q : ℕ) [NeZero Q] [NeZero q], q ∣ Q → ∀ (i : ℤ) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) → (redMap Q q i).app U 0 (resGen i ζ) = resGen i ξ := by
  first | (exact @GlobalTheory.EtC.RedExists.red_exists) | (exact GlobalTheory.EtC.RedExists.red_exists) | (intros; apply GlobalTheory.EtC.RedExists.red_exists  <;> assumption)
end

