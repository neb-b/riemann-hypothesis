module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSpecProdBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapTmulOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdCoh

theorem cpull_bijective_of_isIso {R : Type} [CommRing R] {K L : Cx R} (c : K ⟶ L) [IsIso c] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull c I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull (inv c) I n, fun x => ?_, fun x => ?_⟩
  · rw [BiprodCls.cpull_cpull, IsIso.inv_hom_id, BiprodCls.cpull_id]
  · rw [BiprodCls.cpull_cpull, IsIso.hom_inv_id, BiprodCls.cpull_id]

theorem bij_of_eq {α β : Sort*} {f g : α → β} (h : ∀ x, f x = g x) (hg : Function.Bijective g) :
    Function.Bijective f := by
  rw [show f = g from funext h]; exact hg

theorem ht_prod_bijective : ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ),
    Function.Bijective (fun x : Ht q (sp (A × B)) n i =>
      (pull _ (spMap (RingHom.fst A B)) _ _ x, pull _ (spMap (RingHom.snd A B)) _ _ x)) := by
  intro q A B _ _ n i
  have h2 := _root_.GlobalTheory.EtC.freeYoneda_desc_isIso (ZMod q) _ _ (_root_.GlobalTheory.EtC.sec_prod (ZMod q) A B)
  have h3 := GlobalTheory.T.etaleChains_disc_biprod_desc_isIso (ZMod q) _ _ h2
  have hc := @cpull_bijective_of_isIso _ _ _ _ _ h3 (res (ZMod q) (tw q i)) n
  have := (cpull_biprod_bijective (ZMod q) _ _ (res (ZMod q) (tw q i)) n).comp hc
  refine bij_of_eq (fun x => ?_) this
  dsimp only [Function.comp]
  erw [BiprodCls.cpull_cpull, BiprodCls.cpull_cpull, biprod.inl_desc, biprod.inr_desc]
  rfl

end GlobalTheory.EtC.ProdCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (arrows := fun _ : Fin (n.unop.len + 1) => yoneda.map f) (yoneda.map f)
    (fun _ => 𝟙 (yoneda.obj Y)) (fun _ => Category.id_comp _)
  naturality m n g := by
    apply WidePullback.hom_ext
    · intro j
      simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]
      rfl

theorem cechDiag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : GlobalTheory.CechOne.cechDiag f ≫ GlobalTheory.EtC.cechAug f = sch.map f := by
  ext n : 1
  simp only [GlobalTheory.CechOne.cechDiag, GlobalTheory.EtC.cechAug]
  erw [NatTrans.comp_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
  rfl

theorem isCls_zero_deg_one (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (R := R) (E := E) (n := 1) (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F)
      (0 : H R E F ((1 : ℕ) : ℤ)) := by
  refine ⟨0, ?_, ?_⟩ <;> simp

theorem cechDiag_δ {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 3) :
    (GlobalTheory.CechOne.cechDiag f).app (op ⦋2⦌) ≫ SimplicialObject.δ (cech f) i = (GlobalTheory.CechOne.cechDiag f).app (op ⦋1⦌) := by
  rw [SimplicialObject.δ, ← NatTrans.naturality]
  simp [sch, disc]

theorem pull_sch_eq_zero (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (s : (free R).obj ((cech f).obj (op ⦋1⦌)) ⟶ F)
    (hs : cobd (R := R) (E := cech f) (n := 1) s = 0)
    (x : H R (sch.obj X) F ((1 : ℕ) : ℤ))
    (hx : IsCls (R := R) (E := cech f) (n := 1) s (pull R (GlobalTheory.EtC.cechAug f) F ((1 : ℕ) : ℤ) x)) :
    pull R (sch.map f) F ((1 : ℕ) : ℤ) x = 0 := by
  have hc := congrArg (fun t => (free R).map ((GlobalTheory.CechOne.cechDiag f).app (op ⦋2⦌)) ≫ t) hs
  simp only [cobd, Preadditive.comp_sum, Preadditive.comp_zsmul, ← Functor.map_comp_assoc, cechDiag_δ,
    comp_zero] at hc
  have hc' : ((free R).map ((GlobalTheory.CechOne.cechDiag f).app (op ⦋1⦌)) ≫ s : (free R).obj ((sch.obj Y).obj (op ⦋2⦌)) ⟶ F) = 0 := by
    simpa [Fin.sum_univ_succ] using hc
  have hd : (free R).map ((GlobalTheory.CechOne.cechDiag f).app (op ⦋1⦌)) ≫ s = 0 := hc'
  have h0 : pull R (GlobalTheory.CechOne.cechDiag f) F ((1 : ℕ) : ℤ) (pull R (GlobalTheory.EtC.cechAug f) F ((1 : ℕ) : ℤ) x) = 0 := by
    obtain ⟨z, hzClass, hz⟩ := hx
    rw [← hzClass]
    simp only [pull, HK.pull, HK.pre, cpre_mk]
    rw [← CohomologyClass.mk_zero]
    apply congrArg CohomologyClass.mk
    apply Cocycle.ext
    change (Cochain.ofHom ((chains R).map (GlobalTheory.CechOne.cechDiag f))).comp z.1 (zero_add _) = 0
    rw [hz, ClsBasic.ofHom_comp_single]
    simp only [← Category.assoc, ClsBasic.chainsXIso_nat]
    simp [Category.assoc, hd]
  rw [← cechDiag_aug f, pull_comp]
  exact h0

end GlobalTheory.CechOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureTorsorOfFractionFields
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

theorem etale_closure_of_field : (∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M))) →
  ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA)).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginBC.BC β DA))) := by
  intro H A R _ _ _ _ _ hAR A₁ R₁ _ _ _ _ _ hAR₁ f hf φ hφ β hβ DA _ _ q act hq hqA htor P₁ _ hS₁ hS π hπ y hy
  haveI := hS₁
  haveI := hS
  letI algSS₁ : Algebra (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁) :=
    (Localization.localRingHom (P₁.comap φ) P₁ φ rfl).toAlgebra
  have hloc : ∀ r : R, algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)
      (algebraMap R (Localization.AtPrime (P₁.comap φ)) r) = algebraMap R₁ (Localization.AtPrime P₁) (φ r) :=
    Localization.localRingHom_to_map _ _ _ rfl
  have hR₁S₁ : Function.Injective (algebraMap R₁ (Localization.AtPrime P₁)) :=
    IsLocalization.injective _ P₁.primeCompl_le_nonZeroDivisors
  have hRS : Function.Injective (algebraMap R (Localization.AtPrime (P₁.comap φ))) :=
    IsLocalization.injective _ (P₁.comap φ).primeCompl_le_nonZeroDivisors
  have hπS : algebraMap A (Localization.AtPrime (P₁.comap φ)) π =
      algebraMap R (Localization.AtPrime (P₁.comap φ)) (algebraMap A R π) :=
    IsScalarTower.algebraMap_apply A R _ π
  have hφw : φ (algebraMap A R π) = algebraMap A₁ R₁ (f π) := by
    rw [← RingHom.comp_apply, hφ]; rfl
  have hπ0 : f π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    have h0 : π = 0 := (injective_iff_map_eq_zero f).1 hf π h
    rw [h0, map_zero]
  have hx0 : algebraMap R₁ (Localization.AtPrime P₁) (φ (algebraMap A R π)) ≠ 0 := by
    rw [hφw]
    intro h
    exact hπ0 ((injective_iff_map_eq_zero _).1 hAR₁ _ ((injective_iff_map_eq_zero _).1 hR₁S₁ _ h))
  have hxu : ¬ IsUnit (algebraMap R₁ (Localization.AtPrime P₁) (φ (algebraMap A R π))) := by
    intro hu
    rw [← hloc] at hu
    haveI := Localization.isLocalHom_localRingHom (P₁.comap φ) P₁ φ rfl
    apply hπ.not_isUnit
    rw [hπS]
    exact isUnit_of_map_unit (Localization.localRingHom (P₁.comap φ) P₁ φ rfl) _ hu
  have hSS₁ : Function.Injective
      (algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0'
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0' hπ
    have h2 := hn.map (algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁))
    rw [hx, map_pow, hπS, hloc] at h2
    exact pow_ne_zero n hx0 (h2.eq_zero_iff.1 rfl)
  have hqS : IsUnit ((q : Localization.AtPrime (P₁.comap φ))) := by
    have := hqA.map (algebraMap A (Localization.AtPrime (P₁.comap φ)))
    rwa [map_natCast] at this
  have hy' : (algebraMap R₁ (Localization.AtPrime P₁) y) ^ q =
      algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)
        (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) := by
    rw [← map_pow, hy, hπS, hloc]
  have hxB : IsUnit (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) (φ (algebraMap A R π))) := by
    rw [hφw]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (f π), f π, mem_nonZeroDivisors_of_ne_zero hπ0, rfl⟩ :
        Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  exact etale_closure_core H A R hAR A₁ R₁ hAR₁ φ β hβ DA q act hq htor
    (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁) hRS hR₁S₁ hloc hSS₁ hqS
    (algebraMap A _ π) hπ (algebraMap R₁ _ y) hy' (φ (algebraMap A R π)) hx0 hxu hxB

end GlobalTheory.KeyOriginTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegrallyClosedInLocalizationStatement
section
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_integrallyClosed_in_localization : ∀ (S E : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [CommRing E] [Algebra S E] [Algebra.Etale S E] (M : Submonoid S), M ≤ nonZeroDivisors S →
    Function.Injective (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))) ∧
    ∀ x : Localization (Algebra.algebraMapSubmonoid E M), IsIntegral S x →
      x ∈ (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))).range := by
  first | (exact @GlobalTheory.EtaleNormalLoc.etale_integrallyClosed_localization) | (exact GlobalTheory.EtaleNormalLoc.etale_integrallyClosed_localization) | (intros; apply GlobalTheory.EtaleNormalLoc.etale_integrallyClosed_localization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPairDichotomy
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.PairDich

theorem isUnit_ι_appTop {T : Scheme.{0}} (W : T.Opens) (E : Γ(T, ⊤)) (h : W ≤ T.basicOpen E) :
    IsUnit (W.ι.appTop E) := by
  refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun w _ => ?_
  have hw : w ∈ W.ι ⁻¹ᵁ T.basicOpen E := h w.2
  rw [Scheme.preimage_basicOpen_top] at hw
  exact (Scheme.mem_basicOpen_top _ _ _).1 hw

theorem mem_basicOpen_or {T : Scheme.{0}} (E : Γ(T, ⊤)) (t : T) :
    t ∈ T.basicOpen E ∨ t ∈ T.basicOpen (1 - E) := by
  rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top, map_sub, map_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem comp_rule {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {T : Scheme.{0}}
    (y : T ⟶ Spec (CommRingCat.of B)) (a : A) :
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (y ≫ Spec.map (CommRingCat.ofHom g)).appTop).hom a =
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop).hom (g a) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end GlobalTheory.EtC.PairDich

namespace GlobalTheory.EtC.PairDich

theorem pair_dich : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) (e u : A' ⊗[A] A'), (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) → algebraMap A (A' ⊗[A] A') f * u = 1 - e → ∀ (T : Scheme.{0}) (y y' : T ⟶ Spec (CommRingCat.of A')), y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) = y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) → Loc T fun V k => k ≫ y = k ≫ y' ∨ IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (k ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop).hom f) := by
  intro A A' _ _ _ f e u he hu T y y' hyy
  let φ : A' →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫ y.appTop).hom
  let φ' : A' →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫ y'.appTop).hom
  have hA : ∀ r : A, φ (algebraMap A A' r) = φ' (algebraMap A A' r) := by
    intro r
    have := congrArg (fun m : T ⟶ Spec (CommRingCat.of A) =>
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ m.appTop).hom r) hyy
    simp only at this
    rw [comp_rule, comp_rule] at this
    exact this
  letI : Algebra A Γ(T, ⊤) := (φ.comp (algebraMap A A')).toAlgebra
  let φa : A' →ₐ[A] Γ(T, ⊤) := ⟨φ, fun _ => rfl⟩
  let φa' : A' →ₐ[A] Γ(T, ⊤) := ⟨φ', fun r => (hA r).symm⟩
  let ψ := Algebra.TensorProduct.productMap φa φa'
  have hE : ∀ a : A', (φ a - φ' a) * ψ e = 0 := by
    intro a
    have := congrArg ψ (he a)
    rw [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, map_one, mul_one, one_mul, map_zero] at this
    exact this
  have hF : ψ (algebraMap A _ f) * ψ u = 1 - ψ e := by rw [← map_mul, hu, map_sub, map_one]
  have hψf : ψ (algebraMap A _ f) = φ (algebraMap A A' f) := by rw [AlgHom.commutes]; rfl
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro t
    have key : ∀ G : Γ(T, ⊤), t ∈ T.basicOpen G → ∃ W : T.Opens, IsAffine W ∧ t ∈ W ∧ IsUnit (W.ι.appTop G) := by
      intro G hG
      obtain ⟨W0, hW, htW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hG
      exact ⟨W0, hW, htW, isUnit_ι_appTop W0 G hWle⟩
    rcases mem_basicOpen_or (ψ e) t with h1 | h2
    · obtain ⟨W, hW, htW, hunit⟩ := key _ h1
      refine ⟨W, W.ι, hW, inferInstance, by rw [Scheme.Opens.range_ι]; exact htW, Or.inl ?_⟩
      apply ext_to_Spec
      simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
      ext a
      have h0 := congrArg W.ι.appTop.hom (hE a)
      rw [map_mul, map_sub, map_zero, hunit.mul_left_eq_zero, sub_eq_zero] at h0
      exact h0
    · obtain ⟨W, hW, htW, hunit⟩ := key _ h2
      refine ⟨W, W.ι, hW, inferInstance, by rw [Scheme.Opens.range_ι]; exact htW, Or.inr ?_⟩
      rw [← Category.assoc, comp_rule, Scheme.Hom.comp_appTop]
      have h0 := congrArg W.ι.appTop.hom hF
      rw [map_mul, hψf] at h0
      rw [← h0] at hunit
      exact isUnit_of_mul_isUnit_left hunit
  · rintro V W g k (h | h)
    · exact Or.inl (by rw [Category.assoc, h, Category.assoc])
    · right
      have hc : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ((k ≫ g) ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop
          = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (g ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop) ≫ k.appTop := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      rw [hc, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h.map _

end GlobalTheory.EtC.PairDich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  first | (exact @GlobalTheory.EtC.PrimLoc.prim_loc) | (exact GlobalTheory.EtC.PrimLoc.prim_loc) | (intros; apply GlobalTheory.EtC.PrimLoc.prim_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeRightEpi
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.MVEpi

theorem exists_prime_over (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)
    (hs : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (hi : ∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})
    (p : PrimeSpectrum A) (hp : f ∈ p.asIdeal) :
    ∃ q : PrimeSpectrum A', PrimeSpectrum.comap (algebraMap A A') q = p := by
  set I : Ideal A := Ideal.span {f} with hI
  set J : Ideal A' := Ideal.span {algebraMap A A' f} with hJ
  have hIJ : I ≤ J.comap (algebraMap A A') := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span rfl
  let φ : A ⧸ I →+* A' ⧸ J := Ideal.quotientMap J (algebraMap A A') hIJ
  have hφ : Function.Bijective φ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro a ha
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hi a ha)
    · intro b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨a, ha⟩ := hs b
      refine ⟨Ideal.Quotient.mk I a, ?_⟩
      rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
      have := J.neg_mem ha
      simpa using this
  let e : A ⧸ I ≃+* A' ⧸ J := RingEquiv.ofBijective φ hφ
  have hIp : I ≤ p.asIdeal := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hp
  let p0 : Ideal (A ⧸ I) := p.asIdeal.map (Ideal.Quotient.mk I)
  have hp0 : p0.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  let q : Ideal A' := (p0.comap (e.symm : A' ⧸ J →+* A ⧸ I)).comap (Ideal.Quotient.mk J)
  have hq : q.IsPrime := Ideal.comap_isPrime _ _
  refine ⟨⟨q, hq⟩, ?_⟩
  ext a
  have he : e.symm (Ideal.Quotient.mk J (algebraMap A A' a)) = Ideal.Quotient.mk I a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  change Ideal.Quotient.mk J (algebraMap A A' a) ∈ p0.comap (e.symm : A' ⧸ J →+* A ⧸ I) ↔ a ∈ p.asIdeal
  rw [Ideal.mem_comap]
  change e.symm (Ideal.Quotient.mk J (algebraMap A A' a)) ∈ p0 ↔ _
  rw [he]
  exact Ideal.mem_quotient_iff_mem hIp

theorem loc_point {X B : Scheme.{0}} (e : B ⟶ X) [Etale e] {T : Scheme.{0}} (x : T ⟶ X) (t : T)
    (ht : x t ∈ Set.range e) :
    ∃ (V : Scheme.{0}) (g : V ⟶ T), IsAffine V ∧ Etale g ∧ t ∈ Set.range g ∧ ∃ y : V ⟶ B, y ≫ e = g ≫ x := by
  obtain ⟨b, hb⟩ := ht
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := x) (g := e) t b hb.symm
  obtain ⟨W0, hW, hzW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (pullback x e).isBasis_affineOpens)
    (show z ∈ (⊤ : (pullback x e).Opens) from trivial)
  let W : (pullback x e).Opens := W0
  haveI : IsAffine W := hW
  refine ⟨W, W.ι ≫ pullback.fst x e, inferInstance, inferInstance, ⟨⟨z, hzW⟩, ?_⟩, W.ι ≫ pullback.snd x e, ?_⟩
  · exact hz1
  · simp [pullback.condition]

theorem epi_of_loc (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E)
    (h : ∀ (T : Scheme.{0}) (x : E.obj (op T)),
      Loc T fun (V : Scheme.{0}) (k : V ⟶ T) => (∃ y, f.app (op V) y = E.map k.op x) ∨ (∃ y, g.app (op V) y = E.map k.op x)) :
    Epi (biprod.desc ((free R).map f) ((free R).map g)) := by
  refine ⟨fun {F} φ ψ hφψ => ?_⟩
  have ef : (free R).map f ≫ φ = (free R).map f ≫ ψ := by
    simpa using congrArg (biprod.inl ≫ ·) hφψ
  have eg : (free R).map g ≫ φ = (free R).map g ≫ ψ := by
    simpa using congrArg (biprod.inr ≫ ·) hφψ
  have res_map : ∀ {G H : Shv R} (χ : G ⟶ H) {V U : Scheme.{0}} (k : V ⟶ U) (s : Sec G U),
      Sec.res k (Sec.map χ s) = Sec.map χ (Sec.res k s) := by
    intro G H χ V U k s
    exact (NatTrans.naturality_apply χ.hom k.op s).symm
  have map_comp : ∀ {G H K : Shv R} (χ : G ⟶ H) (ω : H ⟶ K) {U : Scheme.{0}} (s : Sec G U),
      Sec.map (χ ≫ ω) s = Sec.map ω (Sec.map χ s) := by
    intros; rfl
  obtain ⟨-, hext, hres, -⟩ := GlobalTheory.T.free_sections_ext_res_map R E F
  obtain ⟨-, -, -, hmapP⟩ := GlobalTheory.T.free_sections_ext_res_map R P F
  obtain ⟨-, -, -, hmapQ⟩ := GlobalTheory.T.free_sections_ext_res_map R Q F
  apply hext
  intro T x
  apply (_root_.GlobalTheory.EtC.sec_ext_glue R F T).1
  obtain ⟨S, hS, hP⟩ := h T x
  refine ⟨S, hS, fun V k hk => ?_⟩
  rcases hP V k hk with ⟨y, hy⟩ | ⟨y, hy⟩
  · rw [res_map, res_map, hres, ← hy, ← hmapP, ← map_comp, ← map_comp, ef]
  · rw [res_map, res_map, hres, ← hy, ← hmapQ, ← map_comp, ← map_comp, eg]

end GlobalTheory.EtC.MVEpi

namespace GlobalTheory.EtC.MVEpi

theorem mv_right_epi : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) →
    (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) →
    Epi (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f))))))
      ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) := by
  intro R _ A A' _ _ _ _ f hs hi
  haveI hd : Etale (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  apply epi_of_loc
  intro T (x : T ⟶ Spec (CommRingCat.of A))
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro t
    by_cases hf : f ∈ (x t).asIdeal
    · obtain ⟨q, hq⟩ := exists_prime_over A A' f hs hi (x t) hf
      obtain ⟨V, g, hV, hg, ht, y, hy⟩ :=
        loc_point (Spec.map (CommRingCat.ofHom (algebraMap A A'))) x t ⟨q, hq⟩
      exact ⟨V, g, hV, hg, ht, Or.inr ⟨y, hy⟩⟩
    · have hr : x t ∈ Set.range (PrimeSpectrum.comap (algebraMap A (Localization.Away f))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
        exact hf
      obtain ⟨q, hq⟩ := hr
      obtain ⟨V, g, hV, hg, ht, y, hy⟩ :=
        loc_point (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))) x t ⟨q, hq⟩
      exact ⟨V, g, hV, hg, ht, Or.inl ⟨y, hy⟩⟩
  · rintro V W g k (⟨y, hy⟩ | ⟨y, hy⟩)
    · refine Or.inl ⟨k ≫ y, ?_⟩
      change (k ≫ y) ≫ _ = (k ≫ g) ≫ x
      change y ≫ _ = g ≫ x at hy
      rw [Category.assoc, hy, Category.assoc]
    · refine Or.inr ⟨k ≫ y, ?_⟩
      change (k ≫ y) ≫ _ = (k ≫ g) ≫ x
      change y ≫ _ = g ≫ x at hy
      rw [Category.assoc, hy, Category.assoc]

end GlobalTheory.EtC.MVEpi
end

