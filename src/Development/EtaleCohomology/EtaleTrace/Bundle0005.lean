module

public import Development.EtaleCohomology.EtaleTrace.Bundle0004
public import Development.EtaleCohomology.EtaleTrace.Bundle0003

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleTrace.CocEqPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CochainComplex.HomComplex Opposite

namespace LateralTheory.EtaleTrace

theorem free_ext (R : Type) [CommRing R] (P : PSh) {G : Shv R} (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)),
      (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := Scheme.etaleTopology) (P := (freeP R).obj P) f.hom g.hom G.property ?_
  ext U : 2
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  have := h U.unop x
  simp only [freeGen] at this
  simp only [freeP, ModuleCat.freeMk] at this
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  exact this

theorem cocEq : CocEq := by
  intro R _ F X α β h
  apply Cocycle.ext
  apply Cochain.ext₀
  intro q
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
    exact (CochainComplex.isZero_of_isStrictlyGE (res R F) 0 q hq).eq_of_tgt _ _
  · have key : (chainsXIso R (sch.obj X) 0).inv ≫ α.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) =
        (chainsXIso R (sch.obj X) 0).inv ≫ β.1.v _ _ (show -((0:ℕ):ℤ) + 0 = 0 by simp) := by
      apply free_ext
      intro U x
      exact h U x
    have := congrArg (fun φ => (chainsXIso R (sch.obj X) 0).hom ≫ φ) key
    simpa using this
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i hi
    change -(i:ℤ) = q at hi
    omega

theorem CocEq_of : CocEq := cocEq

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.FibreOfEtalePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

lemma isPullback_equalizer {k : Type} [Field k] {X P : Scheme.{0}} (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P)
    (hπ : π ≫ r = p) (t : Pt r) :
    IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π t.1 := by
  have key : ∀ {T : Scheme.{0}} (a : T ⟶ X) (b : T ⟶ S k), a ≫ π = b ≫ t.1 → a ≫ p = b := by
    intro T a b h
    rw [← hπ, ← Category.assoc, h, Category.assoc, t.2, Category.comp_id]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ ?_ ?_ ?_ ?_)
  · rw [Category.assoc]; exact equalizer.condition _ _
  · intro s
    exact equalizer.lift s.fst (by rw [s.condition, ← Category.assoc, key s.fst s.snd s.condition])
  · intro s; exact equalizer.lift_ι _ _
  · intro s
    rw [← Category.assoc, equalizer.lift_ι]; exact key s.fst s.snd s.condition
  · intro s m h1 _
    apply equalizer.hom_ext
    exact h1.trans (equalizer.lift_ι _ _).symm

theorem FibreOfEtale_of : FibreOfEtale := by
  intro k _ X P p r π hπ V hE t ht
  have hr : Set.range t.1.base ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact ht x
  set t' := IsOpenImmersion.lift V.ι t.1 hr
  have ht' : t' ≫ V.ι = t.1 := IsOpenImmersion.lift_fac _ _ _
  have s := (congrArg (IsPullback (equalizer.ι π (p ≫ t.1)) (equalizer.ι π (p ≫ t.1) ≫ p) π) ht').mpr
    (isPullback_equalizer p r π hπ t)
  have h := IsPullback.of_right' s (isPullback_morphismRestrict π V).flip
  exact MorphismProperty.of_isPullback h hE

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenAwayEvalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

variable {k : Type} [Field k] {N : ℕ}

theorem fromSpec_eq {f : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hf : f ∈ A k N d) (hd : 0 < d) :
    (Proj.isAffineOpen_basicOpen (A k N) f hf hd).fromSpec =
      Spec.map (Proj.awayToSection (A k N) f) ≫ Proj.awayι (A k N) f hf hd := by
  rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
  have e : (Proj.isAffineOpen_basicOpen (A k N) f hf hd).isoSpec.hom ≫ Spec.map (Proj.awayToSection (A k N) f) =
      (Proj.basicOpenIsoSpec (A k N) f hf hd).hom := by
    rw [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec, IsAffineOpen.isoSpec_hom]
  rw [e, Iso.hom_inv_id, Category.id_comp]

theorem constSecC {f : MvPolynomial (Fin (N + 1)) k} {d : ℕ} (hf : f ∈ A k N d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (CommRingCat.of (A k N 0))).inv ≫
      (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top =
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f := by
  have hU := Proj.isAffineOpen_basicOpen (A k N) f hf hd
  have key : hU.fromSpec ≫ Proj.toSpecZero (A k N) =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫ Proj.awayToSection (A k N) f) := by
    rw [fromSpec_eq hf hd, Category.assoc, Proj.awayι_toSpecZero, Spec.map_comp]
  have h1 : (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) f) le_top ≫
      hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge =
      (hU.fromSpec ≫ Proj.toSpecZero (A k N)).appLE ⊤ ⊤ (by simp) := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  simp only [key] at h1
  have h3 : hU.fromSpec.appLE _ ⊤ hU.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg (_ ≫ ·) ((congrArg _ (Subsingleton.elim _ (𝟙 _))).trans ((Spec _).presheaf.map_id _))).trans
      (Category.comp_id _)
  have h4 : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S) e, (Spec.map g).appLE ⊤ ⊤ e = (Spec.map g).appTop := fun _ _ => rfl
  rw [h3, h4] at h1
  rw [← cancel_mono (Scheme.ΓSpecIso _).inv, Category.assoc, h1, Scheme.ΓSpecIso_inv_naturality]

theorem kHom_eq {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (ι : X ⟶ PN k N) (hp : ι ≫ PNto k N = p)
    (i : Fin (N + 1)) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) (c : k) :
    kHom p c = X.presheaf.germ _ (genericPoint X) h ((ι.app _).hom ((Proj.awayToSection (A k N) (MvPolynomial.X i)).hom
      (HomogeneousLocalization.fromZeroRingHom _ _ (algebraMap k (A k N 0) c)))) := by
  subst hp
  have hC := constSecC (X_mem k N i) one_pos
  have e1 : kHom (ι ≫ PNto k N) = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫
      X.presheaf.germ _ (genericPoint X) h).hom := by
    rw [kHom, ← X.presheaf.germ_res (homOfLE (le_top : ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i) ≤ ⊤)) _ h]
    rfl
  have e2 : (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top ≫
        ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e3 : (PNto k N).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      (Spec.map (CommRingCat.ofHom (algebraMap k (A k N 0)))).appTop ≫
        (Proj.toSpecZero (A k N)).appLE ⊤ (Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top :=
    Scheme.Hom.comp_appLE _ _ _ _ _
  have e4 : ι.appLE (Proj.basicOpen (A k N) (MvPolynomial.X i)) _ le_rfl = ι.app _ := Scheme.Hom.appLE_eq_app _
  have e5 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (ι ≫ PNto k N).appLE ⊤ (ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) le_top =
      CommRingCat.ofHom (algebraMap k (A k N 0)) ≫ (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom _ _) ≫
        Proj.awayToSection (A k N) (MvPolynomial.X i)) ≫ ι.app _ := by
    rw [e2, e3, e4, ← hC]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k (A k N 0)))
    simp only [Category.assoc] at n ⊢
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) n.symm).trans (by simp only [Category.assoc]))
  rw [e1, ← Category.assoc, e5]
  rfl

theorem eval₂_mul_pow {σ R L : Type} [CommSemiring R] [CommRing L] (F : R →+* L) (a b : σ → L) (t : L)
    (hab : ∀ j, a j * t = b j) {m : ℕ} {g : MvPolynomial σ R} (hg : g.IsHomogeneous m) :
    eval₂ F a g * t ^ m = eval₂ F b g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_eval₂Hom, map_sum, ← coe_eval₂Hom, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.mp hs)
  simp only [coe_eval₂Hom, eval₂_monomial, Finsupp.prod]
  rw [mul_assoc]
  congr 1
  have hm : m = ∑ j ∈ s.support, s j := by
    rw [← hd]
    simp [Finsupp.weight_apply, Finsupp.sum]
  rw [hm, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => by rw [← mul_pow, hab]

theorem mk_eq_eval (i : Fin (N + 1)) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • 1)) :
    HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg =
      eval₂ ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0)))
        (fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) g := by
  apply HomogeneousLocalization.val_injective
  let vH : HomogeneousLocalization (A k N) (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) →+*
      Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k)) :=
    { toFun := fun y => y.val, map_one' := HomogeneousLocalization.val_one,
      map_mul' := HomogeneousLocalization.val_mul, map_zero' := HomogeneousLocalization.val_zero,
      map_add' := HomogeneousLocalization.val_add }
  change _ = vH _
  rw [eval₂_comp_left]
  have hgh : g.IsHomogeneous m := by simpa using (mem_homogeneousSubmodule _ _).1 hg
  set L := Localization (Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) k))
  have hF : vH.comp ((HomogeneousLocalization.fromZeroRingHom (A k N) _).comp (algebraMap k (A k N 0))) =
      (algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C := by
    ext c
    simp [vH, HomogeneousLocalization.fromZeroRingHom]
    rfl
  have hab : ∀ j, (vH ∘ fun j => HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) 1 (X j) (X_mem' k N j)) j *
      algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i) = algebraMap (MvPolynomial (Fin (N + 1)) k) L (X j) := by
    intro j
    simp only [Function.comp_apply, vH, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    simp only [pow_one]
    exact IsLocalization.mk'_spec _ _ _
  have key := eval₂_mul_pow ((algebraMap (MvPolynomial (Fin (N + 1)) k) L).comp C) _ _ _ hab hgh
  rw [hF, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change _ = _ * algebraMap (MvPolynomial (Fin (N + 1)) k) L (X i ^ m)
  rw [map_pow, key]
  exact (congrArg _ (eval₂_eta g)).symm.trans (eval₂_comp_left _ _ _ _)

theorem GenAwayEval_of : GenAwayEval := by
  intro k _ X _ p N ι hp i h m g hg
  let φ : HomogeneousLocalization.Away (A k N) (MvPolynomial.X i) →+* X.functionField :=
    (X.presheaf.germ _ (genericPoint X) h).hom.comp
      ((ι.app _).hom.comp (Proj.awayToSection (A k N) (MvPolynomial.X i)).hom)
  have e : away ι (MvPolynomial.X i) (X_mem k N i) h m g hg =
      φ (HomogeneousLocalization.Away.mk (A k N) (X_mem k N i) m g hg) := rfl
  rw [e, mk_eq_eval, eval₂_comp_left]
  congr 1
  ext c
  exact (kHom_eq p ι hp i h c).symm

end LateralTheory.EtaleTrace.Cov.GenInPf
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenEtalePf
section
namespace LateralTheory.EtaleTrace.GenEtaleRing

theorem ring_gen_etale (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing B] [IsDomain B] [Algebra A B] [FaithfulSMul A B] [Module.Finite A B]
    [Algebra.IsEtaleAt A (⊥ : Ideal B)] :
    ∃ a : A, a ≠ 0 ∧ ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra A A'] [Algebra B B']
      [Algebra A' B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap A B a) B' → Algebra.Etale A' B' := by
  haveI : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.1 inferInstance
  obtain ⟨f, hf, hEt⟩ := Algebra.exists_etale_of_isEtaleAt (R := A) (⊥ : Ideal B)
  have hf0 : f ≠ 0 := by simpa using hf
  obtain ⟨a, ha, g, hg⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) f).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf0)
  refine ⟨a, ha, fun A' B' _ _ _ _ _ _ _ _ hA hB => ?_⟩
  have hloc : Algebra.Etale A (Localization.Away (algebraMap A B a)) := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale] at hEt ⊢
    refine subset_trans ?_ hEt
    rw [hg]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  haveI : Algebra.Etale A B' := Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A B a))
      (Localization.Away (algebraMap A B a)) B').restrictScalars A)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) B' := by
    rw [Algebra.algebraMapSubmonoid_powers]; exact hB
  haveI : Algebra.FormallyEtale A' B' := Algebra.FormallyEtale.localization_base (Submonoid.powers a)
  haveI : Algebra.FiniteType A A' := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers a) A'
  haveI : Algebra.FinitePresentation A' B' :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A A' B'
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.EtaleTrace.GenEtaleRing

open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

def GenAffineSetup : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P]
  (p : X ⟶ S k) (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified →
  ∃ U : P.Opens, IsAffineOpen U ∧ (U : Set P).Nonempty ∧ IsAffineOpen (π ⁻¹ᵁ U) ∧ IsNoetherianRing Γ(P, U) ∧
    (π.app U).hom.Finite ∧ Function.Injective (π.app U).hom ∧
    ∃ _ : (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)).IsPrime, (letI := (π.app U).hom.toAlgebra; Algebra.IsEtaleAt Γ(P, U) (⊥ : Ideal Γ(X, π ⁻¹ᵁ U)))

def EtaleOverBasic : Prop := ∀ {X P : Scheme.{0}} (π : X ⟶ P) (U : P.Opens), IsAffineOpen U → IsAffineOpen (π ⁻¹ᵁ U) →
  ∀ a : Γ(P, U), (letI := (π.app U).hom.toAlgebra;
    ∀ (A' B' : Type) [CommRing A'] [CommRing B'] [Algebra Γ(P, U) A'] [Algebra Γ(X, π ⁻¹ᵁ U) B']
      [Algebra A' B'] [Algebra Γ(P, U) B'] [IsScalarTower Γ(P, U) A' B'] [IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) B'],
      IsLocalization.Away a A' → IsLocalization.Away (algebraMap Γ(P, U) Γ(X, π ⁻¹ᵁ U) a) B' → Algebra.Etale A' B') →
  Etale (π ∣_ P.basicOpen a)

theorem GenEtale_of (h1 : GenAffineSetup) (h2 : EtaleOverBasic) : GenEtale := by
  intro k _ _ X P _ _ p r π hπ hr hfin hsurj hun
  obtain ⟨U, hU, hne, hU', hnoeth, hfinU, hinj, _, het⟩ := h1 k p r π hπ hr hfin hsurj hun
  haveI : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  haveI : Nonempty (π ⁻¹ᵁ U) := by
    obtain ⟨x, hx⟩ := hsurj.surj hne.some
    exact ⟨⟨x, show π x ∈ U by rw [hx]; exact hne.some_mem⟩⟩
  letI := (π.app U).hom.toAlgebra
  haveI : Module.Finite Γ(P, U) Γ(X, π ⁻¹ᵁ U) := hfinU
  haveI : FaithfulSMul Γ(P, U) Γ(X, π ⁻¹ᵁ U) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  obtain ⟨a, ha, H⟩ := LateralTheory.EtaleTrace.GenEtaleRing.ring_gen_etale Γ(P, U) Γ(X, π ⁻¹ᵁ U)
  refine ⟨P.basicOpen a, ?_, h2 π U hU hU' a H⟩
  by_contra hc
  rw [Set.not_nonempty_iff_eq_empty] at hc
  have : P.basicOpen a = ⊥ := by ext1; simpa using hc
  exact ha ((basicOpen_eq_bot_iff a).1 this)

end LateralTheory.EtaleTrace.Cov
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenOfAwayPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov.GenInPf

variable {k : Type} [Field k] {N : ℕ}

def pg {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) (U : (PN (k := k) N).Opens)
    (hU : genericPoint X ∈ ι ⁻¹ᵁ U) : Γ(PN (k := k) N, U) →+* X.functionField :=
  (ι.app U ≫ X.presheaf.germ _ (genericPoint X) hU).hom

theorem pg_res {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) {U V : (PN (k := k) N).Opens} (hVU : V ≤ U)
    (hV : genericPoint X ∈ ι ⁻¹ᵁ V) (hU : genericPoint X ∈ ι ⁻¹ᵁ U) (s : Γ(PN (k := k) N, U)) :
    pg ι V hV ((PN (k := k) N).presheaf.map (homOfLE hVU).op s) = pg ι U hU s := by
  show (((PN (k := k) N).presheaf.map (homOfLE hVU).op ≫ ι.app V) ≫ X.presheaf.germ _ _ hV).hom s = _
  rw [Scheme.Hom.naturality, Category.assoc, TopCat.Presheaf.germ_res]
  rfl

theorem away_eq {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n)) :
    away ι f hf h m g hg = pg ι _ h (Proj.awayToSection _ f (Away.mk _ hf m g hg)) := rfl

theorem away_identity (x f g : MvPolynomial (Fin (N + 1)) k) {n m : ℕ} (hx : x ∈ A k N 1) (hf : f ∈ A k N n)
    (hg : g ∈ A k N (m • n)) (hf' : f ∈ A k N (n • 1)) (hg' : g ∈ A k N ((m * n) • 1)) :
    awayMap (A k N) hx (show x * f = f * x from mul_comm _ _) (Away.mk _ hf m g hg) *
      awayMap (A k N) hf (show x * f = x * f from rfl) (Away.mk _ hx n f hf') ^ m =
      awayMap (A k N) hf (show x * f = x * f from rfl) (Away.mk _ hx (m * n) g hg') := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, awayMap_mk,
    Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, one_mul]
  ring

theorem away_self_pow (x : MvPolynomial (Fin (N + 1)) k) (hx : x ∈ A k N 1) (n : ℕ)
    (h : x ^ n ∈ A k N (n • 1)) : Away.mk (A k N) hx n (x ^ n) h = 1 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_one]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

theorem away_self_pow' (x : MvPolynomial (Fin (N + 1)) k) (hx : x ∈ A k N 1) {m n : ℕ} (hmn : m = n)
    (h : x ^ n ∈ A k N (m • 1)) : Away.mk (A k N) hx m (x ^ n) h = 1 := by
  subst hmn; exact away_self_pow x hx m h

theorem key {X : Scheme.{0}} [IsIntegral X] (ι : X ⟶ PN (k := k) N) (i : Fin (N + 1))
    (hi : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i)) {n : ℕ}
    (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ A k N n) (hfη : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) f)
    (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ A k N (m • n))
    (hf' : f ∈ A k N (n • 1)) (hg' : g ∈ A k N ((m * n) • 1)) :
    away ι f hf hfη m g hg * away ι (MvPolynomial.X i) (X_mem k N i) hi n f hf' ^ m =
      away ι (MvPolynomial.X i) (X_mem k N i) hi (m * n) g hg' := by
  have hF : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen (A k N) (MvPolynomial.X i * f) := by
    rw [Proj.basicOpen_mul]; exact ⟨hi, hfη⟩
  have e1 : ∀ y, pg ι _ hF (Proj.awayToSection _ (MvPolynomial.X i * f)
      (awayMap (A k N) hf (show MvPolynomial.X i * f = MvPolynomial.X i * f from rfl) y)) =
      pg ι _ hi (Proj.awayToSection _ (MvPolynomial.X i) y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (A k N) hf
      (show MvPolynomial.X i * f = MvPolynomial.X i * f from rfl)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    exact pg_res ι _ hF hi _
  have e2 : ∀ y, pg ι _ hF (Proj.awayToSection _ (MvPolynomial.X i * f)
      (awayMap (A k N) (X_mem k N i) (show MvPolynomial.X i * f = f * MvPolynomial.X i from mul_comm _ _) y)) =
      pg ι _ hfη (Proj.awayToSection _ f y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (A k N) (X_mem k N i)
      (show MvPolynomial.X i * f = f * MvPolynomial.X i from mul_comm _ _)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    erw [this]
    exact pg_res ι _ hF hfη _
  rw [away_eq, away_eq, away_eq, ← e2, ← e1, ← e1, ← map_pow, ← map_mul, ← away_identity _ _ _ _ hf hg hf' hg',
    map_mul, map_pow]
  simp only [map_mul, map_pow]

theorem basicOpen_le (i : Fin (N + 1)) {n : ℕ} (hn : 0 < n) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ A k N n) (hf' : f ∈ A k N (n • 1)) :
    (PN (k := k) N).basicOpen (Proj.awayToSection (A k N) (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')) ≤
      Proj.basicOpen (A k N) f := by
  intro y hy
  have hyU : y ∈ Proj.basicOpen (A k N) (MvPolynomial.X i) := (PN (k := k) N).basicOpen_le _ hy
  let y' : (Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)).toScheme := ⟨y, hyU⟩
  have h1 : y' ∈ (Proj.basicOpen (A k N) (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k)).ι ⁻¹ᵁ
      (PN (k := k) N).basicOpen (Proj.awayToSection (A k N) (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')) := hy
  rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen, ← SpecMap_preimage_basicOpen] at h1
  have ht : Away.isLocalizationElem (X_mem k N i) hf = Away.mk _ (X_mem k N i) n f hf' := by
    apply val_injective; simp [Away.val_mk]
  have h2 : y' ∈ Proj.basicOpenToSpec (A k N) (MvPolynomial.X i) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem k N i) hf) := by
    rw [ht]; exact h1
  rw [← Proj.awayι_preimage_basicOpen (A k N) (X_mem k N i) one_pos hf hn, ← Scheme.Hom.comp_preimage,
    ← Proj.basicOpenIsoSpec_inv_ι _ _ (X_mem k N i) one_pos, ← Proj.basicOpenIsoSpec_hom _ _ (X_mem k N i) one_pos,
    Iso.hom_inv_id_assoc] at h2
  exact h2

theorem GenOfAway_of : GenOfAway := by
  intro k _ X _ p N ι hp i h hE n hn f hf
  have hf' : f ∈ A k N (n • 1) := by simpa using hf
  have hfv : away ι (MvPolynomial.X i) (X_mem k N i) h n f hf' = eval₂ (kHom p) (coordAt ι i h) f := hE n f hf'
  refine ⟨⟨fun hfη => ?_, fun hne => ?_⟩, fun m g hg hfη => ?_⟩
  · have hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n ∈ A k N (1 • n) := by
      simpa using SetLike.pow_mem_graded n (X_mem k N i)
    have hx' : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n ∈ A k N ((1 * n) • 1) := by
      simpa using SetLike.pow_mem_graded n (X_mem k N i)
    have h1 : away ι (MvPolynomial.X i) (X_mem k N i) h (1 * n) _ hx' = 1 := by
      rw [away_eq, away_self_pow' _ _ (one_mul n), map_one, map_one]
    have := key ι i h f hf hfη 1 _ hx hf' hx'
    rw [h1, hfv] at this
    intro h0
    rw [h0] at this
    simp at this
  · have hu : IsUnit (X.presheaf.germ _ (genericPoint X) h
        (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i) (Away.mk _ (X_mem k N i) n f hf')))) := by
      rw [← hfv] at hne; exact isUnit_iff_ne_zero.mpr hne
    rw [← Scheme.mem_basicOpen, ← Scheme.preimage_basicOpen] at hu
    exact basicOpen_le i hn f hf hf' hu
  · have hg' : g ∈ A k N ((m * n) • 1) := by simpa using hg
    have := key ι i h f hf hfη m g hg hf' hg'
    rw [hfv, hE (m * n) g hg'] at this
    exact this

end LateralTheory.EtaleTrace.Cov.GenInPf
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenOutGluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def GenOnAgree : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (U U' : X.Opens) (πU : U.toScheme ⟶ PN k N) (πU' : U'.toScheme ⟶ PN k N),
  GenOn p w U πU → GenOn p w U' πU' → pullback.fst U.ι U'.ι ≫ πU = pullback.snd U.ι U'.ι ≫ πU'

def GenOnGen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (π : X ⟶ PN k N) (U : X.Opens),
  genericPoint X ∈ U → GenOn p w U (U.ι ≫ π) → Gen p π w

theorem GenOutGlue_of (h1 : GenOnAgree) (h2 : GenOnGen) : GenOutGlue := by
  intro k _ X _ p N w hloc
  choose U πU hxU hover hgen using hloc
  have hcov : TopologicalSpace.IsOpenCover U := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact (TopologicalSpace.Opens.mem_iSup).2 ⟨x, hxU x⟩
  let 𝒰 := X.openCoverOfIsOpenCover U hcov
  have hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ πU x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ πU y :=
    fun x y => h1 k p N w (U x) (U y) (πU x) (πU y) (hgen x) (hgen y)
  refine ⟨𝒰.glueMorphisms πU hf, ?_, ?_⟩
  · refine 𝒰.hom_ext _ _ fun x => ?_
    have e : 𝒰.f x ≫ 𝒰.glueMorphisms πU hf = πU x := 𝒰.ι_glueMorphisms πU hf x
    rw [← Category.assoc, e]
    exact hover x
  · have hη := 𝒰.ι_glueMorphisms πU hf (genericPoint X)
    refine h2 k p N w _ (U (genericPoint X)) (hxU _) ?_
    have : (U (genericPoint X)).ι ≫ 𝒰.glueMorphisms πU hf = πU (genericPoint X) := hη
    rw [this]
    exact hgen _

theorem genOnGen : GenOnGen := by
  intro k _ X _ p N w π U hη hG n hn f hf
  obtain ⟨h1, h2⟩ := hG hη n hn f hf
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact Iff.rfl
  · intro m g hg h
    have h' := h2 m g hg h
    have hinj : Function.Injective (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom :=
      haveI : IsIso (U.ι.stalkMap ⟨genericPoint X, hη⟩) :=
        (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
      ((asIso (U.ι.stalkMap ⟨genericPoint X, hη⟩)).commRingCatIsoToRingEquiv).injective
    apply hinj
    refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ?_ (map_pow _ _ _)).trans h')
    rw [Scheme.Hom.comp_app]
    exact (Scheme.Hom.germ_stalkMap_apply U.ι (π ⁻¹ᵁ Proj.basicOpen _ f) ⟨genericPoint X, hη⟩ h
      (π.app _ (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))))

theorem GenOutGlue_of_agree (h1 : GenOnAgree) : GenOutGlue :=
  GenOutGlue_of h1 genOnGen

end LateralTheory.EtaleTrace.Cov
end
end

