module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsBasisSpanEqTop
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem span_gen_eq_top (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (functor A B r).obj (op Z))
    (W : Z.affineOpens) :
    Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)) = ⊤ := by
  have sq : IsPullback (pullback.fst (str A B) y.1) (pullback.snd (str A B) y.1) (str A B) y.1 :=
    IsPullback.of_hasPullback _ _
  haveI : IsAffineHom (pullback.snd (str A B) y.1) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback sq inferInstance
  have hpo := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) W.2
    (by simp) (by simp)
  have hQ : IsAffineOpen (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage _
  have hsurj := y.2.1.subschemeι_app_surjective ⟨_, hQ⟩
  let R := Γ(Spec (CommRingCat.of A), ⊤)
  let S := Γ(Spec (CommRingCat.of B), ⊤)
  let T := Γ(Z, (W : Z.Opens))
  let Q := Γ(pullback (str A B) y.1, pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))
  letI : Algebra R S := (show R ⟶ S from (str A B).app ⊤).hom.toAlgebra
  letI : Algebra R T := (y.1.appLE ⊤ W (by simp)).hom.toAlgebra
  letI : Algebra T Q := ((pullback.snd (str A B) y.1).app W).hom.toAlgebra
  letI : Algebra S Q :=
    (show S ⟶ Q from (pullback.fst (str A B) y.1).appLE (str A B ⁻¹ᵁ ⊤) _ (by simp)).hom.toAlgebra
  letI : Algebra R Q :=
    ((y.1.appLE ⊤ W (by simp)) ≫ (pullback.snd (str A B) y.1).app W).hom.toAlgebra
  haveI : IsScalarTower R T Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq (fun x => by
    have h := congr($(hpo.w).hom x)
    exact h.symm)
  haveI : Algebra.IsPushout R T S Q := (CommRingCat.isPushout_iff_isPushout).mp hpo.flip
  have hbc := Algebra.IsPushout.out (R := R) (S := T) (R' := S) (S' := Q)

  have key : ∀ s : S, (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom
      (algebraMap S Q s) = ((y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤
        (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp)).hom s := by
    intro s
    have h : (Scheme.Hom.appLE (pullback.fst (str A B) y.fst) (str A B ⁻¹ᵁ ⊤)
      (pullback.snd (str A B) y.fst ⁻¹ᵁ ↑W) (by simp)) ≫ y.2.1.subschemeι.app _ =
        (y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤
        (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    exact congrArg (fun f => (CommRingCat.Hom.hom f) s) h
  have hι : ∀ (t : T) (n : Q), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (t • n) =
      t • (show Sec A B y W from
        (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom n) := by
    intro t n
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
  have term : ∀ (c : A) (j : Fin N), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (algebraMap S Q
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c * e j))) =
      (algebraMap R T ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c)) • gen A B y W (e j) := by
    intro c j
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c) =
        algebraMap R S ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c) :=
      congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))).hom c)
    rw [map_mul, h1, map_mul, ← IsScalarTower.algebraMap_apply R S Q,
      IsScalarTower.algebraMap_apply R T Q, ← Algebra.smul_def, hι, key]
    rfl
  have hB : ∀ b : B, (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (algebraMap S Q ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b))) ∈
      Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)) := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr b, map_sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def, term]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨q, rfl⟩ := hsurj x
  refine hbc.inductionOn q (motive := fun q => (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom q) ∈ Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)))
    ?_ ?_ ?_
  · intro s
    obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b = s :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s, by simp⟩
    exact hB b
  · intro t n hn
    rw [hι]
    exact Submodule.smul_mem _ _ hn
  · intro a b ha hb
    rw [map_add (f := _)]
    exact add_mem ha hb

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsRankAtStalk
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

theorem isPullback_fromSpec_app_rank {X Y : Scheme.{0}} (π : X ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsPullback hV.fromSpec (Spec.map (π.app W)) π hW.fromSpec :=
  (IsOpenImmersion.isPullback _ _ _ _ (by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV]) (by simp)).flip

theorem rankAtStalk_sec (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)) (W : Z.affineOpens)
    (P : PrimeSpectrum Γ(Z, W)) : Module.rankAtStalk (Sec A B y W) P = r := by
  obtain ⟨_hfin, _hflat, h3⟩ := y.2.2
  have hW : IsAffineOpen (W : Z.Opens) := W.2
  have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := hW.preimage _
  haveI : Module.Finite Γ(Z, W) (Sec A B y W) := by
    have := IsFinite.finite_app (subStr A B y) (W : Z.Opens) hW
    exact this
  haveI : Module.Flat Γ(Z, W) (Sec A B y W) := by
    have := Scheme.Hom.flat_appLE (subStr A B y) hW hV le_rfl
    rw [Scheme.Hom.appLE_eq_app] at this
    exact this
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_fromSpec_app_rank (subStr A B y) hW hV) P
  rw [h3] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertTensorToSubschemeSectionsSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

namespace GlobalTheory.HilbAff

theorem kappa_surjective (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}}
    (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (str A B) g).IdealSheafData)
    (U : T.affineOpens) : Function.Surjective (kappa A B g I U) := by
  letI := (secAlg A g U).toAlgebra
  let W : (pullback (str A B) g).Opens := pullback.snd (str A B) g ⁻¹ᵁ (U : T.Opens)
  haveI : IsAffineHom (pullback.snd (str A B) g) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (str A B) g) inferInstance
  have hW : IsAffineOpen W := U.2.preimage _
  have H := IsPullback.of_hasPullback (str A B) g
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := (U : T.Opens)) (UX := ⊤) (UY := W)
    le_top le_top (by simp [W])).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) U.2 (isAffineOpen_top _))
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have hle : (⊤ : Subring Γ(pullback (str A B) g, W)) ≤
      (kappa A B g I U).range.comap (I.subschemeι.app W).hom := by
    rw [← hgen, Subring.closure_le]
    rintro _ (⟨z, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1 ⊗ₜ (Scheme.ΓSpecIso (CommRingCat.of B)).hom z, ?_⟩
      rw [kappa_tmul]
      simp only [map_one, one_mul, Iso.hom_inv_id_apply]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
      rfl
    · refine ⟨c ⊗ₜ 1, ?_⟩
      rw [kappa_tmul]
      simp only [map_one, mul_one]
      rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE]
      rfl
  intro y
  obtain ⟨x, hx⟩ := I.subschemeι_app_surjective ⟨W, hW⟩ y
  obtain ⟨w, hw⟩ := hle (Subring.mem_top x)
  exact ⟨w, hw.trans hx⟩

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPropertyOfLeKerApp
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed

namespace GlobalTheory.PtClosed

theorem of_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ (V : S.Opens) (hV : IsAffineOpen V), Represents (ptQ P V hV) (killIdeal (ptQ P V hV))) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S),
    (∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom) → P R' x := by
  intro S P hloc hrep R' _ x hx
  have key : ∀ (V : S.Opens) (hV : IsAffineOpen V) (r : R'),
      (∀ q : PrimeSpectrum R', r ∉ q.asIdeal → x.base q ∈ V) →
      P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x) := by
    intro V hV r hsub
    have e : (⊤ : (Sp (Localization.Away r)).Opens) ≤
        (spMap (algebraMap R' (Localization.Away r)) ≫ x) ⁻¹ᵁ V := by
      intro q _
      show x.base ((spMap (algebraMap R' (Localization.Away r))).base q) ∈ V
      apply hsub
      intro h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit r))
    let g' : Γ(S, V) ⟶ CommRingCat.of (Localization.Away r) :=
      (spMap (algebraMap R' (Localization.Away r)) ≫ x).appLE V ⊤ e ≫ (Scheme.ΓSpecIso _).hom
    have hy : spMap (algebraMap R' (Localization.Away r)) ≫ x = spMap g'.hom ≫ hV.fromSpec := by
      have h1 := IsAffineOpen.SpecMap_appLE_fromSpec (spMap (algebraMap R' (Localization.Away r)) ≫ x) hV
        (isAffineOpen_top (Sp (Localization.Away r))) e
      rw [IsAffineOpen.fromSpec_top] at h1
      rw [(Iso.inv_comp_eq _).1 h1.symm, Scheme.isoSpec_Spec_hom]
      simp only [spMap, CommRingCat.ofHom_hom, g', Spec.map_comp, Category.assoc]
    have hker : killIdeal (ptQ P V hV) ≤ RingHom.ker g'.hom := by
      refine (hx V hV).trans ?_
      intro a ha
      rw [RingHom.mem_ker] at ha ⊢
      have hg : g' = x.app V ≫ ((spMap (algebraMap R' (Localization.Away r))).appLE (x ⁻¹ᵁ V) ⊤ e ≫
          (Scheme.ΓSpecIso _).hom) := by
        simp only [g', Scheme.Hom.comp_appLE, Category.assoc]
      rw [hg, CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]
    have := (hrep V hV (Localization.Away r) g'.hom).2 hker
    rw [hy]
    exact this
  let G : Set R' := {r | ∃ V : S.Opens, IsAffineOpen V ∧ ∀ q : PrimeSpectrum R', r ∉ q.asIdeal → x.base q ∈ V}
  have hG : Ideal.span G = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : PrimeSpectrum R' := ⟨m, hm.isPrime⟩
    obtain ⟨V, hV, hpV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 S.isBasis_affineOpens)
      (show x.base p ∈ (⊤ : S.Opens) from trivial)
    have hpV' : p ∈ (x ⁻¹ᵁ V : TopologicalSpace.Opens (PrimeSpectrum R')) := hpV
    obtain ⟨W, ⟨r, rfl⟩, hpW, hW⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (PrimeSpectrum.isBasis_basic_opens (R := R'))) hpV'
    have hr : r ∈ G := ⟨V, hV, fun q hq => hW (show q ∈ PrimeSpectrum.basicOpen r from hq)⟩
    exact hpW (hle (Ideal.subset_span hr))
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite G).1 hG
  refine hloc R' x t hspan fun r hr => ?_
  obtain ⟨V, hV, hsub⟩ := ht hr
  exact key V hV r hsub

end GlobalTheory.PtClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomQuotientSpanPowEqOfEtaleLow
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem algHom_quot_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  intro A R C _ _ _ _ _ _ ρ hρ t hker ht hE n f f' hff
  set P₀ : Ideal R := RingHom.ker ρ with hP₀
  haveI hP : P₀.IsPrime := RingHom.ker_isPrime ρ
  have hρa : ∀ a : A, ρ (algebraMap A R a) = a := fun a => by
    have := congrArg (fun g => g a) hρ
    simpa using this
  have hcomap : P₀.comap (algebraMap A R) = ⊥ := by
    ext a
    simp only [Ideal.mem_comap, hP₀, RingHom.mem_ker, Ideal.mem_bot, hρa]
  have hht : (P₀.comap (algebraMap A R)).height ≤ 1 := by
    rw [hcomap, Ideal.height_bot]; exact zero_le_one
  set Rp := Localization.AtPrime P₀
  haveI : Algebra.Etale Rp (Rp ⊗[R] C) := hE P₀ hht
  haveI : Algebra.FormallyUnramified R Rp := Algebra.FormallyUnramified.of_isLocalization P₀.primeCompl
  haveI : Algebra.FormallyUnramified R (Rp ⊗[R] C) := Algebra.FormallyUnramified.comp R Rp (Rp ⊗[R] C)
  set Q := R ⧸ Ideal.span {t} ^ n
  set B := Localization (Algebra.algebraMapSubmonoid Q P₀.primeCompl)
  letI : Algebra Rp B := localizationAlgebra P₀.primeCompl Q

  have hle : Algebra.algebraMapSubmonoid Q P₀.primeCompl ≤ nonZeroDivisors Q := by
    rintro _ ⟨s, hs, rfl⟩
    suffices H : ∀ x : Q, x * algebraMap R Q s = 0 → x = 0 from
      mem_nonZeroDivisors_iff.2 ⟨fun x hx => H x (by rw [mul_comm]; exact hx), H⟩
    intro x hx
    set a := ρ s
    have ha : a ≠ 0 := fun h => hs (RingHom.mem_ker.2 h)
    have hd : s - algebraMap A R a ∈ Ideal.span {t} := by
      rw [← hker, RingHom.mem_ker, map_sub, hρa, sub_self]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hd
    set u : Q := Ideal.Quotient.mk _ s
    set e : Q := Ideal.Quotient.mk _ (s - algebraMap A R a)
    have he : e ^ n = 0 := by
      simp only [e, ← map_pow, ← hr, mul_pow]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n)
    have hdv : u ∣ (u - e) ^ n := by
      have h1 := sub_dvd_pow_sub_pow (u - e) (-e) n
      rw [neg_pow, he, mul_zero, sub_zero, sub_neg_eq_add, sub_add_cancel] at h1
      exact h1
    obtain ⟨k, hk⟩ := hdv
    have hue : u - e = Ideal.Quotient.mk _ (algebraMap A R a) := by
      simp only [u, e, map_sub, sub_sub_cancel]
    have hzero : algebraMap A R (a ^ n) • x = 0 := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_pow, map_pow, ← hue, hk]
      calc u * k * x = k * (x * u) := by ring
        _ = 0 := by rw [show x * u = 0 from hx, mul_zero]
    exact torsionFree_quot A R ρ hρ t hker ht n (a ^ n) (pow_ne_zero n ha) x hzero
  have hinj : Function.Injective (algebraMap Q B) := IsLocalization.injective B hle
  let φ : Rp →ₐ[R] B := (Algebra.ofId Rp B).restrictScalars R
  let ι : Q →ₐ[R] B := IsScalarTower.toAlgHom R Q B
  let g₁ : Rp ⊗[R] C →ₐ[R] B := Algebra.TensorProduct.productMap φ (ι.comp f)
  let g₂ : Rp ⊗[R] C →ₐ[R] B := Algebra.TensorProduct.productMap φ (ι.comp f')
  set J : Ideal B := Ideal.span {algebraMap R B t}
  have hJ : IsNilpotent J := by
    refine ⟨n, ?_⟩
    rw [Ideal.span_singleton_pow (algebraMap R B t) n, ← map_pow, IsScalarTower.algebraMap_apply R Q B,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self t) n), map_zero, Ideal.zero_eq_bot,
      Ideal.span_singleton_eq_bot]
  have e : (Ideal.Quotient.mkₐ R J).comp g₁ = (Ideal.Quotient.mkₐ R J).comp g₂ := by
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext; intro x; simp [g₁, g₂]
    · ext c
      simp only [g₁, g₂, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.productMap_apply_tmul,
        map_one, one_mul, Ideal.Quotient.mkₐ_eq_mk]
      rw [Ideal.Quotient.eq, ← map_sub]
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (hff c)
      rw [← hq, map_mul]
      refine Ideal.mul_mem_left _ _ ?_
      rw [show ι (Ideal.Quotient.mk _ t) = algebraMap R B t from
        (IsScalarTower.algebraMap_apply R Q B t).symm]
      exact Ideal.mem_span_singleton_self _
  have hg : g₁ = g₂ := Algebra.FormallyUnramified.ext J hJ fun x => by
    simpa using congrArg (fun g => g x) e
  ext c
  apply hinj
  have := congrArg (fun g => g ((1 : Rp) ⊗ₜ[R] c)) hg
  simpa [g₁, g₂, ι] using this

end GlobalTheory.GoodEtaleSection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaKernelDerivativeVanishes
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.RegNorm

theorem geom_mul (q m l : ℕ) (hq : 0 < q) :
    (q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) = (q ^ l) ^ m - 1 := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have h2 : 1 ≤ (q ^ l) ^ m := Nat.one_le_pow _ _ (pow_pos hq _)
  have hZ : (((q ^ m : ℕ) : ℤ) - 1) * ∑ i ∈ Finset.range l, ((q ^ m : ℕ) : ℤ) ^ i
      = ((q ^ m : ℕ) : ℤ) ^ l - 1 := mul_geom_sum _ _
  have : (((q ^ m - 1) * ∑ i ∈ Finset.range l, q ^ (m * i) : ℕ) : ℤ) = (((q ^ l) ^ m - 1 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    simp only [pow_mul] at *
    push_cast at hZ
    rw [hZ, ← pow_mul, ← pow_mul, mul_comm m l]
  exact_mod_cast this

theorem pow_modEq_pow_mod (q m x : ℕ) (hq : 1 ≤ q) :
    q ^ x ≡ q ^ (x % m) [MOD q ^ m - 1] := by
  have h1 : 1 ≤ q ^ m := Nat.one_le_pow _ _ hq
  have hm : q ^ m ≡ 1 [MOD q ^ m - 1] := Nat.modEq_sub h1
  calc q ^ x = (q ^ m) ^ (x / m) * q ^ (x % m) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (x / m) * q ^ (x % m) [MOD q ^ m - 1] := (hm.pow _).mul_right _
    _ = q ^ (x % m) := by simp

end GlobalTheory.Shin.RegNorm

namespace GlobalTheory.Shin.RegNorm

theorem lift_iff (q m l k x y : ℕ) (hq : 0 < q) (hl : 0 < l) :
    (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * x ≡ (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * y
      [MOD (q ^ l) ^ m - 1] ↔ k * x ≡ k * y [MOD q ^ m - 1] := by
  set S := ∑ i ∈ Finset.range l, q ^ (m * i) with hSdef
  have hS : S ≠ 0 := by
    have : 0 < S := Finset.sum_pos (fun i _ => pow_pos hq _) ⟨0, by simp [hl]⟩
    omega
  rw [← geom_mul q m l hq, ← hSdef]
  have e1 : k * S * x = k * x * S := by ring
  have e2 : k * S * y = k * y * S := by ring
  rw [e1, e2]
  exact ⟨Nat.ModEq.mul_right_cancel' hS, Nat.ModEq.mul_right' S⟩

end GlobalTheory.Shin.RegNorm

namespace GlobalTheory.Shin

theorem reg_norm_frob : ∀ q l m k : ℕ, 2 ≤ q → l.Prime → 0 < m → ¬ l ∣ m → Reg q m k →
    Reg (q ^ l) m (k * ∑ i ∈ Finset.range l, q ^ (m * i)) ∧
      ∃ a, (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * q ≡
        (k * ∑ i ∈ Finset.range l, q ^ (m * i)) * (q ^ l) ^ a [MOD (q ^ l) ^ m - 1] := by
  intro q l m k hq hl hm hlm hreg
  have hq0 : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hlm
  refine ⟨?_, ?_⟩
  · intro i hi0 him h
    have h' : (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * (q ^ l) ^ i ≡
        (k * ∑ j ∈ Finset.range l, q ^ (m * j)) * 1 [MOD (q ^ l) ^ m - 1] := by
      simpa using h
    have h2 := (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).1 h'
    rw [← pow_mul, mul_one] at h2
    have h3 : k * q ^ (l * i % m) ≡ k [MOD q ^ m - 1] :=
      ((RegNorm.pow_modEq_pow_mod q m (l * i) hq1).mul_left k).symm.trans h2
    refine hreg (l * i % m) ?_ (Nat.mod_lt _ hm) h3
    rcases Nat.eq_zero_or_pos (l * i % m) with h0 | h0
    · exfalso
      have hd : m ∣ l * i := Nat.dvd_of_mod_eq_zero h0
      have : m ∣ i := hcop.symm.dvd_of_dvd_mul_left hd
      exact absurd (Nat.le_of_dvd hi0 this) (by omega)
    · exact h0
  · have ha : ∃ a, l * a % m = 1 % m := by
      rcases Nat.lt_or_ge 1 m with h1 | h1
      · obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
        exact ⟨a, by rw [ha, Nat.mod_eq_of_lt h1]⟩
      · have : m = 1 := by omega
        subst this
        exact ⟨0, by simp⟩
    obtain ⟨a, ha⟩ := ha
    refine ⟨a, (RegNorm.lift_iff q m l k _ _ hq0 hl.pos).2 ?_⟩
    rw [← pow_mul]
    have e1 : q ^ 1 ≡ q ^ (1 % m) [MOD q ^ m - 1] := RegNorm.pow_modEq_pow_mod q m 1 hq1
    have e2 : q ^ (l * a) ≡ q ^ (l * a % m) [MOD q ^ m - 1] := RegNorm.pow_modEq_pow_mod q m (l * a) hq1
    rw [ha] at e2
    rw [pow_one] at e1
    exact (e1.trans e2.symm).mul_left k

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveBaseChangeResidueFieldOfFiniteEtale
section
open IsLocalRing

namespace GlobalTheory

theorem bijective_baseChange_residueField_of_finiteEtale :
    ∀ (R A B : Type) [CommRing R] [HenselianLocalRing R] [CommRing A] [CommRing B] [Algebra R A]
      [Algebra R B] [Algebra.Etale R A] [Module.Finite R A] [Algebra.Etale R B]
      [Module.Finite R B],
      Function.Bijective (fun φ : A →ₐ[R] B =>
        Algebra.TensorProduct.map (AlgHom.id (ResidueField R) (ResidueField R)) φ) :=
  fun R A B _ _ _ _ _ _ _ _ _ _ => bijective_baseChange_residueField_of_etale R A B

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardBlockParabolicSubgroupGLStatement
section
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_blockParabolicSubgroupGL : ∀ (R : Type) [CommRing R] [Finite R] (a d : ℕ), a ≤ d →
    Nat.card (blockPar R a d) = Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  first | exact @GlobalTheory.StdLoc.card_blockPar | exact GlobalTheory.StdLoc.card_blockPar | (intros; apply GlobalTheory.StdLoc.card_blockPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGeneratorStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ f ∈ V, rd f ∈ R) → (∀ f ∈ V', rd f ∈ R) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h h' : B, h ∈ R → h' ∈ R → h * h' = 1 → (∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A))) → ∀ T : V →ₗ[K] V', T ≠ 0 → (∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  first | exact @GlobalTheory.commuting_multiplier_eq_const_smul_generator | exact GlobalTheory.commuting_multiplier_eq_const_smul_generator | (intros; apply GlobalTheory.commuting_multiplier_eq_const_smul_generator <;> assumption)
end

