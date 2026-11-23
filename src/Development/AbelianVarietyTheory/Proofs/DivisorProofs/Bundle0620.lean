module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolUnifCompLinearEquivExists
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

namespace GlobalTheory.KeyFam

theorem holUnif_transport_linearEquiv : ∀ (h : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L h) (T : (Fin h → ℂ) ≃ₗ[ℂ] (Fin h → ℂ)), ∃ u' : HolUnif A L h, (∀ z, u'.ex z = u.ex (T z)) ∧ ∀ z, z ∈ u'.Λ ↔ T z ∈ u.Λ := by
  intro h A _ L u T
  have hc : Continuous T := T.toContinuousLinearEquiv.continuous
  have hd : Differentiable ℂ T := T.toContinuousLinearEquiv.differentiable
  let Λ' : Submodule ℤ (Fin h → ℂ) := u.Λ.comap ((T.restrictScalars ℤ).toLinearMap)
  have hmem : ∀ z, z ∈ Λ' ↔ T z ∈ u.Λ := fun z => Iff.rfl
  have hdisc : DiscreteTopology Λ' := by
    haveI := u.discrete
    let f : Λ' → u.Λ := fun z => ⟨T z, (hmem z).1 z.2⟩
    have hf : Continuous f := (hc.comp continuous_subtype_val).subtype_mk _
    have hi : Function.Injective f := fun a b hab =>
      Subtype.ext (T.injective (congrArg Subtype.val hab))
    exact DiscreteTopology.of_continuous_injective hf hi
  have hfull : Submodule.span ℝ (Λ' : Set (Fin h → ℂ)) = ⊤ := by
    have h1 : (Λ' : Set (Fin h → ℂ)) = (T.symm.restrictScalars ℝ).toLinearMap '' (u.Λ : Set (Fin h → ℂ)) := by
      ext z
      constructor
      · intro hz
        exact ⟨T z, hz, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        refine (hmem _).2 ?_
        simpa using hw
    rw [h1, ← Submodule.map_span, u.full, Submodule.map_top, LinearMap.range_eq_top]
    exact (T.symm.restrictScalars ℝ).surjective
  refine ⟨{ ex := fun z => u.ex (T z)
            ex_add := fun z w => by rw [map_add (f := _), u.ex_add]
            ex_onto := u.ex_onto.comp T.surjective
            Λ := Λ'
            ker := fun z => u.ker (T z)
            discrete := hdisc
            full := hfull
            hol := fun U f => ⟨(u.hol U f).1.preimage hc,
              (u.hol U f).2.comp hd.differentiableOn (fun _ hz => hz)⟩
            fr := fun i z => u.fr i (T z)
            fr_hol := fun i => (u.fr_hol i).comp hd.differentiableOn (fun _ hz => hz)
            fr_ne := fun i z hz => u.fr_ne i (T z) hz
            fr_compat := fun i j z hz => u.fr_compat i j (T z) hz }, fun _ => rfl, hmem⟩

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfAgreeOnFibreDenseOpenSmooth
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibreDense

theorem alg (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b : B)
    (h : ∀ q : PrimeSpectrum B, q ∈ closure ({P : PrimeSpectrum B | ∃ s ∉ P.asIdeal, s * b = 0} ∩
      PrimeSpectrum.comap (algebraMap A B) ⁻¹' {PrimeSpectrum.comap (algebraMap A B) q})) : b = 0 := by
  by_contra hb
  let I : Ideal B := LinearMap.ker (LinearMap.toSpanSingleton B B b)
  have hI : I ≠ ⊤ := by
    intro h1
    have : (1 : B) ∈ I := h1 ▸ Submodule.mem_top
    simp [I] at this
    exact hb this
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
  let u : PrimeSpectrum B := ⟨m, hm.isPrime⟩
  obtain ⟨g, hg, hgQ⟩ := GlobalTheory.T.exists_annihilator_not_mem_minimalPrimes_le A B b h u
  have h0 := _root_.GlobalTheory.NzdDescent.of_noetherian _root_.GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero A B b g u hg hgQ
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).1 h0
  exact s.2 (hle (by simpa [I] using hs))

theorem dense (X T : Scheme.{0}) (p : X ⟶ T) [Smooth p] (W : X.Opens)
    (hW : ∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) : IsSchemeTheoreticallyDominant W.ι := by
  refine GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective X T p W fun U V hU hV e b hb => ?_
  letI := (p.appLE V U e).hom.toAlgebra
  haveI : Algebra.Smooth Γ(T, V) Γ(X, U) := HasRingHomProperty.appLE @Smooth p ‹_› ⟨V, hV⟩ ⟨U, hU⟩ e
  exact alg Γ(T, V) Γ(X, U) b (_root_.GlobalTheory.fibre_dense_affine_chart_primes X T p W U V hU hV e hW b hb)

theorem ext_of_dominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (d ≫ f ≫ s)
  let d' : U' ⟶ X' := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem main : ∀ (X T Y : Scheme.{0}) (p : X ⟶ T) [Smooth p] (q : Y ⟶ T) [IsSeparated q] (W : X.Opens),
    (∀ x : X, x ∈ closure ((W : Set X) ∩ p ⁻¹' {p x})) →
    ∀ f g : X ⟶ Y, f ≫ q = g ≫ q → W.ι ≫ f = W.ι ≫ g → f = g := by
  intro X T Y p _ q _ W hW f g hfg hfgW
  haveI := dense X T p W hW
  exact ext_of_dominant q hfg W.ι hfgW

end GlobalTheory.FibreDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationCoeffEqZeroOfDegreeLt
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory

theorem invDer_coeff_eq_zero_of_degree_lt :
    ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
      (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R) (r : ℕ),
      (∀ α : Fin d →₀ ℕ, α.degree < r + 1 → coeff α F = 0) →
      ∀ α : Fin d →₀ ℕ, α.degree < r → coeff α (invDer μ u F) = 0 := by
  intro R _ d μ hμ u F r hF α hα
  unfold invDer
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul]
  unfold atZero
  rw [(coeff_subst_restrict_sum (pderiv (R := R) (Sum.inr i) (subst μ F))).1 α, coeff_pderiv]
  have h := coeff_subst_eq_zero_of_degree_lt R (Fin d) (Fin d ⊕ Fin d) μ F (r + 1) hμ hF
    (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) (by
      rw [map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single]; omega)
  rw [h, zero_mul, smul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteSpanNatCast
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.FinProjComplete

theorem mem_span_pow_smul_top_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x : M) :
    x ∈ (Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M) ↔ ∃ m : M, x = (p ^ n : ℕ) • m := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, Submodule.mem_top, by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]⟩

theorem smodEq_iff (p : ℕ) {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M))] ↔
      ∃ m : M, x - y = (p ^ n : ℕ) • m := by
  rw [SModEq.sub_mem, mem_span_pow_smul_top_iff]

end GlobalTheory.FinProjComplete

open GlobalTheory.FinProjComplete in
theorem GlobalTheory.FinProjComplete.isAdicComplete_span_natCast : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  intro p O A _ _ _ _ _ hO
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' O A
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π (LinearMap.id) hπ
  have hπs : ∀ a, π (s a) = a := fun a => by simpa using LinearMap.congr_fun hs a
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hc : ∀ i, s x i = 0 := by
      intro i
      apply hO.toIsHausdorff.haus'
      intro n
      obtain ⟨m, hm⟩ := (smodEq_iff p n x 0).1 (hx n)
      rw [smodEq_iff]
      refine ⟨s m i, ?_⟩
      rw [sub_zero] at hm ⊢
      rw [hm, map_nsmul, Pi.smul_apply]
    have : s x = 0 := funext hc
    rw [← hπs x, this, map_zero]
  · intro f hf
    have hcoord : ∀ i, ∃ L : O, ∀ n, s (f n) i ≡ L [SMOD ((Ideal.span {(p : O)}) ^ n • (⊤ : Submodule O O))] := by
      intro i
      apply hO.toIsPrecomplete.prec'
      intro m n hmn
      obtain ⟨c, hc⟩ := (smodEq_iff p m (f m) (f n)).1 (hf hmn)
      rw [smodEq_iff]
      refine ⟨s c i, ?_⟩
      rw [← Pi.sub_apply, ← map_sub, hc, map_nsmul, Pi.smul_apply]
    choose L hL using hcoord
    refine ⟨π L, fun n => ?_⟩
    have hd : ∀ i, ∃ c : O, s (f n) i - L i = (p ^ n : ℕ) • c := fun i => (smodEq_iff p n _ _).1 (hL i n)
    choose c hc using hd
    rw [smodEq_iff]
    refine ⟨π c, ?_⟩
    have hv : s (f n) - L = (p ^ n : ℕ) • c := funext fun i => by simpa using hc i
    rw [← map_nsmul, ← hv, map_sub, hπs]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevExistsPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

def secPush (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) : Over.mk (T.hom ≫ f) ⟶ o.A :=
  Over.homMk (u.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; rfl)

theorem secPush_left (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) :
    (secPush m T u).left = u.left ≫ m.φ := rfl

theorem secPush_inj (m : ObjMap o' o f) (T : Over S') {u v : T ⟶ o'.A}
    (h : secPush m T u = secPush m T v) : u = v := by
  have h' := congrArg CommaMorphism.left h
  exact Over.OverMorphism.ext (m.cart.1.hom_ext h' (by rw [Over.w, Over.w]))

theorem secPush_mul (m : ObjMap o' o f) (T : Over S') (u v : T ⟶ o'.A) :
    secPush m T (u * v) = secPush m T u * secPush m T v := by
  apply Over.OverMorphism.ext
  rw [secPush_left]
  exact (m.cart.2 T u v (secPush m T u) (secPush m T v) rfl rfl).symm

theorem secPush_one (m : ObjMap o' o f) (T : Over S') :
    secPush m T 1 = 1 := by
  have h := secPush_mul m T 1 1
  rw [_root_.mul_one] at h
  exact (_root_.mul_eq_left.mp h.symm)

theorem secPush_act (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) (c : D.O) :
    secPush m T (u ≫ o'.act.act c) = secPush m T u ≫ o.act.act c := by
  apply Over.OverMorphism.ext
  simp only [secPush_left, Over.comp_left, Category.assoc, m.act]

theorem isEtLev_exists_pull : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S} (m : ObjMap o' o f) {w0 : Ideal (𝓞 D.F)} {r : ℕ} {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}, IsEtLev o w0 r lv → ∃ lv' : D.La → (𝟙_ (Over S') ⟶ o'.A), IsEtLev o' w0 r lv' ∧ ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := by
  intro p _ D R _ b N S S' s s' o o' f m w0 r lv hlv
  have hu : ∀ {X : Scheme.{0}} (T : Over X), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have wα : ∀ y, (f ≫ (lv y).left) ≫ o.A.hom = 𝟙 S' ≫ f := fun y => by
    rw [Category.assoc, Over.w]; simp
  let lv' : D.La → (𝟙_ (Over S') ⟶ o'.A) := fun y =>
    Over.homMk (m.cart.1.lift (f ≫ (lv y).left) (𝟙 S') (wα y)) (m.cart.1.lift_snd _ _ _)
  have hα : ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := fun y => m.cart.1.lift_fst _ _ _
  have hP1 : ∀ y, secPush m (𝟙_ (Over S')) (lv' y) =
      toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ lv y := fun y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, hα, Over.comp_left, hu]; simp
  have hP : ∀ (T : Over S') y, secPush m T (toUnit T ≫ lv' y) =
      toUnit (Over.mk (T.hom ≫ f)) ≫ lv y := fun T y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, Over.comp_left, Category.assoc, hα, Over.comp_left, hu, hu]; simp
  refine ⟨lv', ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x' => ?_⟩, hα⟩
  · apply secPush_inj m
    rw [secPush_mul, hP1, hP1, hP1, hlv.1, MonObj.comp_mul]
  · apply secPush_inj m
    rw [secPush_act, hP1, hP1, hlv.2.1, Category.assoc]
  · apply secPush_inj m
    rw [hP1, secPush_one, hlv.2.2.1 x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hlv.2.2.2 k (x' ≫ f)
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h := congrArg (secPush m (Over.mk x')) hy
      rw [hP, secPush_one] at h
      exact h
    · obtain ⟨y, hy⟩ := hsurj (secPush m (Over.mk x') g) (fun c hc => by
        rw [← secPush_act, hg c hc, secPush_one])
      refine ⟨y, secPush_inj m _ ?_⟩
      rw [hP]
      exact hy

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
section
noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def IsEtLevOver {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) ∧
    (∀ x ∈ wSub D w0 r, l x = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
      ∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
        ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = g

def ptOf {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {T : Scheme.{0}} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s}
    {o₁ : Obj b N s₁} (m : ObjMap o₁ o t) (l : 𝟙_ (Over T) ⟶ o₁.A) : Over.mk t ⟶ o.A :=
  Over.homMk (l.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w l]
    exact Category.id_comp t)

def levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) : D.La :=
  Function.surjInv (Submodule.mkQ_surjective (wSub D w0 r)) (g ((wSub D w0 r).mkQ y))

theorem mkQ_levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) :
    (wSub D w0 r).mkQ (levAct g y) = g ((wSub D w0 r).mkQ y) :=
  Function.surjInv_eq _ _

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullSymplecticLevelStructureUniqueOfLevelsStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop},
    (∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c') →
    ∀ {z : kˣ}, IsPrimitiveRoot z l.M' → ∀ {etaA eta ev ev' : D.La → Q},
    IsSympLevel D act e l.M' z ev → Induces l etaA eta ev →
    IsSympLevel D act e l.M' z ev' → Induces l etaA eta ev' → ev = ev' := by
  first | exact @GlobalTheory.FullLevel.isSympLevel_unique | exact GlobalTheory.FullLevel.isSympLevel_unique | (intros; apply GlobalTheory.FullLevel.isSympLevel_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplier
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.LatTorsVal

theorem exists_tors {L : PeriodPair} {c : ℂ} {τ : ℍ} (hτ : IsTauOf L c τ) (M : ℕ) [NeZero M] (P : ℂ)
    (hP : (M : ℂ) * P ∈ L.lattice) :
    ∃ x : Fin 2 → ZMod M, P - c * tors M τ x ∈ L.lattice ∧ (P ∉ L.lattice → x ≠ 0) := by
  have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf L c τ hτ
  have tm := GlobalTheory.WpFam.TorsMem.main M τ
  have hc : c ≠ 0 := hτ.1
  have hPz : P = c * (P / c) := by field_simp
  have hMz : (M : ℂ) * (P / c) ∈ (tauPair τ).lattice := by
    rw [← hom.1]
    have : c * ((M : ℂ) * (P / c)) = (M : ℂ) * P := by rw [hPz]; field_simp
    rw [this]; exact hP
  obtain ⟨x, hx⟩ := tm.2.2.2.2 (P / c) hMz
  refine ⟨x, ?_, ?_⟩
  · have := (hom.1 _).2 hx
    rwa [mul_sub, ← hPz] at this
  · rintro hPL rfl
    apply hPL
    have h0 := (tm.2.2.1 0).2 rfl
    have : P / c ∈ (tauPair τ).lattice := by
      have := add_mem hx h0
      simpa using this
    rw [hPz]; exact (hom.1 _).2 this

theorem wp_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (M : ℕ) (P : ℂ) (x : Fin 2 → ZMod M)
    (h : P - c * tors M τ x ∈ L.lattice) :
    L.weierstrassP P = L.weierstrassP (c * tors M τ x) ∧
      L.derivWeierstrassP P = L.derivWeierstrassP (c * tors M τ x) := by
  have e : P = c * tors M τ x + ((⟨P - c * tors M τ x, h⟩ : L.lattice) : ℂ) := by simp
  constructor
  · rw [e, L.weierstrassP_add_coe]
  · rw [e, L.derivWeierstrassP_add_coe]

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  intro L β Ω M hβ hβi hΩ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hj := _root_.GlobalTheory.JInt.main L c τ β hτ hβ hβi
  have hω := (GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD L c τ hτ).2 Ω hΩ
  have st := (_root_.GlobalTheory.WpFam.TauVal.main L c Ω τ hτ).2 M
  refine ⟨fun P hP => ?_, fun P Q hP hQ hMP hMQ => ?_⟩
  · obtain ⟨x, hx, -⟩ := exists_tors hτ M P hP
    obtain ⟨e1, e2⟩ := wp_eq M P x hx
    have hv := _root_.GlobalTheory.WpInt.main M τ _ hj hω x
    rw [e1, e2, mul_div_assoc, mul_div_assoc, ← (st x).1, ← (st x).2, ← mul_div_assoc, ← mul_div_assoc]
    exact hv
  · obtain ⟨x, hx, hx0⟩ := exists_tors hτ M P hMP
    obtain ⟨y, hy, hy0⟩ := exists_tors hτ M Q hMQ
    have hv := _root_.GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div M τ _ hj hω x y (hx0 hP) (hy0 hQ)
    rw [(wp_eq M P x hx).1, (wp_eq M Q y hy).1, mul_div_assoc, sub_div, ← (st x).1, ← (st y).1, ← sub_div,
      ← mul_div_assoc]
    exact hv

end GlobalTheory.WpFam.LatTorsVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentBlockFrobeniusXiAinfOfFrameBlockP
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem isNil_V_blk_frob_xi :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hUV hnil
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  apply isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a
  refine isNil_of_theta_eq p F.θ F.σ (Fact.out) F.σ_pow _ _ ?_ hnil
  intro i j
  have hU : F.θ (U i j) = F.θ (F.a (V i j)) := by
    obtain ⟨c, hc⟩ := hUV i j
    have h := congrArg F.θ hc
    rw [map_sub, map_mul, theta_tau F hv hε, zero_mul, sub_eq_zero] at h
    exact h
  simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
  rcases j with j | j
  · simp only [Sum.elim_inl, map_mul, map_natCast, hU, F.θ_a, theta_frob_xi hv hε]
  · simp only [Sum.elim_inr, map_mul, map_one, mul_one, hU]

end GlobalTheory.WinLift
end
end

