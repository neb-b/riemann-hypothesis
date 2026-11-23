module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.MultInt

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem pow_left_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {T : Over S'} {T₀ : Over S}
    (h : T.left ⟶ T₀.left) (hh : h ≫ T₀.hom = T.hom ≫ f) (x : T ⟶ (Over.pullback f).obj G) (x₀ : T₀ ⟶ G)
    (hx : h ≫ x₀.left = x.left ≫ pullback.fst G.hom f) (k : ℕ) :
    h ≫ (x₀ ^ k).left = (x ^ k).left ≫ pullback.fst G.hom f := by
  let h' : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk h hh
  have e : TorsionLift.ptsEquiv f G T _ rfl x = h' ≫ x₀ :=
    Over.OverMorphism.ext ((TorsionLift.ptsEquiv_left f G T _ rfl x).trans hx.symm)
  rw [← TorsionLift.ptsEquiv_left f G T _ rfl, map_pow, e, ← comp_pow]
  rfl

theorem exists_finite_factor {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] {X : Scheme.{0}} (s : X ⟶ Sp V)
    [LocallyOfFiniteType s] (φ : V →+* PadicAlgCl p) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K₀] (hφ : ∀ v, φ v ∈ K₀) (x : Sp (PadicAlgCl p) ⟶ X) (hx : x ≫ s = spMap φ) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K ∧ FiniteDimensional ℚ_[p] K ∧
      ∃ x' : Sp K ⟶ X, spMap K.val.toRingHom ≫ x' = x := by
  obtain ⟨U, hU, ψ', hψ'⟩ := exists_affineOpen_factor_of_isLocalRing x
  let A : Type := Γ(X, U)
  let i : Sp A ⟶ X := hU.fromSpec
  haveI : IsOpenImmersion i := hU.isOpenImmersion_fromSpec
  let ψ : A →+* PadicAlgCl p := ψ'.hom
  have hψ : spMap ψ ≫ i = x := hψ'
  obtain ⟨α, hα⟩ : ∃ α : V →+* A, spMap α = i ≫ s := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (i ≫ s)
    exact ⟨α.hom, hα⟩
  have hft : α.FiniteType := by
    have : LocallyOfFiniteType (spMap α) := by rw [hα]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hψα : ψ.comp α = φ := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (?_ : spMap _ = spMap _))
    rw [← spMap_comp_spMap, hα, ← Category.assoc, hψ, hx]
  letI := α.toAlgebra
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (self := hft)
  haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := K₀ ⊔ IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))
  have hk : K₀ ≤ K := le_sup_left
  have hmem : ∀ x, ψ x ∈ K := by
    intro x
    have hx : x ∈ Algebra.adjoin V (t : Set A) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      change (ψ.comp α) r ∈ K
      rw [hψα]; exact hk (hφ r)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨K, hk, IntermediateField.finiteDimensional_sup _ _, spMap (ψ.codRestrict K hmem) ≫ i, ?_⟩
  rw [← Category.assoc, spMap_comp_spMap]
  exact hψ

theorem isProjOver_snd_snd {V F O K : Type} [CommRing V] [CommRing F] [CommRing O] [CommRing K] {X : Scheme.{0}}
    (s : X ⟶ Sp V) (α : V →+* F) (β : F →+* K) (ψ : V →+* O) (χ : O →+* K) (h : β.comp α = χ.comp ψ)
    (hp : IsProjOver (pullback.snd s (spMap α))) :
    IsProjOver (pullback.snd (pullback.snd s (spMap ψ)) (spMap χ)) := by
  have e : spMap χ ≫ spMap ψ = spMap β ≫ spMap α := by rw [spMap_comp_spMap, spMap_comp_spMap, h]
  have H := (IsPullback.of_hasPullback (pullback.snd s (spMap ψ)) (spMap χ)).paste_horiz
    (IsPullback.of_hasPullback s (spMap ψ))
  rw [e] at H
  exact ProjSpace.isProjOver_of_isPullback_spMap β
    (IsPullback.of_right' H (IsPullback.of_hasPullback s (spMap α))) hp

end GlobalTheory.ZH.MultInt

namespace GlobalTheory.ZH
open MultInt

theorem exists_int_pow : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC), ∃ k : ℕ, 1 ≤ k ∧ u.Int (a ^ k) := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u a
  obtain ⟨-, -, -, K₀, hK₀, hr⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  haveI := u.semi.smooth
  haveI := u.semi.separated
  let θ : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  let α : u.V →+* FractionRing u.V := algebraMap _ _
  have hθ : ∀ v, θ v ∈ K₀ := fun v => show θ v ∈ (K₀ : Set _) from hr ▸ ⟨v, rfl⟩
  have ha : u.toG a ≫ u.G.hom = spMap (θ.comp α) := by
    have := Over.w a
    rw [← spMap_comp_spMap, ThetaSys.Real.UTest.toG, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ spMap α) this
  obtain ⟨K, hK, hfd, x, hx⟩ := exists_finite_factor u.G.hom (θ.comp α) K₀ (fun v => hθ _) (u.toG a) ha
  let β : FractionRing u.V →+* K := θ.codRestrict K fun v => hK (hθ v)
  let ψ : u.V →+* integralClosure ℤ_[p] K := (β.comp α).codRestrict (integralClosure ℤ_[p] K) fun v =>
    (mem_integralClosure_padicInt_iff K _).mpr ((u.norm_le _).2 ⟨v, rfl⟩)
  let χ : integralClosure ℤ_[p] K →+* K := algebraMap _ _
  have hc : β.comp α = χ.comp ψ := rfl
  have hxG : x ≫ u.G.hom = spMap χ ≫ spMap ψ := by
    obtain ⟨δ, hδ⟩ := Spec.map_surjective (x ≫ u.G.hom)
    have h1 : spMap K.val.toRingHom ≫ spMap δ.hom = spMap (θ.comp α) := by
      rw [← ha, ← hx, Category.assoc, ← hδ]; rfl
    rw [spMap_comp_spMap] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : δ.hom = χ.comp ψ := RingHom.ext fun v => Subtype.ext (RingHom.congr_fun h2 v)
    rw [spMap_comp_spMap, ← h3, ← hδ]; rfl
  have hp : IsProjOver (pullback.snd u.G.hom (spMap α)) := by
    have : IsIso u.U.gen.inv.left := ((Over.forget _).mapIso u.U.gen).isIso_inv
    refine ProjSpace.isProjOver_of_isIso_comp (Y := pullback u.G.hom (spMap α)) u.U.gen.inv.left ?_
    have := ProjSpace.isProjOver_polAV u.A
    rw [← Over.w u.U.gen.inv] at this
    exact this
  let G' := (Over.pullback (spMap ψ)).obj u.G
  haveI : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd u.G.hom (spMap ψ)))
  haveI : IsSeparated G'.hom := inferInstanceAs (IsSeparated (pullback.snd u.G.hom (spMap ψ)))
  let a' : Over.mk (spMap χ) ⟶ G' := Over.homMk (pullback.lift x (spMap χ) hxG) (pullback.lift_snd _ _ _)
  obtain ⟨k, hk, g, hg⟩ := _root_.GlobalTheory.IntegralPower.exists_pow_integral p K G' (isProjOver_snd_snd u.G.hom α β ψ χ hc hp) a'
  let a₀ : Over.mk (spMap χ ≫ spMap ψ) ⟶ u.G := Over.homMk x hxG
  have e₁ := pow_left_pullback (spMap ψ) u.G (T := Over.mk (spMap χ)) (𝟙 _) (Category.id_comp _) a' a₀
    ((Category.id_comp _).trans (pullback.lift_fst _ _ _).symm) k
  have e₂ := pow_left_pullback (jK u.V) u.G (spMap K.val.toRingHom)
    (show spMap K.val.toRingHom ≫ spMap χ ≫ spMap ψ = spMap θ ≫ spMap α by
      simp only [spMap_comp_spMap]; rfl) a a₀ hx k
  have hgw : g.left ≫ pullback.snd u.G.hom (spMap ψ) = 𝟙 _ := Over.w g
  have hg' : spMap χ ≫ g.left = (a' ^ k).left := by
    rw [← hg]; rfl
  refine ⟨k, hk, spMap (integralClosureToPadicAlgClIntegers K) ≫ g.left ≫ pullback.fst u.G.hom (spMap ψ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hgw, spMap_comp_spMap]
    rfl
  · have e₃ : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) = spMap K.val.toRingHom ≫ spMap χ := by
      rw [spMap_comp_spMap, spMap_comp_spMap]; rfl
    rw [reassoc_of% e₃, reassoc_of% hg']
    refine Eq.trans ?_ e₂
    exact congrArg _ (e₁.symm.trans (Category.id_comp _))

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxCosetNormGe
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.TwistCoset

theorem tx_eq_of_qEq {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) {m : ℕ} (hm : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.tx m p' = N.tx m p := by
  obtain ⟨z, h1, h2⟩ := h
  refine Eq.trans (tsum_congr fun χ => ?_) ((Equiv.addRight (m • z)).tsum_eq fun χ => N.txT m p χ)
  exact (_root_.GlobalTheory.Ex.txT_shift O N m hm p p' χ).1 z h1 h2

variable {O : Type} [CommRing O] {N : NumD O} {k : ℕ} {β : N.Form k} {u r : Oˣ} {l : ℕ}

theorem twRel_mul {a b : N.QT l} {a' b' : (N.twist β u).QT l} (ha : TwRel β u r a a') (hb : TwRel β u r b b') :
    TwRel β u r (a * b) (a' * b') := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  refine ⟨congrArg₂ (fun s t : Multiplicative N.X => s * t) a1 b1,
    congrArg₂ (fun s t : N.A => s * t) a2 b2, fun z => ?_⟩
  change a'.1.2.s z * b'.1.2.s z / N.θ (N.c z) a'.1.2.b b'.1.2.b =
    a.1.2.s z * b.1.2.s z / N.θ (N.c z) a.1.2.b b.1.2.b * r ^ β.be (a.1.1.toAdd + b.1.1.toAdd) z
  rw [a2, b2, a3, b3, map_add (f := _), LinearMap.add_apply, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

theorem twRel_qEq (hr : r ^ l = u) {a b : N.QT l} {a' b' : (N.twist β u).QT l} (ha : TwRel β u r a a')
    (hb : TwRel β u r b b') (h : N.QEq a b) : (N.twist β u).QEq a' b' := by
  obtain ⟨a1, a2, a3⟩ := ha
  obtain ⟨b1, b2, b3⟩ := hb
  obtain ⟨z, h1, h2⟩ := h
  refine ⟨z, ?_, NumD.Gt.ext ?_ (funext fun (w : N.X) => ?_)⟩
  · rw [a1, b1]; exact h1
  · refine b2.trans ?_
    rw [h2]
    exact congrArg (fun s : N.A => s * N.c z) a2.symm
  · change b'.1.2.s w = a'.1.2.s w * (N.twist β u).τ z w / N.θ (N.c w) a'.1.2.b (N.c z)
    have e : r ^ ((l : ℤ) * β.be z w) = u ^ β.be z w := by rw [zpow_mul, zpow_natCast, hr]
    rw [b3, a3, a2, N.twist_τ, h1, h2, NumD.Gt.mul_s, NumD.io_s, NumD.io_b, map_add (f := _), LinearMap.add_apply, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul, zpow_add, e]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]; abel

theorem exists_twRel_of_eq_one (r : Oˣ) (h : (N.twist β u).QT l) (h1 : h.1.1 = 1) {e : ℕ} (he : h.1.2 ^ e = 1) :
    ∃ h₀ : N.QT l, h₀ ^ e = 1 ∧ TwRel β u r h₀ h := by
  let f : (N.twist β u).Gt →* N.Gt := MonoidHom.mk' (fun g => ⟨g.b, g.s, g.mult⟩) fun _ _ => rfl
  have hl : h.1.2 ^ l = 1 := by
    rw [(N.twist β u).mem_QT.1 h.2, h1]; exact (N.twist β u).io_zero
  refine ⟨⟨(1, f h.1.2), ?_⟩, Subtype.ext (Prod.ext (one_pow e) ?_), h1, rfl, fun z => ?_⟩
  · rw [NumD.mem_QT, ← map_pow, hl, map_one]; exact N.io_zero.symm
  · change f h.1.2 ^ e = 1
    rw [← map_pow, he, map_one]
  · change h.1.2.s z = h.1.2.s z * r ^ β.be 0 z
    rw [map_zero, LinearMap.zero_apply, zpow_zero, mul_one]

variable {La : Type} [AddCommGroup La] {q : La → N.QT l}

theorem qEq_zero (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) : N.QEq (q 0) 1 := by
  have E : Equivalence (N.QEq (k := l)) := by
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  have := TateInh.qEq_mul N (hq 0 0) (E.refl (q 0)⁻¹)
  rwa [add_zero, mul_inv_cancel_right, mul_inv_cancel] at this

theorem qEq_nsmul (hq : ∀ a b, N.QEq (q a * q b) (q (a + b))) (a : La) (e : ℕ) : N.QEq (q a ^ e) (q (e • a)) := by
  have E : Equivalence (N.QEq (k := l)) := by
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact E.symm (qEq_zero hq)
  | succ e ih => rw [pow_succ, succ_nsmul]; exact E.trans (TateInh.qEq_mul N ih (E.refl _)) (hq _ _)

theorem qEq_pow {a b : N.QT l} (h : N.QEq a b) (e : ℕ) : N.QEq (a ^ e) (b ^ e) := by
  induction e with
  | zero => rw [pow_zero, pow_zero]; exact ⟨0, by simp, by simp⟩
  | succ e ih => rw [pow_succ, pow_succ]; exact TateInh.qEq_mul N ih h

theorem eq_zero_of_pow_nsmul {n : ℕ} (hn : ∀ a : La, n • a = 0 → a = 0) (e : ℕ) (a : La) (h : n ^ e • a = 0) :
    a = 0 := by
  induction e with
  | zero => rwa [pow_zero, one_smul] at h
  | succ e ih => exact ih (hn _ (by rwa [pow_succ', mul_smul] at h))

end GlobalTheory.TwistCoset


open GlobalTheory.TwistCoset in
theorem GlobalTheory.twist_tx_coset_norm_ge : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (k : ℕ) (β : N.Form k) (u r : Cˣ) (qf : QuadraticMap ℤ N.X ℝ) (n g j : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 → 1 ≤ j → ‖(u : C)‖ < 1 → r ^ ((n ^ j) ^ 2) = u → (N.twist β u).Int qf → (∀ y, qf y = -Real.log ‖(u : C)‖ * ((β.be y y : ℝ) / 2)) → N.Tors n g → ∀ (La : Type) [AddCommGroup La] (q : La → N.QT ((n ^ j) ^ 2)), (∀ a : La, n • a = 0 → a = 0) → (∀ a b, N.QEq (q a * q b) (q (a + b))) → (∀ a b, N.QEq (q a) (q b) ↔ ∃ e, a = b + (n ^ j) ^ 2 • e) → (∀ p, ∃ a, N.QEq (q a) p) → ∀ p : La → (N.twist β u).QT ((n ^ j) ^ 2), (∀ x, TwRel β u r (q x) (p x)) → (∃ x, 1 ≤ ‖(N.twist β u).tx (n ^ j) (p x)‖) ∧ ∀ x, ∃ h, ‖(u : C)‖ ^ (β.be (q x).1.1.toAdd (q x).1.1.toAdd).toNat ≤ ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • h))‖ := by
  intro C _ _ _ _ N k β u r qf n g j hp ho hn hj hu hr hI hqf hT La _ q htf hadd hker honto p hpq
  have hm : Odd (n ^ j) := ho.pow
  have E : Equivalence (N.QEq (k := (n ^ j) ^ 2)) := by
    exact {
      refl := fun p => ⟨0, by simp, by simp⟩
      symm := by
        rintro p p' ⟨z, h, h'⟩
        exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
      trans := by
        rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
        exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, _root_.mul_assoc]⟩ }
  have hP : qf.PosDef := GlobalTheory.CosetCrit.posDef_of_tendsto (X := N.X) hI.pos
  have key : ∀ (x : La) (χ₀ : N.X), (∀ χ : N.X, qf ((q x).1.1.toAdd + n ^ j • χ₀) ≤ qf ((q x).1.1.toAdd + n ^ j • χ)) →
      ∃ e, Real.exp (-(qf ((q x).1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤
        ‖(N.twist β u).tx (n ^ j) (p (x + n ^ (j - 1) • e))‖ := fun x χ₀ h₀ => by
    obtain ⟨h, h1, h2, h3⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge (N := N.twist β u) (q := qf) hI hp ho hn hT hj (p x)
      (χ₀ := χ₀) (by rw [(hpq x).1]; exact h₀)
    obtain ⟨h', h4, h5⟩ := exists_twRel_of_eq_one r h h1 h2
    obtain ⟨a, ha⟩ := honto h'
    have h6 : N.QEq (q (n ^ (j + 1) • a)) (q 0) := by
      have := qEq_pow ha (n ^ (j + 1))
      rw [h4] at this
      exact E.trans (E.symm (qEq_nsmul hadd a _)) (E.trans this (E.symm (qEq_zero hadd)))
    obtain ⟨e, he⟩ := (hker _ _).1 h6
    have h7 : a = n ^ (j - 1) • e := by
      refine sub_eq_zero.1 (eq_zero_of_pow_nsmul htf (j + 1) _ ?_)
      rw [smul_sub, he, zero_add, ← mul_smul, ← pow_add, ← pow_mul, show j + 1 + (j - 1) = j * 2 by omega, sub_self]
    refine ⟨e, ?_⟩
    have h8 : N.QEq (q x * h') (q (x + a)) := E.trans (TateInh.qEq_mul N (E.refl _) (E.symm ha)) (hadd x a)
    rw [← h7, tx_eq_of_qEq _ hm (twRel_qEq hr (twRel_mul (hpq x) h5) (hpq (x + a)) h8)]
    rw [(hpq x).1] at h3
    exact h3
  refine ⟨?_, fun x => ?_⟩
  · obtain ⟨z, hz, -⟩ := E.symm (qEq_zero hadd)
    have hz0 : (q 0).1.1.toAdd + n ^ j • (-(n ^ j • z)) = 0 := by
      rw [hz, smul_neg, ← mul_smul, ← sq]
      exact (congrArg (· + -((n ^ j) ^ 2 • z)) (zero_add _)).trans (add_neg_cancel _)
    obtain ⟨e, he⟩ := key 0 (-(n ^ j • z)) fun χ => by rw [hz0, map_zero]; exact hP.nonneg _
    rw [hz0, map_zero, zero_div, neg_zero, Real.exp_zero] at he
    exact ⟨_, he⟩
  · obtain ⟨χ₀, h₀⟩ := (GlobalTheory.CosetCrit.tendsto_class (X := N.X) (q := qf) hI.pos (q x).1.1.toAdd
      hm.pos.ne').exists_forall_le
    obtain ⟨e, he⟩ := key x χ₀ h₀
    refine ⟨e, le_trans ?_ he⟩
    have h1 := h₀ 0
    rw [smul_zero, add_zero, hqf (q x).1.1.toAdd] at h1
    have h2 := hP.nonneg ((q x).1.1.toAdd + n ^ j • χ₀)
    set y := (q x).1.1.toAdd
    have hB : 0 ≤ β.be y y := by
      by_cases hy : y = 0
      · rw [hy, map_zero]
      · exact (β.pos y hy).le
    have h0 : 0 < ‖(u : C)‖ := norm_pos_iff.2 u.ne_zero
    have hL : Real.log ‖(u : C)‖ < 0 := Real.log_neg h0 hu
    have hc : (((β.be y y).toNat : ℕ) : ℝ) = (β.be y y : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hB]
    have hB' : (0 : ℝ) ≤ (β.be y y : ℝ) := by exact_mod_cast hB
    have hsq : (1 : ℝ) ≤ ((n ^ j : ℕ) : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hm.pos)
    have h3 := div_le_self h2 hsq
    rw [← Real.exp_log (pow_pos h0 _), Real.log_pow, hc]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_nonneg hB' (neg_pos.2 hL).le]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistTxEvEqMapArcRoot
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Ex
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.RootSum

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) : N.Form n where
  be := (n : ℤ) • β.be
  symm y z := congrArg ((n : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hn) (β.pos y hy)
  dvd y z := by
    obtain ⟨a, ha⟩ := β.dvd y z
    exact ⟨k * a, by change (n : ℤ) * β.be y z = _; rw [ha]; ring⟩

def pullForm {O O' : Type} [CommRing O] [CommRing O'] {N₀ : NumD O} {N : NumD O'} {k : ℕ} (β : N.Form k)
    (e : N₀.X ≃+ N.X) (be₀ : LinearMap.BilinForm ℤ N₀.X) (h : ∀ y z, β.be (e y) (e z) = be₀ y z) : N₀.Form k where
  be := be₀
  symm y z := by rw [← h, ← h, β.symm]
  pos y hy := by rw [← h]; exact β.pos _ (fun h0 => hy (e.map_eq_zero_iff.1 h0))
  dvd y z := h y z ▸ β.dvd _ _

def idHom {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u : Oˣ)
    (h : t ^ n = u) : NumD.Hom (RingHom.id O) (N.twist (scaleForm β n hn) t) (N.twist β u) where
  φ := MonoidHom.id _
  h _ := 1
  h_one := rfl
  θ_eq _ _ _ := by simp only [mul_one]; rfl
  σ_eq _ := by simp only [mul_one]; rfl
  lam := 1
  th_eq _ := by simp only [mul_one, Units.val_one, one_mul]; rfl
  e := AddEquiv.refl N.X
  c_eq _ := rfl
  ψ_eq (χ : N.X) := by
    rw [mul_one]
    change N.ψ χ * u ^ (β.be χ χ / 2) = N.ψ χ * t ^ ((n : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl : (2 : ℤ) ∣ 2 * k).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, h]

theorem idHom_rel {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (n : ℕ) (hn : 0 < n) (t u r : Oˣ)
    (h : t ^ n = u) {i : ℕ} (a : ℕ) (hi : i * a = n) (hd : i ∣ n) (hr : t ^ a = r) (p₁ : N.QT i)
    (p : (N.twist β u).QT i) (hp : TwRel β u r p₁ p) :
    p.1.1.toAdd = (idHom β n hn t u h).e (N.twQ (scaleForm β n hn) t hd p₁).1.1.toAdd ∧
      (idHom β n hn t u h).Rel (N.twQ (scaleForm β n hn) t hd p₁).1.2 p.1.2 := by
  refine ⟨congrArg Multiplicative.toAdd hp.1, hp.2.1, fun (χ : N.X) => ?_⟩
  change p.1.2.s χ * 1 = p₁.1.2.s χ * t ^ ((n : ℤ) * β.be p₁.1.1.toAdd χ / i) * 1 * 1
  have hi0 : (i : ℤ) ≠ 0 := by
    rintro h0
    rw [Int.natCast_eq_zero.1 h0, zero_mul] at hi
    omega
  rw [hp.2.2, ← hi, Nat.cast_mul, mul_assoc (i : ℤ), Int.mul_ediv_cancel_left _ hi0, zpow_mul, zpow_natCast, hr,
    mul_one, mul_one]

theorem twist_tx_ev_eq_map_arc_root : ∀ (O C : Type) [CommRing O] [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (φ : PowerSeries O →+* C), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (t u rm rj : Cˣ) (m j : ℕ), Odd m → 0 < j → (t : C) = φ PowerSeries.X → t ^ j = rm → t ^ (m ^ 2) = rj → rm ^ (m ^ 2) = u → ∀ (N₀ : NumD O) (N : NumD C) (I : NumD.Hom (φ.comp PowerSeries.C) N₀ N) (k : ℕ) (be₀ : LinearMap.BilinForm ℤ N₀.X) (β : N.Form k), (∀ y z, β.be (I.e y) (I.e z) = be₀ y z) → ∀ (p₀ : N₀.QT (m ^ 2)) (p₁ : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2)), p₁.1.1.toAdd = I.e p₀.1.1.toAdd → I.Rel p₀.1.2 p₁.1.2 → TwRel β u rm p₁ p → (N.twist β u).tx m p = I.lam * φ (N₀.arcTx (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀) ∧ ∀ (q₀ : N₀.QT j) (q₁ : N.QT j) (q : (N.twist β u).QT j), q₁.1.1.toAdd = I.e q₀.1.1.toAdd → I.Rel q₀.1.2 q₁.1.2 → TwRel β u rj q₁ q → ∀ s : ℕ, (m : ℤ) ^ 2 * (((m ^ 2 * j : ℕ) : ℤ) * be₀ q₀.1.1.toAdd q₀.1.1.toAdd) ≤ s → (t : C) ^ s * (N.twist β u).ev m p q.1.2 = (I.lam * I.h q₀.1.2.b ^ (m ^ 2) : Cˣ) * φ (N₀.arcEv (((m ^ 2 * j : ℕ) : ℤ) • be₀) m p₀ q₀ s) := by
  intro O C _ _ _ _ φ h1 h2 t u rm rj m j hm hj ht hrm hrj hu N₀ N I k be₀ β hβ p₀ p₁ p hp1 hp2 hp
  have hn : 0 < m ^ 2 * j := Nat.mul_pos (pow_pos hm.pos 2) hj
  have htu : t ^ (m ^ 2 * j) = u := by rw [mul_comm, pow_mul, hrm, hu]
  have hd : m ^ 2 ∣ m ^ 2 * j := Dvd.intro _ rfl
  have key := _root_.GlobalTheory.Ex.twist_tx_ev_eq_map_arc O C φ h1 h2 t ht N₀ N I (m ^ 2 * j) (scaleForm (pullForm β I.e be₀ hβ) _ hn)
    (scaleForm β _ hn) (fun y z => congrArg (((m ^ 2 * j : ℕ) : ℤ) * ·) (hβ y z)) m hd hm p₀ p₁ hp1 hp2
  have hr := idHom_rel β _ hn t u rm htu j rfl hd hrm p₁ p hp
  have tr := (NumD.hom_transport C C _ _ _ (idHom β _ hn t u htu)).2.2.2.2 m hm _ p hr.1 hr.2
  refine ⟨Eq.trans (tsum_congr fun χ => ?_) key.1, fun q₀ q₁ q hq1 hq2 hq s hs => ?_⟩
  · exact (tr χ).1.trans (one_mul _)
  · have hd' : j ∣ m ^ 2 * j := Dvd.intro_left _ rfl
    have hr' := idHom_rel β _ hn t u rj htu (m ^ 2) (mul_comm _ _) hd' hrj q₁ q hq
    refine Eq.trans (congrArg _ (tsum_congr fun χ => ?_)) (key.2 j hd' q₀ q₁ hj.ne' hq1 hq2 s hs)
    refine ((tr χ).2 _ _ hr'.2).trans ?_
    change ((1 * 1 ^ (m ^ 2) : Cˣ) : C) * _ = _
    rw [one_pow, mul_one, Units.val_one, one_mul]
    rfl

end GlobalTheory.Ex.RootSum
end
end

