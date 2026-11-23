module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AdmissibleOfIntegralConjLe
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem powMap_congr {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f f' : X ⟶ Y} {φ φ' : A.left ⟶ B.left} (h : f = f') (h' : φ = φ')
    (u : φ ≫ B.hom = A.hom ≫ f) (u' : φ' ≫ B.hom = A.hom ≫ f') (k : ℕ) : GlobalTheory.KS.powMap f φ u k = GlobalTheory.KS.powMap f' φ' u' k := by
  subst h h'; rfl

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫}

theorem Down.pw_ov (hP : PowCart) {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} (d : Down X₁ X₂) (k : ℕ) :
    d.pw k ≫ (GlobalTheory.KS.pow X₂.Y.univ.A k).hom ≫ X₂.Y.s = (GlobalTheory.KS.pow X₁.Y.univ.A k).hom ≫ X₁.Y.s := by
  have h := (hP _ _ _ X₁.Y.univ.A X₂.Y.univ.A X₂.Y.univ.A d.t (𝟙 _) d.Φ (𝟙 _) d.w (by simp) k).2.1
  rw [Down.pw, ← Category.assoc, h, Category.assoc, d.ov]

theorem exists_wit (hP : PowCart) {k : ℕ} (T : KS L gb k) (h : G.GAf) (M₁ M₂ : Lv p) (a b) :
    ∃ W : Wit T h M₁ M₂, ∀ {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}
      (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (d : Down X₁ X₂), d.Extends W C₁ C₂ →
      X₁.site.pi T C₁ ≫ d.pw k = T.X.tr (T.lev M₁) (T.lev M₂) h a b ≫ X₂.site.pi T C₂ := by
  obtain ⟨π, o, ψ, φ, hw, hov, htr, he⟩ := T.tr_eq M₁ M₂ h a b
  refine ⟨⟨π, o, ψ, φ, hov, htr⟩, fun {_ _ _ _ X₁ X₂ _ _ _ _} C₁ C₂ d hd => ?_⟩
  have e1 := (hP _ _ _ (T.M M₁).univ.A X₁.Y.univ.A X₂.Y.univ.A C₁.j d.t C₁.m.φ d.Φ C₁.m.cart.1.w d.w k).2.2
    (by rw [Category.assoc, d.w, ← Category.assoc, C₁.m.cart.1.w, Category.assoc])
  have e2 := (hP _ _ _ (T.M M₁).univ.A (T.M M₂).univ.A X₂.Y.univ.A π C₂.j (ψ.left ≫ φ.φ) C₂.m.φ hw C₂.m.cart.1.w k).2.2
    (by rw [Category.assoc, C₂.m.cart.1.w, ← Category.assoc, hw, Category.assoc])
  have e3 : C₁.pw k ≫ d.pw k = GlobalTheory.KS.powMap π (ψ.left ≫ φ.φ) hw k ≫ C₂.pw k :=
    e1.trans ((powMap_congr hd.1 (hd.2.trans (Category.assoc _ _ _).symm) _ _ k).trans e2.symm)
  show ((T.e M₁).hom ≫ C₁.pw k) ≫ d.pw k = _ ≫ (T.e M₂).hom ≫ C₂.pw k
  rw [Category.assoc, e3, ← Category.assoc, ← he, Category.assoc]

def Ext.ps {N₁ : ℕ} {𝔟 : Ideal (𝓞 D.F)} (X : Ext S N₁ 𝔟) (k : ℕ) : (GlobalTheory.KS.pow X.Y.univ.A k).left ⟶ Spec (CommRingCat.of (Ow w)) :=
  (GlobalTheory.KS.pow X.Y.univ.A k).hom ≫ X.Y.s

def Ok {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {k : ℕ} (T : KS L gb k) (h : G.GAf) {M₁ M₂ : Lv p}
    (π₁ : T.X.Z (T.lev M₁) ⟶ (GlobalTheory.KS.pow X₁.Y.univ.A k).left) (π₂ : T.X.Z (T.lev M₂) ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left)
    (t : (GlobalTheory.KS.pow X₁.Y.univ.A k).left ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left) : Prop :=
  t ≫ X₂.ps k = X₁.ps k ∧ ∀ a b, π₁ ≫ t = T.X.tr (T.lev M₁) (T.lev M₂) h a b ≫ π₂

theorem ok_of (hP : PowCart) {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {k : ℕ} (T : KS L gb k) (h : G.GAf)
    {M₁ M₂ : Lv p} {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F} (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂)
    (Q : Down X₁ X₂ → Prop) (ad : T.X.admitted (T.lev M₁) (T.lev M₂) h)
    (H : ∀ W : Wit T h M₁ M₂, ∃ d : Down X₁ X₂, d.Extends W C₁ C₂ ∧ Q d) :
    ∃ d : Down X₁ X₂, Ok T h (X₁.site.pi T C₁) (X₂.site.pi T C₂) (d.pw k) ∧ Q d := by
  obtain ⟨W, hW⟩ := exists_wit (S := S) hP T h M₁ M₂ ad.1 ad.2
  obtain ⟨d, hd, hq⟩ := H W
  exact ⟨d, ⟨d.pw_ov hP k, fun _ _ => hW C₁ C₂ d hd⟩, hq⟩

theorem Ok.comp {N₁ N₂ N₃ : ℕ} {𝔟₁ 𝔟₂ 𝔟₃ : Ideal (𝓞 D.F)} {X₁ : Ext S N₁ 𝔟₁} {X₂ : Ext S N₂ 𝔟₂} {X₃ : Ext S N₃ 𝔟₃} {k : ℕ} {T : KS L gb k}
    {h h' : G.GAf} {M₁ M₂ M₃ : Lv p} {π₁ : T.X.Z (T.lev M₁) ⟶ (GlobalTheory.KS.pow X₁.Y.univ.A k).left}
    {π₂ : T.X.Z (T.lev M₂) ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left} {π₃ : T.X.Z (T.lev M₃) ⟶ (GlobalTheory.KS.pow X₃.Y.univ.A k).left} {t t'}
    (H : Ok T h π₁ π₂ t) (H' : Ok T h' π₂ π₃ t') (ad : T.X.admitted (T.lev M₁) (T.lev M₂) h) (ad' : T.X.admitted (T.lev M₂) (T.lev M₃) h') :
    Ok T (h' * h) π₁ π₃ (t ≫ t') := by
  refine ⟨by rw [Category.assoc, H'.1, H.1], fun a b => ?_⟩
  rw [← Category.assoc, H.2 ad.1 ad.2, Category.assoc, H'.2 ad'.1 ad'.2, ← Category.assoc, T.X.tr_mul]

theorem admissible_of_integral_conj_le {k : ℕ} (T : KS L gb k) {h : G.GAf} {M₁ M₂ : Lv p} (hi : Integ L h) (ha : ∀ u ∈ L.KN M₁.1, h * u * h⁻¹ ∈ L.KN M₂.1) :
    T.X.admitted (T.lev M₁) (T.lev M₂) h :=
  ⟨(T.Δ_eq _).2 hi, fun u hu => by rw [T.K_eq] at hu ⊢; exact ha u hu⟩

theorem cls_of (hNum : NumEx) (hCls : ClsEx) {N₁ : ℕ} {𝔟 : Ideal (𝓞 D.F)} (X : Ext S N₁ 𝔟) {k : ℕ} (T : KS L gb k) (M : Lv p) (c : ℕ) (a : 𝓞 D.F)
    (hn : X.site.Num M.1 c a) : Nonempty (X.site.Cl (T.M M).univ c a) :=
  (hCls q (datAt S.atq S.sp) (Ow w) E S.b gb _ S.mat M.1 _ c a _ hn.1 (lt_of_lt_of_le (by norm_num) M.2.1) X.lev.1 X.lev.2.1 hn.2 X.Y _ _
    (T.M M).univ).1

theorem lev_le {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} {K₀ K₁ : Subgroup G.GAf} (hK₀ : IsLev L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) K₀)
    (hK₁ : IsLev L (Ideal.span {((N₀ * κ : ℕ) : 𝓞 D.F)} * 𝔞') K₁) (hle : 𝔞' ≤ 𝔞) : K₁ ≤ K₀ := fun u hu => by
  obtain ⟨u1, u2⟩ := (hK₁ u).1 hu
  refine (hK₀ u).2 ⟨u1, fun v hv => AddSubgroup.closure_mono ?_ (u2 v hv)⟩
  rintro z ⟨x, hx, y⟩
  refine ⟨x, Ideal.mul_mono ?_ hle hx, y⟩
  rw [Ideal.span_singleton_le_span_singleton, Nat.cast_mul]
  exact dvd_mul_right _ _

theorem forget_of (hSc : Sc D G) (hNum : NumEx) (hCls : ClsEx) (hInv : PiInv) (hP : PowCart) (hQ : QuotOf) (hF : StepF) (hD : DegGen) (hE : FEtExt)
    {k : ℕ} (T : KS L gb k) {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} (X₁ : Ext S (N₀ * κ) 𝔞') (X₀ : Ext S N₀ 𝔞) (hle : 𝔞' ≤ 𝔞) {K₀ K₁ : Subgroup G.GAf}
    (hK₀ : IsLev L (Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞) K₀) (hK₁ : IsLev L (Ideal.span {((N₀ * κ : ℕ) : 𝓞 D.F)} * 𝔞') K₁) {M N : Lv p}
    (hd : N.1 ∣ M.1) {c₁ c₀ : ℕ} {a₁ a₀ : 𝓞 D.F} (n₁ : X₁.site.Num M.1 c₁ a₁) (n₀ : X₀.site.Num N.1 c₀ a₀)
    (C₁ : X₁.site.Cl (T.M M).univ c₁ a₁) (C₀ : X₀.site.Cl (T.M N).univ c₀ a₀) :
    ∃ s, Ok T 1 (X₁.site.pi T C₁) (X₀.site.pi T C₀) s ∧ IsQuot T.X (Ow w) K₀ (T.lev M) (X₀.ps k) (X₁.site.pi T C₁ ≫ s) ∧
      IsQuot T.X (Ow w) K₁ (T.lev M) (s ≫ X₀.ps k) (X₁.site.pi T C₁) ∧ FEt s (K₁.relIndex K₀) := by
  have ad : T.X.admitted (T.lev M) (T.lev N) 1 := admissible_of_integral_conj_le T (integ_of_mem (one_mem _)) fun u hu => by simpa using KN_anti hd hu
  obtain ⟨d, ok, fd, ed, pd⟩ := ok_of hP T 1 C₁ C₀ _ ad (hF p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞 X₁ X₀ hle M N c₁ c₀ a₁ a₀ n₁ n₀ hd C₁ C₀)
  obtain ⟨t, ht⟩ := hd
  have n₀' : X₀.site.Num M.1 (c₀ * t) (t * a₀) := by
    rw [ht]; exact (hNum p D E gb w q r 𝔴 _ X₀.site N.1 (lt_of_lt_of_le (by norm_num) N.2.1)).2 c₀ a₀ t n₀
  obtain ⟨C₀'⟩ := cls_of hNum hCls X₀ T M _ _ n₀'
  have pb := (hP _ _ _ X₁.Y.univ.A X₀.Y.univ.A X₀.Y.univ.A d.t (𝟙 _) d.Φ (𝟙 _) d.w (by simp) k).1 pd
  have fs : IsFinite (d.pw k) := MorphismProperty.of_isPullback pb.flip fd
  have ets : Etale (d.pw k) := MorphismProperty.of_isPullback pb.flip ed
  have e0 : X₁.site.pi T C₁ ≫ d.pw k = X₀.site.pi T C₀' :=
    (ok.2 ad.1 ad.2).trans (hInv p D G L E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ M N t c₀ a₀ ht n₀ C₀' C₀ 1 (one_mem _) _ _)
  have q0 : IsQuot T.X (Ow w) K₀ (T.lev M) (X₀.ps k) (X₁.site.pi T C₁ ≫ d.pw k) :=
    e0.symm ▸ hQ p D G L hSc E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ M _ _ n₀' C₀'
  have q1 : IsQuot T.X (Ow w) K₁ (T.lev M) (d.pw k ≫ X₀.ps k) (X₁.site.pi T C₁) := by
    rw [ok.1]
    exact hQ p D G L hSc E gb w q r 𝔴 _ X₁.site k T K₁ hK₁ M _ _ n₁ C₁
  have fl : Flat (X₀.ps k) := by
    obtain ⟨n, hn⟩ := X₀.dim k
    haveI : Smooth (X₀.ps k) := hn.smooth
    infer_instance
  exact ⟨d.pw k, ok, q0, q1, hE (Ow w) E _ _ _ _ _ fl fs ets (hD E _ T.X (Ow w) K₀ K₁ _ _ _ _ _ _ (lev_le hK₀ hK₁ hle) q0 q1)⟩

theorem transl_of (hSc : Sc D G) (hNum : NumEx) (hCls : ClsEx) (hP : PowCart) (hExt : ExtEx) (hA : StepA) (hB : StepB)
    {k : ℕ} (T : KS L gb k) {N₀ κ : ℕ} {𝔞 𝔞' : Ideal (𝓞 D.F)} (X₁ : Ext S (N₀ * κ) 𝔞') (X₀ : Ext S N₀ 𝔞) (hle : 𝔞' ≤ 𝔞) {M N N₁ : Lv p}
    {c₁ c₀ : ℕ} {a₁ a₀ : 𝓞 D.F} (n₁ : X₁.site.Num M.1 c₁ a₁) (n₀ : X₀.site.Num N.1 c₀ a₀)
    (C₁ : X₁.site.Cl (T.M M).univ c₁ a₁) (C₀ : X₀.site.Cl (T.M N).univ c₀ a₀) {h₁ h₂ : G.GAf} (i₁ : Integ L h₁) (i₂ : Integ L h₂)
    (hκ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = κ • v) (hN₁ : ((N₁.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞')
    (ad₂ : ∀ u ∈ L.KN M.1, h₂ * u * h₂⁻¹ ∈ L.KN N₁.1) (ad₁ : ∀ u ∈ L.KN N₁.1, h₁ * u * h₁⁻¹ ∈ L.KN N.1)
    (hcase : h₁ = 1 ∨ ∃ (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal ∧ uId D q r ≤ 𝔴' ∧ 𝔞' ≤ 𝔞 * 𝔴' ∧ i ≤ D.n ∧
      Ideal.absNorm 𝔴' ^ i ∣ N₁.1 ∧ IsTjElt L q r 𝔴' i h₁) :
    ∃ t, Ok T (h₁ * h₂) (X₁.site.pi T C₁) (X₀.site.pi T C₀) t := by
  rcases hcase with h1 | ⟨𝔴', i, m', u', le', hi, dv, tj⟩
  · rw [h1] at ad₁
    rw [h1, _root_.one_mul]
    obtain ⟨d, ok, -⟩ := ok_of hP T h₂ C₁ C₀ (fun _ => True) (admissible_of_integral_conj_le T i₂ fun u hu => by simpa using ad₁ _ (ad₂ u hu)) fun W =>
      (hA p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞 X₁ X₀ hle _ i₂ hκ M N c₁ c₀ a₁ a₀ n₁ n₀ C₁ C₀ W).imp fun _ h => ⟨h, trivial⟩
    exact ⟨_, ok⟩
  · obtain ⟨X₂⟩ := hExt p D G hSc E gb w q r 𝔴 _ S N₀ 𝔞' ⟨X₀.lev.1, X₀.lev.2.1, X₀.lev.2.2.1, X₁.lev.2.2.2.1, X₁.lev.2.2.2.2⟩
    obtain ⟨c₂, a₂, n₂⟩ := (hNum p D E gb w q r 𝔴 _ X₂.site N₁.1 (lt_of_lt_of_le (by norm_num) N₁.2.1)).1 hN₁
    obtain ⟨C₂⟩ := cls_of hNum hCls X₂ T N₁ c₂ a₂ n₂
    obtain ⟨d₂, ok₂, -⟩ := ok_of hP T h₂ C₁ C₂ (fun _ => True) (admissible_of_integral_conj_le T i₂ ad₂) fun W =>
      (hA p D G L hSc E gb w q r 𝔴 _ S k T N₀ κ 𝔞' 𝔞' X₁ X₂ le_rfl _ i₂ hκ M N₁ c₁ c₂ a₁ a₂ n₁ n₂ C₁ C₂ W).imp fun _ h => ⟨h, trivial⟩
    obtain ⟨d₁, ok₁, -⟩ := ok_of hP T h₁ C₂ C₀ (fun _ => True) (admissible_of_integral_conj_le T i₁ ad₁) fun W =>
      (hB p D G L hSc E gb w q r 𝔴 _ S k T N₀ 𝔞' 𝔞 X₂ X₀ 𝔴' i m' u' le' hi h₁ i₁ tj N₁ N c₂ c₀ a₂ a₀ n₂ n₀ dv C₂ C₀ W).imp fun _ h => ⟨h, trivial⟩
    exact ⟨_, ok₂.comp ok₁ (admissible_of_integral_conj_le T i₂ ad₂) (admissible_of_integral_conj_le T i₁ ad₁)⟩

end

theorem ksGood_of (hSite : SiteEx) (hNum : NumEx) (hCls : ClsEx) (hCov : KSCover) (hInv : PiInv) (hP : PowCart) (hExt : ExtEx)
    (hQ : QuotOf) (hA : StepA) (hB : StepB) (hF : StepF) (hD : DegGen) (hE : FEtExt) (hL : LiesAbs) : KSGood := by
  intro p _ D G L hSc E _ _ e gb hstd k T N J A _ g θ w 𝔴 hpl ⟨q, r, N₀, 𝔞, K₀, hat, hlev, hK₀, hNK, hNm, hdeck, hall⟩
  haveI : Fact q.Prime := ⟨hat.prime⟩
  obtain ⟨S⟩ := hSite p D G hSc E e gb hstd w q r 𝔴 _ hpl hat ⟨N₀, 𝔞, hlev.1, hlev.2.1, hlev.2.2.1, hlev.2.2.2.1, hlev.2.2.2.2, rfl⟩
  have pos : ∀ M : Lv p, 0 < M.1 := fun M => lt_of_lt_of_le (by norm_num) M.2.1
  obtain ⟨X₀⟩ := hExt p D G hSc E gb w q r 𝔴 _ S N₀ 𝔞 hlev
  obtain ⟨c₀, a₀, n₀⟩ := (hNum p D E gb w q r 𝔴 _ X₀.site N.1 (pos N)).1 hNm
  obtain ⟨C₀⟩ := cls_of hNum hCls X₀ T N c₀ a₀ n₀
  obtain ⟨Cv⟩ := hCov p D G L E gb w q r 𝔴 _ X₀.site k T K₀ hK₀ N c₀ a₀ n₀ C₀ hNK J A g θ hdeck
  refine ⟨Cv.toCover, fun j => ?_⟩
  obtain ⟨κ, 𝔞', K₁, h₁, h₂, N₁, hlev', hK₁, hle, -, hMm, hdec, hh, i₁, i₂, hκ, hN₁, ad₂, ad₁, hcase⟩ := hall j
  obtain ⟨X₁⟩ := hExt p D G hSc E gb w q r 𝔴 _ S (N₀ * κ) 𝔞' hlev'
  obtain ⟨c₁, a₁, n₁⟩ := (hNum p D E gb w q r 𝔴 _ X₁.site (g j).M.1 (pos _)).1 hMm
  obtain ⟨C₁⟩ := cls_of hNum hCls X₁ T (g j).M c₁ a₁ n₁
  obtain ⟨s, ok, q0, q1, fe⟩ := forget_of hSc hNum hCls hInv hP hQ hF hD hE T X₁ X₀ hle hK₀ hK₁ (g j).dvd n₁ n₀ C₁ C₀
  refine hL p D G L E gb k T N J A g θ (Ow w) Cv.toCover j K₀ K₁ _ (X₁.site.pi T C₁) s _ (lev_le hK₀ hK₁ hle) hNK q0 q1
    (fun a b => (ok.2 a b).symm) fe hdec fun x hx => ?_
  have x1 : x ∈ L.KN 1 := (g j).le_one hx
  have κx : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h₂ * x) v' = κ • v := fun v hv => by
    obtain ⟨v', hv', e'⟩ := hκ v hv
    refine ⟨L.actG x⁻¹ v', integ_of_mem (inv_mem x1) v' hv', ?_⟩
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right, e']
  obtain ⟨t, okt⟩ := transl_of hSc hNum hCls hP hExt hA hB T X₁ X₀ hle n₁ n₀ C₁ C₀ i₁ (i₂.mul (integ_of_mem x1)) κx hN₁ (ad₂ x hx) ad₁ hcase
  rw [← _root_.mul_assoc, ← hh] at okt
  exact ⟨t, okt.1.trans ok.1.symm, okt.2⟩

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LGrpHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lGrp_holds :
    LGrp := by
  intro Γ _ K K₀ K₁ KN KM hMN hNK hN0 hM1 h10 hnorm hdec b₀ hb₀ u hu
  obtain ⟨a, haK, ha0, hau⟩ := hdec u⁻¹ (inv_mem hu)
  have hconj : ∀ m ∈ KM, a⁻¹ * m * a ∈ KM := by
    intro m hm
    simpa using hnorm a⁻¹ (inv_mem ha0) m hm
  have hmem : ∀ (c : ↥K ⧸ KN.subgroupOf K) (n : ↥KN ⧸ KM.subgroupOf KN),
      b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * u⁻¹ ∈ K₁ →
      b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * a ∈ K ⊓ K₁ := by
    intro c n hcn
    refine ⟨?_, ?_⟩
    · exact K.mul_mem (K.mul_mem (K.mul_mem (K.inv_mem hb₀) (Quotient.out c).2) (hNK (Quotient.out n).2)) haK
    · have hua : u * a ∈ K₁ := by simpa using K₁.inv_mem hau
      rw [show b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * a
          = (b₀⁻¹ * ((Quotient.out c : ↥K) : Γ) * ((Quotient.out n : ↥KN) : Γ) * u⁻¹) * (u * a) by group]
      exact K₁.mul_mem hcn hua
  refine Eq.trans (b := Nat.card ((K ⊓ K₁ : Subgroup Γ) ⧸ KM.subgroupOf (K ⊓ K₁))) ?_ rfl
  refine Nat.card_eq_of_bijective (fun cn => (QuotientGroup.mk ⟨_, hmem cn.1.1 cn.1.2 cn.2⟩ : (K ⊓ K₁ : Subgroup Γ) ⧸ KM.subgroupOf (K ⊓ K₁))) ⟨?_, ?_⟩
  · rintro ⟨⟨c₁, n₁⟩, h₁⟩ ⟨⟨c₂, n₂⟩, h₂⟩ h
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    have h' : ((Quotient.out n₁ : ↥KN) : Γ)⁻¹ * ((Quotient.out c₁ : ↥K) : Γ)⁻¹
        * ((Quotient.out c₂ : ↥K) : Γ) * ((Quotient.out n₂ : ↥KN) : Γ) ∈ KM := by
      have := hnorm a ha0 _ h
      convert this using 1
      group
    have hc : c₁ = c₂ := by
      rw [← QuotientGroup.out_eq' c₁, ← QuotientGroup.out_eq' c₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have := KN.mul_mem (KN.mul_mem (Quotient.out n₁).2 (hMN h')) (KN.inv_mem (Quotient.out n₂).2)
      convert this using 1
      group
    subst hc
    have hn : n₁ = n₂ := by
      rw [← QuotientGroup.out_eq' n₁, ← QuotientGroup.out_eq' n₂, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      convert h' using 1
      group
    subst hn
    rfl
  · intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨x, hK, hK1⟩ := x
      let g : ↥K := ⟨b₀ * x * a⁻¹, K.mul_mem (K.mul_mem hb₀ hK) (K.inv_mem haK)⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KN.subgroupOf K) g
      have hkN : ((k : ↥K) : Γ) ∈ KN := k.2
      let n₀ : ↥KN := ⟨((k : ↥K) : Γ)⁻¹, KN.inv_mem hkN⟩
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (KM.subgroupOf KN) n₀
      have hmM : ((m : ↥KN) : Γ) ∈ KM := m.2
      have key : ((Quotient.out (QuotientGroup.mk g : ↥K ⧸ KN.subgroupOf K) : ↥K) : Γ)
          * ((Quotient.out (QuotientGroup.mk n₀ : ↥KN ⧸ KM.subgroupOf KN) : ↥KN) : Γ)
          = b₀ * x * a⁻¹ * ((m : ↥KN) : Γ) := by
        rw [hk, hm]
        simp only [Subgroup.coe_mul, g, n₀]
        group
      refine ⟨⟨(QuotientGroup.mk g, QuotientGroup.mk n₀), ?_⟩, ?_⟩
      · dsimp only
        rw [mul_assoc b₀⁻¹, key,
          show b₀⁻¹ * (b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)) * u⁻¹
            = x * (a⁻¹ * ((m : ↥KN) : Γ) * a) * (a⁻¹ * u⁻¹) by group]
        exact K₁.mul_mem (K₁.mul_mem hK1 (hM1 (hconj _ hmM))) hau
      · dsimp only
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [mul_assoc b₀⁻¹, key,
          show (b₀⁻¹ * (b₀ * x * a⁻¹ * ((m : ↥KN) : Γ)) * a)⁻¹ * x
            = (a⁻¹ * ((m : ↥KN) : Γ) * a)⁻¹ by group]
        exact KM.inv_mem (hconj _ hmM)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LIdxHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lIdx_holds :
    LIdx := by
  intro p _ D G L N hN
  obtain ⟨K1, h1⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L 1 one_pos
  obtain ⟨KN, hKN⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N hN
  have hc : CompactSpace (L.KN 1) := by
    rw [← h1]
    exact isCompact_iff_compactSpace.1 K1.compact
  have ho : IsOpen (((L.KN N).subgroupOf (L.KN 1) : Subgroup (L.KN 1)) : Set (L.KN 1)) := by
    rw [← hKN]
    exact KN.K.isOpen.preimage continuous_subtype_val
  have hf : Finite ((L.KN 1) ⧸ (L.KN N).subgroupOf (L.KN 1)) :=
    Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPCount
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lCount_holds :
    LSigPt → LSigFin → LCount := by
  intro hpt hfin I B _ _ W Z Y Y' cls f kc π s m hf he hs hes hm h
  obtain ⟨hsF, hsE⟩ := hfin B Y' Y s hs hes
  obtain ⟨hdF, hdE⟩ := hfin I W Z f hf he
  set sB : (∐ fun _ : B => Y') ⟶ Y := Sigma.desc fun _ : B => s with hsB
  set ℓ := pullback.lift _ _ h with hℓ
  have hℓ1 : ℓ ≫ pullback.fst π sB = Sigma.desc fun _ : I => f := pullback.lift_fst _ _ h
  have hℓ2 : ℓ ≫ pullback.snd π sB =
      Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c) := pullback.lift_snd _ _ h
  haveI := hsF
  haveI := hsE
  haveI : IsFinite (pullback.fst π sB) := inferInstance
  haveI : Etale (pullback.fst π sB) := inferInstance
  haveI : IsFinite (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdF
  haveI : Etale (ℓ ≫ pullback.fst π sB) := by rw [hℓ1]; exact hdE
  refine ⟨IsFinite.of_comp ℓ (pullback.fst π sB), Etale.of_comp ℓ (pullback.fst π sB), ?_⟩
  intro K _ _ x
  obtain ⟨⟨b, y'⟩, hb⟩ := (hpt B Y' K).2 (x ≫ pullback.snd π sB)
  replace hb : y' ≫ Sigma.ι (fun _ : B => Y') b = x ≫ pullback.snd π sB := hb
  have hy : y' ≫ s = (x ≫ pullback.fst π sB) ≫ π := by
    calc y' ≫ s = (y' ≫ Sigma.ι (fun _ : B => Y') b) ≫ sB := by simp [hsB]
      _ = (x ≫ pullback.fst π sB) ≫ π := by
        rw [hb, Category.assoc, Category.assoc, pullback.condition]
  have key : ∀ (c : I) (v : sp K ⟶ W), (v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ = x ↔
      v ≫ f = x ≫ pullback.fst π sB ∧ cls c = b ∧ v ≫ kc c = y' := by
    intro c v
    have e1 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.fst π sB = v ≫ f := by
      rw [Category.assoc, hℓ1]; simp
    have e2 : ((v ≫ Sigma.ι (fun _ : I => W) c) ≫ ℓ) ≫ pullback.snd π sB =
        (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) := by
      rw [Category.assoc, hℓ2]; simp
    constructor
    · intro hx
      rw [hx] at e1 e2
      have h2 : (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (cls c, v ≫ kc c) =
          (fun p : B × (sp K ⟶ Y') => p.2 ≫ Sigma.ι (fun _ : B => Y') p.1) (b, y') := by
        show (v ≫ kc c) ≫ Sigma.ι (fun _ : B => Y') (cls c) = y' ≫ Sigma.ι (fun _ : B => Y') b
        rw [← e2, hb]
      obtain ⟨h3, h4⟩ := Prod.mk.inj ((hpt B Y' K).1 h2)
      exact ⟨e1.symm, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩
      apply pullback.hom_ext
      · rw [e1, h1]
      · rw [e2, h3, h4, hb]
  rw [← hm K (x ≫ pullback.fst π sB) b y' hy]
  let F : {cx : I × (sp K ⟶ W) // cx.2 ≫ f = x ≫ pullback.fst π sB ∧ cls cx.1 = b ∧ cx.2 ≫ kc cx.1 = y'} →
      {y : sp K ⟶ ∐ (fun _ : I => W) // y ≫ ℓ = x} :=
    fun p => ⟨p.1.2 ≫ Sigma.ι (fun _ : I => W) p.1.1, (key _ _).2 p.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨⟨c, v⟩, hv⟩ ⟨⟨c', v'⟩, hv'⟩ e
      have e' : (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c, v) =
          (fun p : I × (sp K ⟶ W) => p.2 ≫ Sigma.ι (fun _ : I => W) p.1) (c', v') :=
        congrArg Subtype.val e
      exact Subtype.ext ((hpt I W K).1 e')
    · rintro ⟨y, hy'⟩
      obtain ⟨⟨c, v⟩, hv⟩ := (hpt I W K).2 y
      replace hv : v ≫ Sigma.ι (fun _ : I => W) c = y := hv
      subst hv
      exact ⟨⟨(c, v), (key c v).1 hy'⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective F hF)).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPSigFin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lSigFin_holds :
    LSigFin := by
  intro I _ W Z f hf he
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin W k
  let i : (∐ fun _ : I => W) ≅ ∐ fun _ : Fin k => W :=
    Sigma.whiskerEquiv (f := fun _ : I => W) (g := fun _ : Fin k => W) e fun _ => Iso.refl W
  have hd : (Sigma.desc fun _ : I => f) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 W) ≫ f := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_⟩
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LPSigPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lSigPt_holds :
    LSigPt := by
  intro I W Ω _
  haveI : Unique (sp Ω) := inferInstanceAs (Unique (PrimeSpectrum Ω))
  constructor
  · rintro ⟨i, x⟩ ⟨j, x'⟩ h
    have h' : x ≫ Sigma.ι (fun _ : I => W) i = x' ≫ Sigma.ι (fun _ : I => W) j := h
    have e : (Sigma.ι (fun _ : I => W) i) (x default) = (Sigma.ι (fun _ : I => W) j) (x' default) := by
      have := congrArg (fun f : sp Ω ⟶ _ => f default) h'
      simpa using this
    have e2 := (sigmaι_eq_iff _ _ _ _ _).mp e
    obtain ⟨rfl⟩ : i = j := congrArg Sigma.fst e2
    have : x = x' := (cancel_mono (Sigma.ι (fun _ : I => W) i)).mp h'
    rw [this]
  · intro y
    obtain ⟨i, w, hw⟩ := (sigmaOpenCover fun _ : I => W).exists_eq (y default)
    have hr : Set.range y ⊆ Set.range (Sigma.ι (fun _ : I => W) i) := by
      rintro _ ⟨p, rfl⟩
      rw [Subsingleton.elim p default]
      exact ⟨w, hw⟩
    exact ⟨(i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y hr), IsOpenImmersion.lift_fac _ _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PExtEx
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.extEx_holds :
    MIn → PowProj → ExtEx := by
  intro hM hPP p _ D G hSc E _ _ gb w q _ r 𝔴 𝔫 S N₁ 𝔟 hL
  obtain ⟨h3, hcq, hcp, hsup, hpow⟩ := hL
  obtain ⟨M⟩ := hM.ex q _ (Ow w) S.b N₁ h3 hcq
  have het : IsEtIdeal S.b 𝔟 :=
    (hM.placeOf q _ (Ow w) S.b r 𝔴 S.atq.max S.std.pmem S.std.a1 S.std.ule S.std.tw 𝔟 hsup).2 hpow
  obtain ⟨Y, π, ρ, hov, ⟨m⟩, hG⟩ := hM.finModel q _ (Ow w) S.b N₁ h3 hcq 𝔟 1 het M
  have hfin : IsFinite π := hG.fin
  have het' : Etale π := hG.etale
  have hMp : IsProjOver M.s := hM.proj q _ (Ow w) S.b N₁ h3 hcq hSc.cpt M
  have hYp : IsProjOver Y.s := by
    rw [← hov]
    exact GlobalTheory.isProjOver_comp_of_finite (Ow w) M.X Y.X π M.s hfin hMp
  have hYs : ∃ d, SmoothOfRelativeDimension d Y.s := by
    have h0 := het'
    rw [Etale.iff_smoothOfRelativeDimension_zero] at h0
    have key : ∀ n, SmoothOfRelativeDimension n M.s → SmoothOfRelativeDimension (0 + n) (π ≫ M.s) :=
      fun n hn => inferInstance
    rw [← hov]
    exact ⟨_, key _ M.smooth⟩
  refine ⟨⟨⟨h3, hcq, hcp, hsup, hpow⟩, M, Y, π, hov, m, hfin, het', fun k => ?_, fun k => ?_⟩⟩
  · exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).1 hYp
  · obtain ⟨d, hd⟩ := hYs
    exact (hPP q _ (Ow w) S.b N₁ h3 hcq Y.X Y.s Y.univ k).2 d hd
end

