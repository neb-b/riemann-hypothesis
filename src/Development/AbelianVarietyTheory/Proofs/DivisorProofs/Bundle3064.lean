module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2474
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDividingLabelsIffClassZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep.IntLabel

section
variable {G X : Type} [AddCommGroup G] [AddCommGroup X] {N : ℕ} {Y : G → X → Prop}

theorem yy_zero (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) : Y 0 0 := by
  obtain ⟨mu, hmu⟩ := h1 0
  have h2 := h4 0 0 mu mu hmu hmu
  rw [add_zero] at h2
  have hc := (h3 0 mu (mu + mu) hmu).1 h2
  refine (h3 0 mu 0 hmu).2 ?_
  obtain ⟨w, hw⟩ := hc
  have e : mu = N • w := add_left_cancel (a := mu) (by simpa using hw)
  exact ⟨-w, by simp [e]⟩

theorem yy_neg (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a : G} {mu : X} (ha : Y a mu) :
    Y (-a) (-mu) := by
  obtain ⟨mu', h'⟩ := h1 (-a)
  have h0 := h4 a (-a) mu mu' ha h'
  rw [add_neg_cancel] at h0
  have hc := (h3 0 0 (mu + mu') (yy_zero h1 h3 h4)).1 h0
  refine (h3 (-a) mu' (-mu) h').2 ?_
  obtain ⟨w, hw⟩ := hc
  rw [zero_add] at hw
  refine ⟨-w, ?_⟩
  rw [smul_neg, ← hw]
  abel

theorem yy_sub (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) {a b : G} {mu nu : X} (ha : Y a mu)
    (hb : Y b nu) : Y (a - b) (mu - nu) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h4 _ _ _ _ ha (yy_neg h1 h3 h4 hb)

theorem yy_nsmul (h1 : ∀ a, ∃ mu, Y a mu) (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (k : ℕ) {a : G} {mu : X} (ha : Y a mu) :
    Y (k • a) (k • mu) := by
  induction k with
  | zero => simpa using yy_zero h1 h3 h4
  | succ k ih => rw [succ_nsmul, succ_nsmul]; exact h4 _ _ _ _ ih ha

theorem mem_closure_iff (p J : ℕ) (hJ : 2 ≤ J) (hN : N = p ^ J) (hG : ∀ a : G, N • a = 0)
    (htor : ∀ b : G, p • b = 0 → ∃ c, b = p ^ (J - 1) • c) (htf : ∀ x : X, p ^ (J - 1) • x = 0 → x = 0)
    (h1 : ∀ a, ∃ mu, Y a mu) (h2 : ∀ mu, ∃ a, Y a mu)
    (h3 : ∀ a mu mu', Y a mu → (Y a mu' ↔ CongMod N mu' mu))
    (h4 : ∀ a a' mu mu', Y a mu → Y a' mu' → Y (a + a') (mu + mu')) (S : Set G) (hS : ∀ a ∈ S, Y a 0)
    (hT : ∀ a, Y a 0 → ∃ b, p • b = 0 ∧ a + b ∈ S) (a : G) : a ∈ AddSubgroup.closure S ↔ Y a 0 := by
  constructor
  · intro ha
    induction ha using AddSubgroup.closure_induction with
    | mem x hx => exact hS x hx
    | zero => exact yy_zero h1 h3 h4
    | add x y _ _ hx hy => simpa using h4 x y 0 0 hx hy
    | neg x _ hx => simpa using yy_neg h1 h3 h4 hx
  · intro ha
    obtain ⟨b, hb, hab⟩ := hT a ha
    have hYb : Y b 0 := by simpa using yy_sub h1 h3 h4 (hS _ hab) ha
    obtain ⟨c, rfl⟩ := htor b hb
    obtain ⟨muc, hc⟩ := h1 c
    have hcong := (h3 _ _ _ (yy_nsmul h1 h3 h4 (p ^ (J - 1)) hc)).1 hYb
    have hw : ∃ w : X, muc = p • w := by
      obtain ⟨w, hw⟩ := hcong
      refine ⟨-w, ?_⟩
      have e : p ^ (J - 1) • (muc + p • w) = 0 := by
        rw [smul_add, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN]
        exact hw.symm
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      exact htf _ e
    obtain ⟨w, hmu⟩ := hw
    obtain ⟨c', hc'⟩ := h2 w
    have hk : Y (c - p • c') 0 := by
      have := yy_sub h1 h3 h4 hc (yy_nsmul h1 h3 h4 p hc')
      rwa [← hmu, sub_self] at this
    obtain ⟨bk, hbk, hkS⟩ := hT _ hk
    have hbk0 : p ^ (J - 1) • bk = 0 := by
      obtain ⟨e, he⟩ : ∃ e, J - 1 = e + 1 := ⟨J - 2, by omega⟩
      rw [he, pow_succ, mul_smul, hbk, smul_zero]
    have key : p ^ (J - 1) • c = p ^ (J - 1) • ((c - p • c') + bk) := by
      rw [smul_add, hbk0, add_zero, smul_sub, smul_smul, ← pow_succ, Nat.sub_add_cancel (by omega), ← hN, hG, sub_zero]
    have hbcl : p ^ (J - 1) • c ∈ AddSubgroup.closure S := by
      rw [key]; exact nsmul_mem (AddSubgroup.subset_closure hkS) _
    have e : a = (a + p ^ (J - 1) • c) - p ^ (J - 1) • c := by abel
    rw [e]
    exact sub_mem (AddSubgroup.subset_closure hab) hbcl

theorem zmod_tors {p J M : ℕ} (hp : 0 < p) (hJ : 1 ≤ J) (hM : M = p ^ J) (x : ZMod M) (hx : p • x = 0) :
    ∃ y : ZMod M, x = p ^ (J - 1) • y := by
  subst hM
  haveI : NeZero (p ^ J) := ⟨pow_ne_zero _ hp.ne'⟩
  have h1 : p ^ J ∣ p * x.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod (p ^ J)) (p ^ J)]
    push_cast
    rw [ZMod.natCast_zmod_val]
    rwa [nsmul_eq_mul] at hx
  have h2 : p ^ (J - 1) ∣ x.val := by
    have e : p ^ J = p * p ^ (J - 1) := by rw [← pow_succ']; congr 1; omega
    have h1' : p * p ^ (J - 1) ∣ p * x.val := by rw [← e]; exact h1
    exact Nat.dvd_of_mul_dvd_mul_left hp h1'
  obtain ⟨q, hq⟩ := h2
  refine ⟨(q : ZMod (p ^ J)), ?_⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [hq, nsmul_eq_mul]
  push_cast
  ring

end
end GlobalTheory.GSep.IntLabel

namespace GlobalTheory.GSep


open GlobalTheory.GSep.IntLabel in
theorem mem_HH_iff_yy_zero : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ ↔ 𝔪.YY a 0 := by
  intro I X₁ z₁ act x₀ hx₀ V _ _ _ ev X _ t δ 𝔪 a
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.GSep.Labels.yy_hom I X₁ z₁ act V ev X t δ 𝔪
  obtain ⟨j, hj, hr⟩ := X₁.ρ.r_eq
  have hp : 0 < X₁.ρ.n := X₁.ρ.n_prime.pos
  have hk := X₁.ρ.two_le
  have hN : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j + X₁.ρ.k * 2) := by rw [hr, X₁.ρ.N_eq, pow_add, pow_mul]
  have hJ : 2 ≤ j + X₁.ρ.k * 2 := by omega
  have hG : ∀ b : X₁.S.Gam, (X₁.S.r * X₁.S.N) • b = 0 := fun b => by
    funext v
    simp [nsmul_eq_mul]
  have htor : ∀ b : X₁.S.Gam, X₁.ρ.n • b = 0 → ∃ c : X₁.S.Gam, b = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • c := by
    intro b hb
    have hv : ∀ v, ∃ y : ZMod (X₁.S.r * X₁.S.N), b v = X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • y := fun v =>
      zmod_tors hp (by omega) hN (b v) (by simpa using congrFun hb v)
    choose c hc using hv
    exact ⟨c, funext fun v => by simpa using hc v⟩
  have htf : ∀ x : X, X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) • x = 0 → x = 0 := by
    intro x hx
    have hq : X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) ≠ 0 := pow_ne_zero _ hp.ne'
    have he : ((X₁.ρ.n ^ (j + X₁.ρ.k * 2 - 1) : ℕ) : ℤ) • 𝔪.e₈ x = 0 := by
      rw [natCast_zsmul, ← map_nsmul, hx, map_zero]
    have h0 : 𝔪.e₈ x = 0 := (smul_eq_zero.1 he).resolve_left (by exact_mod_cast hq)
    exact 𝔪.e₈.injective (h0.trans (map_zero _).symm)
  rw [ThetaSys.HH]
  exact mem_closure_iff (X₁.ρ.n) (j + X₁.ρ.k * 2) hJ hN hG htor htf h1 h2 h3 h4 _
    (fun b hb => _root_.GlobalTheory.GSep.DivInt.label_zero_of_mem_supI I X₁ z₁ act V ev X t δ 𝔪 b hb)
    (fun b hb => _root_.GlobalTheory.GSep.TorTrans.exists_translate_mem_supI I X₁ z₁ act V ev X t δ 𝔪 x₀ hx₀ b hb) a

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionEqOfValuesAtLabelTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.GSep.GMem

theorem sec_eq_of_valAt : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)) (th th₂ : SecA 𝔪.A (FractionRing V) 1),
  (∀ a, (fr a).IsGen) → (∀ a, ValAt th (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) →
  (∀ a, ValAt th₂ (x a) (fr a) (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩)) → th₂ = th := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 x fr th th₂ _ h₁ h₂
  obtain ⟨b, hb⟩ := GlobalTheory.GSep.GMem.exists_th_ne_zero I X₁ z₁ act V ev Y t δ 𝔪
  set y := 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ with hy
  have ht : (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th) ≠ 0 := by
    intro h0
    have hz : ValAt (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th) (x b) (fr b) 0 := by
      rw [h0]; exact GlobalTheory.TermsMove.valAt_zero (x b) (fr b)
    exact hb (GlobalTheory.TermsMove.valAt_unique (h₁ b) hz)
  obtain ⟨c, hc⟩ := GlobalTheory.TermsMove.exists_eq_smul ht (show GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1 from th₂)
  have hz0 : ValAt (0 : GlobalTheory.TorsionExt.AbSec 𝔪.A (FractionRing V) 1) (x b) (fr b) 0 :=
    GlobalTheory.TermsMove.valAt_zero (x b) (fr b)
  have hl := GlobalTheory.TermsMove.valAt_lin (h₁ b) hz0 c
  rw [add_zero, add_zero, ← hc] at hl
  have e := GlobalTheory.TermsMove.valAt_unique (h₂ b) hl
  have c1 : c = 1 := by
    have : (c - 1) * y = 0 := by rw [sub_mul, ← e]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hb
  rw [c1, one_smul] at hc
  exact hc

end GlobalTheory.GSep.GMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPullOfPrincipalisation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.SemiPullAll

theorem isometric_pull_pull {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}
    {s : Z ⟶ Sp k} (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = s) (c : Z ⟶ X)
    (hc : c ≫ p = s) (e : g ≫ f = c) : ((L.pull f hf).pull g hg).Isometric (L.pull c hc) := by
  subst e
  have R : GlobalTheory.TwistTop.Refines ((L.pull f hf).pull g hg) (L.pull (g ≫ f) hc)
      (fun c => c PUnit.unit) 0 := by
    refine ⟨fun c y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) a, ?_, ?_⟩
    · intro W r z c c' hc₁ hc₂
      have h₁ := Set.mem_iInter.1 hc₁ PUnit.unit
      have h₂ := Set.mem_iInter.1 hc₂ PUnit.unit
      refine (gm_pull_g _ g r z c c' hc₁ hc₂).trans ((gm_pull_g _ f (r ≫ g) z _ _ h₁ h₂).trans ?_)
      refine Eq.trans ?_ (gm_pull_g _ (g ≫ f) r z (c PUnit.unit) (c' PUnit.unit)
        (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₁ a) (Set.mem_iInter.2 fun a => Set.mem_iInter.1 h₂ a)).symm
      rw [Category.assoc]
    · intro σ c y hy
      refine (((L.pull f hf).φ σ).pull_φ g hg c y).trans (((L.φ σ).pull_φ f hf _ _).trans ?_)
      refine Eq.trans ?_ (((L.φ σ).pull_φ (g ≫ f) hc (c PUnit.unit) y).symm.trans (add_zero _).symm)
      exact congrArg _ (Subtype.ext (Category.assoc _ _ _))
  exact HermLB.isometric_of_chart _ R.le (fun x => R.g Z (𝟙 Z) x) fun σ c y hy =>
    ((R.φ σ c y hy).trans (add_zero _)).symm

theorem semiPull_of_principalisation : GlobalTheory.Published.Principalisation → SemiPull := by
  intro hP k _ X Y p q D E hp hq π hπ L hL
  have := hp.isIntegral
  have := hq.isIntegral
  obtain ⟨X', _, ρ, hρ, hsm, hgen, hdeg⟩ := GlobalTheory.GenRes.exists_birational_genSmooth hP k X p D hp
  obtain ⟨V, hV, het⟩ := _root_.GlobalTheory.GenEtale.exists_opens_etale k X X' p (ρ ≫ p) D hp hρ ρ rfl hgen (by rw [hdeg]; exact one_ne_zero)
  have h₁ : (L.pull ρ rfl).SemiPos D := _root_.GlobalTheory.SemiPosUp.semiPos_pull_of_etale k X X' p (ρ ≫ p) D hp hρ ρ rfl V hV het L hL
  have hπp : IsArithVar (π ≫ p) E := by rw [hπ]; exact hq
  obtain ⟨Y', _, g, π', hcomm, hY', hggen, hgdeg⟩ := _root_.GlobalTheory.CoverLift.exists_cover_over_modification k X X' Y p D E ρ π hp hρ hπp hgen
  have hY'q : IsArithVar (g ≫ q) E := by rw [← hπ]; exact hY'
  have e₁ : π' ≫ ρ ≫ p = g ≫ q := by rw [← Category.assoc, hcomm, Category.assoc, hπ]
  have e₂ : (g ≫ π) ≫ p = g ≫ q := by rw [Category.assoc, hπ]
  have h₂ : ((L.pull ρ rfl).pull π' e₁).SemiPos E :=
    _root_.GlobalTheory.HermLB.semiPos_pull_of_genSmooth k X' Y' (ρ ≫ p) (g ≫ q) D E hsm π' e₁ (L.pull ρ rfl) h₁
  have iso : ((L.pull ρ rfl).pull π' e₁).Isometric ((L.pull π hπ).pull g rfl) :=
    (isometric_pull_pull L ρ rfl π' e₁ (g ≫ π) e₂ hcomm).trans
      (isometric_pull_pull L π hπ g rfl (g ≫ π) e₂ rfl).symm
  have h₃ : ((L.pull π hπ).pull g rfl).SemiPos E :=
    HermLB.Isometric.semiPos _ _ E iso h₂
  obtain ⟨W, hW, hWet⟩ := _root_.GlobalTheory.GenEtale.exists_opens_etale k Y Y' q (g ≫ q) E hq hY'q g rfl hggen hgdeg
  exact _root_.GlobalTheory.SemiPosEtale.semiPos_of_pull_etale k Y Y' q (g ≫ q) E hq hY'q g rfl W hW hWet (L.pull π hπ) h₃

end GlobalTheory.SemiPullAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExpansionTermsEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.ExpUnique

theorem expandsF_unique {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (w : W0 U) (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s s₂ : Fam D.toPre F k)
    (h : U.ExpandsF F k w t s) (h₂ : U.ExpandsF F k w t s₂) : s = s₂ := by
  obtain ⟨σ, hσ, hG⟩ := h
  obtain ⟨σ₂, hσ₂, hG₂⟩ := h₂
  have hf : ∀ j, σ.f j = σ₂.f j := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.Tor.sec_ext_val U.LG.isLB (fun y J hJ => ?_)
    choose J₁ hJ₁ using fun χ : _ ⟶ A.A.left => exists_chart A.isLB (χ y)
    have e₁ := GlobalTheory.Jets.sval_of_isoRelM hσ (𝟙 _) y hJ hJ₁
    have e₂ := GlobalTheory.Jets.sval_of_isoRelM hσ₂ (𝟙 _) y hJ hJ₁
    exact e₁.trans e₂.symm
  obtain rfl : σ = σ₂ := by
    rcases σ with ⟨a, _⟩
    rcases σ₂ with ⟨b, _⟩
    obtain rfl : a = b := funext hf
    rfl
  exact GlobalTheory.expandsG_unique R I hR D A G U k F σ s s₂ hG hG₂

end GlobalTheory.GSep.ExpUnique

theorem GlobalTheory.GSep.ExpUnique.coef_eq_of_expandsF : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (k : ℕ) (th : SecA 𝔪.A (FractionRing V) k) (s s₂ : Fam 𝔪.D.toPre (FractionRing V) k),
  w₀.IsGen → 1 ≤ k → 𝔪.U.ExpandsF (FractionRing V) k w₀ th s → 𝔪.U.ExpandsF (FractionRing V) k w₀ th s₂ →
  ∀ (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) k g.b), w.IsGen → ∀ χ, coef s₂ g w χ = coef s g w χ := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ k th s s₂ _ _ hs hs₂ g w _ χ
  rw [GlobalTheory.GSep.ExpUnique.expandsF_unique (GlobalTheory.TorRef.admissibleBase_of_completeNormalLocalCharZero 𝔪.cn) 𝔪.U.toUnifPre (FractionRing V) k w₀ th
    s s₂ hs hs₂]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberLiesOverRescaleFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep

theorem over_rescale : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (g : GtPtF 𝔪.D.toPre (FractionRing V)) (w w' : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (e e' : FrAt x) (l : FractionRing V), l ≠ 0 → (∀ z J, Good 𝔪.A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val) → (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w (𝟙 _) z J).val = cstH (R := V) z l * (val w' (𝟙 _) z J).val) → 𝔪.Over' w₀ g w x e → 𝔪.Over' w₀ g w' x e' := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ g w w' x e e' l hl he hw H k hk wk' hwk' hgen s s' v hs hv
  have hlk : l ^ k ≠ 0 := pow_ne_zero k hl
  obtain ⟨wk, hwkg, hwk⟩ := GlobalTheory.UT.TorsionValue.exists_frm_scale wk' hgen hlk
  have h₁ : ValAt s x e (l ^ k * v) := fun z J hJ => by
    rw [hv z J hJ]
    have r₁ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    have r₂ : Geo.Tor.val (powFrame 𝔪.A.A 𝔪.A.L x e' (k : ℤ)) (𝟙 _) z J = Geo.Tor.val e' (𝟙 _) z J ^ (k : ℤ) :=
      map_zpow _ _ _
    rw [r₁, r₂, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, he z J hJ]
    simp only [id, GlobalTheory.Poinc.TorsRatio.cst_eq_cstK, map_mul, map_pow]
    ring
  have h₂ := H k hk wk (fun z J hJ => Units.ext (by
    rw [hwk z J hJ, hwk' z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hw z J hJ, mul_pow,
      GlobalTheory.UT.CoefBasic.cst_eq, map_pow])) hwkg s s' _ hs h₁
  have h₃ := GlobalTheory.Poinc.Sep.sumF_const_mul (l ^ k)⁻¹ h₂
  simpa only [GlobalTheory.UT.TorsionValue.coef_scale hgen hwk, inv_mul_cancel_left₀ hlk] using h₃

end GlobalTheory.GSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberTorsionFrameUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep
open GlobalTheory.UT.CoefBasic

noncomputable section
namespace GlobalTheory.GSep.FrameUniq

section Gen
variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F] {D : DegPre R}

theorem exists_ratio {b b' : TF (R := R) F ⟶ D.P.A} (h : b' = b) {w : Frm D F 1 b} {w' : Frm D F 1 b'}
    (hw : w.IsGen) (hw' : w'.IsGen) : ∃ c : F, c ≠ 0 ∧ ∀ z J, Good D.P.L z J →
      (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val := by
  subst h
  exact exists_frame_ratio hw hw'

theorem coef_congr' {k : ℕ} {g g₂ : GtPtF D F} {w : Frm D F k g.b} {w₂ : Frm D F k g₂.b} (hw : w.IsGen)
    (hb : g₂.b = g.b) (hs : ∀ χ z J, Good D.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J)
    (hv : ∀ z J, Good D.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J) (s : Fam D F k) (χ : D.X) :
    coef s g₂ w₂ χ = coef s g w χ := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  have e : lift (𝟙 (TF (R := R) F)) g₂.b = lift (𝟙 (TF (R := R) F)) g.b := by rw [hb]
  rw [hs χ z J hJ, hv z J hJ, e]
  exact a
end Gen

theorem frame_val_eq : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ) (w₀ : W0 𝔪.U.toUnifPre) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A) (fr : FrAt x)
  (g g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w : Frm 𝔪.D.toPre (FractionRing V) 1 g.b) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
  w₀.IsGen → fr.IsGen →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g o ∧ o.IsZero) → w.IsGen → 𝔪.Over' w₀ g w x fr →
  (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) → w₂.IsGen → 𝔪.Over' w₀ g₂ w₂ x fr →
  g₂.b = g.b → (∀ χ z J, Good 𝔪.D.toPre.P.L z J → val (g₂.s χ) (𝟙 _) z J = val (g.s χ) (𝟙 _) z J) →
  ∀ z J, Good 𝔪.D.toPre.P.L z J → val w₂ (𝟙 _) z J = val w (𝟙 _) z J := by
  intro I X₁ z₁ act V _ _ _ ev Y _ t δ 𝔪 w₀ x fr g g₂ w w₂ hw₀ hfr _ hw hO _ hw₂ hO₂ hb hs
  have hadm : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  obtain ⟨c, hc, hcv⟩ := exists_ratio hb hw hw₂
  have pow_one_of : ∀ k : ℕ, 4 ≤ k → c ^ k = 1 := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    obtain ⟨wk, hwkg, hwk⟩ := TorsionValue.exists_frm_pow w hw k
    obtain ⟨wk₂, hwk₂g, hwk₂⟩ := TorsionValue.exists_frm_pow w₂ hw₂ k
    obtain ⟨w', hw'g, hw'⟩ := TorsionValue.exists_frm_scale wk hwkg (pow_ne_zero k hc)
    obtain ⟨th, a, ha0, ha⟩ := GlobalTheory.UT.NonVan.exists_sec_ne_zero GlobalTheory.firstFiveLaws V 𝔪.A (FractionRing V) k hk x fr hfr
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF GlobalTheory.globalFns_holds 𝔪.U (FractionRing V) (k := k) hk1 w₀ hw₀
    have hexp : 𝔪.U.ExpandsF (FractionRing V) k w₀ th (e th) := (he th _).2 rfl
    have H1 := hO k hk1 wk hwk hwkg th (e th) a hexp ha
    have H2 := hO₂ k hk1 wk₂ hwk₂ hwk₂g th (e th) a hexp ha
    have hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → val wk₂ (𝟙 _) z J = val w' (𝟙 _) z J := by
      intro z J hJ
      apply Units.ext
      rw [hwk₂ z J hJ, hw' z J hJ, hwk z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hcv z J hJ, mul_pow,
        cst_eq, cst_eq, map_pow]
    have e2 : coef (e th) g₂ wk₂ = fun χ => c ^ k * coef (e th) g wk χ := funext fun χ => by
      rw [coef_congr' hw'g hb hs hv, TorsionValue.coef_scale hwkg hw' (e th) χ]
    rw [e2] at H2
    have hl := ((GlobalTheory.AdicSum.sumF_calculus V (maximalIdeal V) hadm (FractionRing V) _ (coef (e th) g wk)
      (coef (e th) g wk) a a).2.1 H1 H1 (c ^ k - 1))
    have ee : (fun χ => (c ^ k - 1) * coef (e th) g wk χ + coef (e th) g wk χ) = fun χ => c ^ k * coef (e th) g wk χ :=
      funext fun χ => by ring
    rw [ee] at hl
    have := (GlobalTheory.AdicSum.sumF_calculus V (maximalIdeal V) hadm (FractionRing V) _ _ (coef (e th) g wk) a
      ((c ^ k - 1) * a + a)).1 H2 hl
    have h0 : (c ^ k - 1) * a = 0 := by linear_combination -this
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right ha0)
  have h4 := pow_one_of 4 le_rfl
  have h5 := pow_one_of 5 (by norm_num)
  have hc1 : c = 1 := by linear_combination (-c) * h4 + h5
  intro z J hJ
  apply Units.ext
  rw [hcv z J hJ, hc1, cst_eq, map_one, _root_.one_mul]

end GlobalTheory.GSep.FrameUniq
end
end

