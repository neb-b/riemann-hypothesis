module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PQuotOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem conj_congOne {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {u v : G.GAf} {N : ℕ}
    (hu : u ∈ L.KN 1) (hv : L.CongOne N v) : L.CongOne N (u * v * u⁻¹) := by
  intro z hz
  have hu' : L.CongOne 1 u ∧ L.CongOne 1 u⁻¹ := hu
  obtain ⟨w1, hw1, e1⟩ := hu'.2 z hz
  have hz' : L.actG u⁻¹ z ∈ LaHat D := by
    rw [e1, one_smul]
    exact add_mem hz hw1
  obtain ⟨w2, hw2, e2⟩ := hv _ hz'
  obtain ⟨w3, hw3, e3⟩ := hu'.1 w2 hw2
  refine ⟨L.actG u w2, ?_, ?_⟩
  · rw [e3, one_smul]
    exact add_mem hw2 hw3
  · have key : L.actG u (L.actG u⁻¹ z) = z := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e2, map_add (f := _), map_nsmul, key]

private theorem inAf_mem' {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

private theorem cl_cast {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E]
    {gb : GBase D.toG E} {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)}
    (S : Site gb w q r 𝔴 𝔫) {k : ℕ} (T : KS L gb k) (M : Lv p) {c c' : ℕ} {a a' : 𝓞 D.F} (hc : c' = c) (ha : a' = a)
    (C : S.Cl (T.M M).univ c a) : ∃ C' : S.Cl (T.M M).univ c' a', S.pi T C' = S.pi T C := by
  subst hc ha
  exact ⟨C, rfl⟩

theorem UpperTheory.Gal.FiniteEtaleModels.quotOf_holds :
    PowCart → PiInv → PiFet → PiSep → CongCRT → BaseOnto → QuotOf := by
  intro hPC hPI hPF hPS hCRT hBO p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK M c a hNum C
  have hM := hNum.1
  have hGen := hNum.2
  let N0 : Lv p := ⟨S.N₀, S.std.three, S.cop⟩
  have hMpos : 0 < M.1 := by have := M.2.1; omega
  have hdvd : S.N₀ ∣ M.1 := ⟨c, hM⟩
  have hup := S.upow
  have hcop : S.N₀.Coprime q := S.std.cop
  have hK₀le : K₀ ≤ L.KN S.N₀ := by
    have key : ∀ g, g ∈ K₀ → L.CongOne S.N₀ g := fun g hg => by
      have h := (hK g).1 hg
      have h2 := h.2
      rw [S.lev] at h2
      exact (((hCRT p D G L q r S.N₀ S.𝔞 hcop hup g (integ_of_mem h.1)).1).1 h2).1
    exact fun g hg => ⟨key g hg, key _ (inv_mem hg)⟩
  have hKM : L.KN M.1 ≤ K₀ := by
    intro g hg
    have h1 : g ∈ L.KN 1 := KN_anti (one_dvd _) hg
    have hcrt := hCRT p D G L q r S.N₀ S.𝔞 hcop hup g (integ_of_mem h1)
    have h2 : L.CongOne S.N₀ g := (KN_anti hdvd hg).1
    have h3 : CongId L S.𝔞 g := (hcrt.2 a M.1 hMpos M.2.2 hGen).2 fun y => hg.1 _ (inAf_mem' D _)
    exact (hK g).2 ⟨h1, by rw [S.lev]; exact hcrt.1.2 ⟨h2, h3⟩⟩
  have hX : T.X.K (T.lev M) = L.KN M.1 := T.K_eq M
  have hX0 : T.X.K (T.lev N0) = L.KN S.N₀ := T.K_eq N0
  refine ⟨?ov, ?le, ?idx, ?adm, ?inv, ?fib, ?free, ?onto⟩
  · obtain ⟨e, -⟩ := hPF p D G L E gb w q r 𝔴 𝔫 S k T M c a hNum C
    exact e
  · rw [hX]; exact hKM
  · rw [hX]
    have h := T.X.idx (T.lev M) (T.lev N0)
    rw [hX, hX0] at h
    exact fun e => h (Subgroup.relIndex_eq_zero_of_le_right hK₀le e)
  · intro u hu
    have hu1 := ((hK u).1 hu).1
    refine ⟨(T.Δ_eq u).2 (integ_of_mem hu1), fun v hv => ?_⟩
    rw [hX] at hv ⊢
    refine ⟨conj_congOne L hu1 hv.1, ?_⟩
    have e : (u * v * u⁻¹)⁻¹ = u * v⁻¹ * u⁻¹ := by group
    rw [e]; exact conj_congOne L hu1 hv.2
  · intro u hu x y
    obtain ⟨C', hC'⟩ := cl_cast (a' := ((1 : ℕ) : 𝓞 D.F) * a) S T M (_root_.mul_one c) (by simp) C
    have h := hPI p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK M M 1 c a (_root_.mul_one _).symm hNum C' C u hu x y
    rwa [hC'] at h
  · intro Ω _ _ x y h
    exact hPS p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK M c a hNum C Ω x y h
  · intro u hu x y Ω _ _ z hz
    exact T.X.free _ (T.lev N0) (by rw [hX, hX0]; exact KN_anti hdvd) u (by rw [hX0]; exact hK₀le hu) x y Ω z hz
  · intro Ω _ _ y σ hy
    obtain ⟨x₀, hx₀, -⟩ := hBO p D G L hSc E gb w q r 𝔴 𝔫 S k T M c a hNum C Ω (y ≫ (GlobalTheory.KS.pow S.Y.univ.A k).hom) σ
      (by simpa using hy)
    have hpb := (hPC _ _ _ (T.M M).univ.A S.Y.univ.A S.Y.univ.A C.j (𝟙 _) C.m.φ (𝟙 _) C.m.cart.1.w (by simp) k).1 C.m.cart.1
    refine ⟨hpb.lift y x₀ hx₀.symm ≫ (T.e M).inv, ?_⟩
    simp only [Site.pi, Cls.pw, Category.assoc, Iso.inv_hom_id_assoc]
    exact hpb.lift_fst _ _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫} {k : ℕ} {T : KS L gb k}
  {N₀ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₀ 𝔟₁} {X₂ : Ext S N₀ 𝔟₂} {𝔴' : Ideal (𝓞 D.F)} {i : ℕ} {h : G.GAf} {M₁ M₂ : Lv p}
  {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}

structure BPt (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
    {f : X₁.Y.X ⟶ X₂.M.X} (mf : ObjMap X₁.Y.univ X₂.M.univ f) {c : ℕ} (Tj : TjD X₂.M r 𝔴' i c) : Type where
  y : (T.M M₁).X ⟶ Tj.Y
  ys : y ≫ Tj.s = C₁.j ≫ f
  yt : y ≫ Tj.t = W.π ≫ C₂.j ≫ X₂.π
  fa : (T.M M₁).univ.A.left ⟶ Tj.o.A.left
  fb : W.o.A.left ⟶ Tj.o'.A.left
  ca : IsGrpPullback (T.M M₁).univ.A Tj.o.A y fa
  cb : IsGrpPullback W.o.A Tj.o'.A y fb
  sq : fa ≫ Tj.ψ.left = W.ψ.left ≫ fb
  ms : fa ≫ Tj.ms.φ = C₁.m.φ ≫ mf.φ
  mt : fb ≫ Tj.mt.φ = W.φ.φ ≫ C₂.m.φ ≫ X₂.mπ.φ

end

def IsogG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R' : Type) [CommRing R'] [Algebra ℚ R'] (gb : GBase D.toG R')
    (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴₀ 𝔴 : Ideal (𝓞 D.F)) (atq : AtPrime D q r 𝔴₀)
    (sp : Nonempty ((D.O ⊗[ℤ] ℤ_[q]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[q]))), D.m = 1 → 𝔴.IsMaximal → uId D q r ≤ 𝔴 →
    ∀ (R : Type) [CommRing R] (b : Base (datAt atq sp) R) (N₀ : ℕ), N₀.Coprime q → ∀ (i e : ℕ), Ideal.absNorm 𝔴 ^ i = q ^ e →
    ∀ (h u : G.GAf), IsTjElt L q r 𝔴 i h → Integ L h → u ∈ L.KN N₀ → ∀ (N' N : Lv p) (c' c : ℕ), N'.1 = N₀ * c' → N.1 = N₀ * c →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R') (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L (h * u) o' o ψ →
    ∀ (s₀ : X ⟶ Sp R) (o₁ o₂ : Obj b N₀ s₀) (n₁ : QMap (D := datAt atq sp) (gb := gb) o' o₁ (𝟙 _) c')
      (n₂ : QMap (D := datAt atq sp) (gb := gb) o o₂ (𝟙 _) c),
    ∃ ψ₀ : o₁.A ⟶ o₂.A, n₁.φ ≫ ψ₀.left = ψ.left ≫ n₂.φ ∧ ES.IsPIsog (q ^ e) o₁ o₂ ψ₀ ∧ ES.IsTj (D := datAt atq sp) r 𝔴 i o₁ o₂ ψ₀

def TjExG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ),
    3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j e : ℕ), w.IsMaximal →
    ES.uIdeal D r ≤ w → j ≤ D.n → (0 < j → 0 < e) → ∀ M : Model b N, Nonempty (TjD M r w j (p ^ e))

def SecInjG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
    ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j e : ℕ), w.IsMaximal → ES.uIdeal D r ≤ w → j ≤ D.n → (0 < j → 0 < e) →
    ∀ (M : Model b N) (T : TjD M r w j (p ^ e)) (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
      (x : Sp K ⟶ M.X) (y y' : Sp K ⟶ T.Y), y ≫ T.s = x → y' ≫ T.s = x →
    (∀ g : Over.mk x ⟶ M.univ.A, ES.KilledBy M.univ w g → (KerAt T y g.left ↔ KerAt T y' g.left)) → y = y'

def DescExt : Prop :=
  ∀ (O E : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [IsFractionRing O E]
    (V X Y B : Scheme.{0}) (s : X ⟶ Sp O) (σ : V ⟶ Sp E) (j : V ⟶ X) (ov : j ≫ s = σ ≫ spMap (algebraMap O E)), Smooth s →
    IsFinite (pullback.lift j σ ov) → Etale (pullback.lift j σ ov) →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X) (τ : Sp Ω ⟶ Sp E), x ≫ s = τ ≫ spMap (algebraMap O E) → ∃ v, v ≫ j = x ∧ v ≫ σ = τ) →
    ∀ (f : X ⟶ B) (g : Y ⟶ B) (y : V ⟶ Y), IsFinite g → y ≫ g = j ≫ f →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ V), x ≫ j = x' ≫ j → x ≫ y = x' ≫ y) → ∃ y' : X ⟶ Y, j ≫ y' = y ∧ y' ≫ g = f

def LatB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (q : ℕ) (r : ℤ) (𝔴 𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (i : ℕ) (h : G.GAf),
    AtPrime D q r 𝔴 → IsTjElt L q r 𝔴 i h → Integ L h → 𝔟₁ ≤ 𝔟₂ * 𝔴 → (∃ e : ℕ, uId D q r ^ e ≤ 𝔟₁) →
    ∀ (M₁ M₂ : Lv p) (a₁ a₂ : 𝓞 D.F), IsGen a₁ M₁.1 𝔟₁ → IsGen a₂ M₂.1 𝔟₂ → ∀ y : D.La, ∃ x : D.La, ∃ v ∈ LaHat D,
      L.actG h (inAf D (M₂.1 • algebraMap (𝓞 D.F) D.O a₁ • x)) = inAf D (M₁.1 • algebraMap (𝓞 D.F) D.O a₂ • y) + (M₁.1 * M₂.1) • v

def EtaPtB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R)
    (h : G.GAf) (X : Scheme.{0}) (s : X ⟶ Sp R) (N' N : Lv p) (o' : GObj gb N'.1 s) (o : GObj gb N.1 s) (ψ : o'.A ⟶ o.A), IsTrans L h o' o ψ →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : Sp Ω ⟶ X) (x y : D.La),
    (∃ v ∈ LaHat D, L.actG h (inAf D (N.1 • x)) = inAf D (N'.1 • y) + (N'.1 * N.1) • v) →
    toUnit (Over.mk z) ≫ o'.eta x ≫ ψ = toUnit (Over.mk z) ≫ o.eta y

def BRead : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    Nonempty (BPt C₁ C₂ W mf Tj)

def BKer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    ∀ (P : BPt C₁ C₂ W mf Tj) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ (T.M M₁).X), x ≫ C₁.j = x' ≫ C₁.j → x ≫ P.y = x' ≫ P.y

def BLev : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : Ext S N₀ 𝔟₁) (X₂ : Ext S N₀ 𝔟₂) (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂)
      (f : X₁.Y.X ⟶ X₂.M.X) (mf : ObjMap X₁.Y.univ X₂.M.univ f), f ≫ X₂.M.s = X₁.Y.s →
    ∀ (e : ℕ), Ideal.absNorm 𝔴' ^ i = q ^ e → (0 < i → 0 < e) → ∀ (Tj : TjD X₂.M r 𝔴' i (q ^ e)),
    ∀ (P : BPt C₁ C₂ W mf Tj) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ (T.M M₁).X), x ≫ C₁.j = x' ≫ C₁.j → x ≫ P.y = x' ≫ P.y →
      x ≫ W.π ≫ C₂.j = x' ≫ W.π ≫ C₂.j

end UpperTheory.Gal.FiniteEtaleModels
end
end

