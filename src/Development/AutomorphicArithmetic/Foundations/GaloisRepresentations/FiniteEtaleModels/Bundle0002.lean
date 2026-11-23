module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IsGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsQuotTriv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.BaseOnto
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.crystallineComparison.Mod (Std)

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)}

structure Ext (S : Site gb w q r 𝔴 𝔫) (N₁ : ℕ) (𝔟 : Ideal (𝓞 D.F)) : Type 1 where
  lev : LevAt D q r 𝔴 N₁ 𝔟
  M : Model S.b N₁
  Y : EtModel S.b N₁ 𝔟 1
  π : Y.X ⟶ M.X
  ov : π ≫ M.s = Y.s
  mπ : ObjMap Y.univ M.univ π
  fin : IsFinite π
  et : Etale π
  proj : ∀ k, IsProjOver ((GlobalTheory.KS.pow Y.univ.A k).hom ≫ Y.s)
  dim : ∀ k, ∃ d, SmoothOfRelativeDimension d ((GlobalTheory.KS.pow Y.univ.A k).hom ≫ Y.s)

abbrev Ext.site {S : Site gb w q r 𝔴 𝔫} {N₁ : ℕ} {𝔟 : Ideal (𝓞 D.F)} (X : FiniteEtaleModels.Ext S N₁ 𝔟) :
    Site gb w q r 𝔴 (Ideal.span {(N₁ : 𝓞 D.F)} * 𝔟) where
  atq := S.atq
  sp := S.sp
  f := S.f
  b := S.b
  mat := S.mat
  N₀ := N₁
  𝔞 := 𝔟
  std := { S.std with three := X.lev.1, cop := X.lev.2.1 }
  qmem := S.qmem
  norm := S.norm
  cop := X.lev.2.2.1
  sup := X.lev.2.2.2.1
  upow := X.lev.2.2.2.2
  lev := rfl
  M := X.M
  Y := X.Y
  π := X.π
  ov := X.ov
  mπ := X.mπ
  fin := X.fin
  et := X.et
  proj := X.proj
  dim := X.dim

variable {S : Site gb w q r 𝔴 𝔫} {N₁ N₂ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)}

structure Down (X₁ : FiniteEtaleModels.Ext S N₁ 𝔟₁) (X₂ : FiniteEtaleModels.Ext S N₂ 𝔟₂) : Type where
  t : X₁.Y.X ⟶ X₂.Y.X
  ov : t ≫ X₂.Y.s = X₁.Y.s
  Φ : X₁.Y.univ.A.left ⟶ X₂.Y.univ.A.left
  w : Φ ≫ X₂.Y.univ.A.hom = X₁.Y.univ.A.hom ≫ t

def Down.pw {X₁ : FiniteEtaleModels.Ext S N₁ 𝔟₁} {X₂ : FiniteEtaleModels.Ext S N₂ 𝔟₂} (d : Down X₁ X₂) (k : ℕ) :
    (GlobalTheory.KS.pow X₁.Y.univ.A k).left ⟶ (GlobalTheory.KS.pow X₂.Y.univ.A k).left := GlobalTheory.KS.powMap d.t d.Φ d.w k

def Down.Extends {X₁ : FiniteEtaleModels.Ext S N₁ 𝔟₁} {X₂ : FiniteEtaleModels.Ext S N₂ 𝔟₂} (d : Down X₁ X₂)
    {k : ℕ} {T : KS L gb k} {h : G.GAf} {M₁ M₂ : Lv p}
    (W : Wit T h M₁ M₂) {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F} (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) : Prop :=
  C₁.j ≫ d.t = W.π ≫ C₂.j ∧ C₁.m.φ ≫ d.Φ = W.ψ.left ≫ W.φ.φ ≫ C₂.m.φ

end

def StepA : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ κ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : FiniteEtaleModels.Ext S (N₀ * κ) 𝔟₁) (X₂ : FiniteEtaleModels.Ext S N₀ 𝔟₂),
    𝔟₁ ≤ 𝔟₂ → ∀ (h : G.GAf), Integ L h →
    (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = κ • v) → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂),
      ∃ d : Down X₁ X₂, d.Extends W C₁ C₂

def StepF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ κ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : FiniteEtaleModels.Ext S (N₀ * κ) 𝔟₁) (X₂ : FiniteEtaleModels.Ext S N₀ 𝔟₂), 𝔟₁ ≤ 𝔟₂ →
    ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F), X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ → M₂.1 ∣ M₁.1 →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T 1 M₁ M₂),
      ∃ d : Down X₁ X₂, d.Extends W C₁ C₂ ∧ IsFinite d.t ∧ Etale d.t ∧ IsPullback d.Φ X₁.Y.univ.A.hom X₂.Y.univ.A.hom d.t

def StepB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (N₀ : ℕ) (𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)) (X₁ : FiniteEtaleModels.Ext S N₀ 𝔟₁) (X₂ : FiniteEtaleModels.Ext S N₀ 𝔟₂)
    (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal → uId D q r ≤ 𝔴' →
    𝔟₁ ≤ 𝔟₂ * 𝔴' → i ≤ D.n → ∀ (h : G.GAf), Integ L h → IsTjElt L q r 𝔴' i h → ∀ (M₁ M₂ : Lv p) (c₁ c₂ : ℕ) (a₁ a₂ : 𝓞 D.F),
    X₁.site.Num M₁.1 c₁ a₁ → X₂.site.Num M₂.1 c₂ a₂ → Ideal.absNorm 𝔴' ^ i ∣ M₁.1 →
    ∀ (C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁) (C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂) (W : Wit T h M₁ M₂),
      ∃ d : Down X₁ X₂, d.Extends W C₁ C₂

def BaseFet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (M : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num M.1 c a → ∀ C : S.Cl (T.M M).univ c a,
      IsFinite (pullback.lift C.j (T.M M).s C.ov) ∧ Etale (pullback.lift C.j (T.M M).s C.ov)

def BaseOnto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (M : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num M.1 c a → ∀ (C : S.Cl (T.M M).univ c a) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      (y : Sp Ω ⟶ S.Y.X) (σ : Sp Ω ⟶ Sp E), y ≫ S.Y.s = σ ≫ spMap (algebraMap (Ow w) E) → ∃ x, x ≫ C.j = y ∧ x ≫ (T.M M).s = σ

def LiftSys : Prop :=
  ∀ (q : ℕ) [Fact q.Prime] (D : Datum q), D.m = 1 → ∀ (r : ℤ), (q : ℤ) ∣ r ^ 2 - D.tr * r + D.nm → ∀ (𝔞 : Ideal (𝓞 D.F)) (N₀ : ℕ),
    (∃ e : ℕ, ES.uIdeal D r ^ e ≤ 𝔞) → N₀.Coprime q → ∀ g₀ : LevGrp D 𝔞 1, ∃ g : ℕ → D.La →+ D.La,
      (∀ n, 0 < n → ∀ (c : D.O) x, ∃ z, g n (c • x) = c • g n x + n • z) ∧ (∀ n, 0 < n → ∀ x, ∃ y z, g n y = x + n • z) ∧
      (∀ n, 0 < n → ∀ x z, g n x = n • z → ∃ v, x = n • v) ∧ (∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ D.EF (g n x) (g n y) - D.EF x y) ∧
      (∀ n m, 0 < n → 0 < m → ∀ x, ∃ z, g (n * m) x = g n x + n • z) ∧ (∀ x, ∃ z, g N₀ x = x + N₀ • z) ∧
      ∀ n, 0 < n → ((n : ℕ) : 𝓞 D.F) ∈ 𝔞 → ∀ x, (wSub D 𝔞 1).mkQ (g n x) = g₀ ((wSub D 𝔞 1).mkQ x)

def QuotOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫) (k : ℕ) (T : KS L gb k)
    (K₀ : Subgroup G.GAf), IsLev L 𝔫 K₀ → ∀ (M : Lv p) (c : ℕ) (a : 𝓞 D.F), S.Num M.1 c a → ∀ C : S.Cl (T.M M).univ c a,
      IsQuot T.X (Ow w) K₀ (T.lev M) ((GlobalTheory.KS.pow S.Y.univ.A k).hom ≫ S.Y.s) (S.pi T C)

def ExtEx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p), Sc D G → ∀ (E : Type) [Field E] [NumberField E] (gb : GBase D.toG E)
    (w : HeightOneSpectrum (𝓞 E)) (q : ℕ) [Fact q.Prime] (r : ℤ) (𝔴 𝔫 : Ideal (𝓞 D.F)) (S : Site gb w q r 𝔴 𝔫)
    (N₁ : ℕ) (𝔟 : Ideal (𝓞 D.F)), LevAt D q r 𝔴 N₁ 𝔟 → Nonempty (FiniteEtaleModels.Ext S N₁ 𝔟)

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LSigFin
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

def LGrp : Prop :=
  ∀ (Γ : Type) [Group Γ] (K K₀ K₁ KN KM : Subgroup Γ), KM ≤ KN → KN ≤ K → KN ≤ K₀ → KM ≤ K₁ → K₁ ≤ K₀ →
    (∀ u ∈ K₀, ∀ v ∈ KM, u * v * u⁻¹ ∈ KM) → (∀ u ∈ K₀, ∃ a ∈ K, a ∈ K₀ ∧ a⁻¹ * u ∈ K₁) → ∀ b₀ ∈ K, ∀ u ∈ K₀,
    Nat.card {cn : (K ⧸ KN.subgroupOf K) × (KN ⧸ KM.subgroupOf KN) //
      b₀⁻¹ * (cn.1.out : Γ) * (cn.2.out : Γ) * u⁻¹ ∈ K₁} = KM.relIndex (K ⊓ K₁)

def LPts : Prop :=
  ∀ (E : Type) [Field E] (Γ : Type) [Group Γ] (X : G3.Tower (Sp E) Γ) (O : Type) [CommRing O] [Algebra O E] (K K₀ K₁ KN : Subgroup Γ)
    (M N : X.ι) (Y Y' : Scheme.{0}) (pY : Y ⟶ Spec (CommRingCat.of O)) (π : X.Z N ⟶ Y) (π' : X.Z M ⟶ Y') (s : Y' ⟶ Y) (a b : _),
    X.K N = KN → KN ≤ K → KN ≤ K₀ → K₁ ≤ K₀ → π ≫ pY = X.q N ≫ gen O E →
    IsQuot X O K₀ M pY (π' ≫ s) → IsQuot X O K₁ M (s ≫ pY) π' → X.tr M N 1 a b ≫ π = π' ≫ s →
    (∀ u ∈ K₀, ∃ a ∈ K, a ∈ K₀ ∧ a⁻¹ * u ∈ K₁) → ∀ b₀ ∈ K,
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ X.Z N) (y' : sp Ω ⟶ Y'), y' ≫ s = z ≫ π →
      Nat.card {cx : (K ⧸ KN.subgroupOf K) × (sp Ω ⟶ X.Z M) // cx.2 ≫ X.tr M N 1 a b = z ∧ b₀⁻¹ * (cx.1.out : Γ) ∈ K₀ ∧
        ∀ a' b', cx.2 ≫ X.tr M M (b₀⁻¹ * (cx.1.out : Γ)) a' b' ≫ π' = y'} = (X.K M).relIndex (K ⊓ K₁)

def LSigPt : Prop :=
  ∀ (I : Type) (W : Scheme.{0}) (Ω : Type) [Field Ω],
    Function.Bijective fun x : I × (sp Ω ⟶ W) => x.2 ≫ Sigma.ι (fun _ : I => W) x.1

def LSigFin : Prop :=
  ∀ (I : Type) [Finite I] (W Z : Scheme.{0}) (f : W ⟶ Z), IsFinite f → Etale f →
    IsFinite (Sigma.desc fun _ : I => f) ∧ Etale (Sigma.desc fun _ : I => f)

def LCount : Prop :=
  ∀ (I B : Type) [Finite I] [Finite B] (W Z Y Y' : Scheme.{0}) (cls : I → B) (f : W ⟶ Z) (kc : I → (W ⟶ Y')) (π : Z ⟶ Y) (s : Y' ⟶ Y) (m : ℕ),
    IsFinite f → Etale f → IsFinite s → Etale s →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : sp Ω ⟶ Z) (b : B) (y' : sp Ω ⟶ Y'), y' ≫ s = z ≫ π →
      Nat.card {cx : I × (sp Ω ⟶ W) // cx.2 ≫ f = z ∧ cls cx.1 = b ∧ cx.2 ≫ kc cx.1 = y'} = m) →
    ∀ h : (Sigma.desc fun _ : I => f) ≫ π = (Sigma.desc fun c : I => kc c ≫ Sigma.ι (fun _ : B => Y') (cls c)) ≫ Sigma.desc fun _ : B => s,
      FEt (pullback.lift _ _ h) m

def LIdx : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ), 0 < N → (L.KN N).relIndex (L.KN 1) ≠ 0

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PDegGen
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

theorem degGen_holds : DegGen := by
  intro E _ Γ _ X O _ _ K₀ K₁ i Y Y' pY π' s h01 hQ0 hQ1 Ω _ _ y σ hy
  let T : ∀ u : Γ, u ∈ K₀ → (X.Z i ⟶ X.Z i) := fun u hu => X.tr i i u (hQ0.adm u hu).1 (hQ0.adm u hu).2
  have hT : ∀ a b (ha : a ∈ K₀) (hb : b ∈ K₀), T a ha ≫ T b hb = T (b * a) (K₀.mul_mem hb ha) :=
    fun a b ha hb => X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  have hTc : ∀ a b (ha : a ∈ K₀) (hb : b ∈ K₀), a = b → T a ha = T b hb := by
    rintro a b ha hb rfl
    rfl
  have h1 : ∀ h1 : (1 : Γ) ∈ K₀, T 1 h1 = 𝟙 _ := fun h1 => X.tr_self _ _ _ _ (X.K i).one_mem
  have hinv1 : ∀ w (hw : w ∈ K₀), w ∈ K₁ → T w hw ≫ π' = π' := fun w hw hw1 =>
    hQ1.inv w hw1 _ _
  have hinv0 : ∀ w (hw : w ∈ K₀), T w hw ≫ π' ≫ s = π' ≫ s := fun w hw => hQ0.inv w hw _ _
  obtain ⟨x, hx⟩ := hQ0.onto Ω y σ hy
  let f : K₀ → { y' // y' ≫ s = y } := fun u =>
    ⟨x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ π', by
      rw [Category.assoc, Category.assoc, hinv0 _ (K₀.inv_mem u.2), hx]⟩
  have key : ∀ u v : K₀, f u = f v ↔ (u : Γ)⁻¹ * v ∈ K₁ := by
    intro u v
    constructor
    · intro h
      have hv : (x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2)) ≫ π' = (x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2)) ≫ π' := by
        simpa [f] using congrArg Subtype.val h
      obtain ⟨w, hw1, a, b, he⟩ := hQ1.fib Ω _ _ hv
      have hw0 := h01 hw1
      have he' : x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2) = x ≫ T (w * (u : Γ)⁻¹) (K₀.mul_mem hw0 (K₀.inv_mem u.2)) := by
        rw [he, Category.assoc]
        exact congrArg (x ≫ ·) (hT _ _ (K₀.inv_mem u.2) hw0)
      have hm : v.1 * w * (u : Γ)⁻¹ ∈ K₀ := K₀.mul_mem (K₀.mul_mem v.2 hw0) (K₀.inv_mem u.2)
      have hfix : x ≫ T (v.1 * w * (u : Γ)⁻¹) hm = x := by
        have p1 : w * (u : Γ)⁻¹ ∈ K₀ := K₀.mul_mem hw0 (K₀.inv_mem u.2)
        have e1 : T (v.1 * w * (u : Γ)⁻¹) hm = T (w * (u : Γ)⁻¹) p1 ≫ T v.1 v.2 :=
          (hTc _ _ hm (K₀.mul_mem v.2 p1) (by group)).trans (hT _ _ p1 v.2).symm
        have e2 : T (v : Γ)⁻¹ (K₀.inv_mem v.2) ≫ T v.1 v.2 = 𝟙 _ :=
          (hT _ _ (K₀.inv_mem v.2) v.2).trans
            ((hTc _ _ (K₀.mul_mem v.2 (K₀.inv_mem v.2)) K₀.one_mem (by group)).trans (h1 K₀.one_mem))
        rw [e1, ← Category.assoc, ← he', Category.assoc, e2, Category.comp_id]
      have ht := hQ0.free _ hm _ _ Ω x hfix
      have hc := (hQ0.adm _ (K₀.inv_mem u.2)).2 _ ht
      have := K₁.mul_mem (hQ1.le hc) (K₁.inv_mem hw1)
      convert this using 1
      group
    · intro h
      apply Subtype.ext
      show x ≫ T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ π' = x ≫ T (v : Γ)⁻¹ (K₀.inv_mem v.2) ≫ π'
      have hk : ((u : Γ)⁻¹ * v)⁻¹ ∈ K₀ := h01 (K₁.inv_mem h)
      have e : T (v : Γ)⁻¹ (K₀.inv_mem v.2) = T (u : Γ)⁻¹ (K₀.inv_mem u.2) ≫ T _ hk :=
        (hTc _ _ (K₀.inv_mem v.2) (K₀.mul_mem hk (K₀.inv_mem u.2)) (by group)).trans
          (hT _ _ (K₀.inv_mem u.2) hk).symm
      rw [e, Category.assoc, hinv1 _ hk (K₁.inv_mem h)]
  let F : K₀ ⧸ K₁.subgroupOf K₀ → { y' // y' ≫ s = y } := Quotient.lift f (fun u v huv =>
    (key u v).2 (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp huv)))
  have hinj : Function.Injective F := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H u =>
      induction b using QuotientGroup.induction_on with
      | H v =>
        intro h
        exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ((key u v).1 h))
  have hsurj : Function.Surjective F := by
    rintro ⟨y', hy'⟩
    obtain ⟨x', hx'⟩ := hQ1.onto Ω y' σ (by rw [← Category.assoc, hy', hy])
    obtain ⟨u, hu, a, b, hxe⟩ := hQ0.fib Ω x x' (by rw [hx, ← Category.assoc, hx', hy'])
    refine ⟨QuotientGroup.mk ⟨u⁻¹, K₀.inv_mem hu⟩, ?_⟩
    apply Subtype.ext
    show x ≫ T (u⁻¹)⁻¹ (K₀.inv_mem (K₀.inv_mem hu)) ≫ π' = y'
    rw [hTc (u⁻¹)⁻¹ u (K₀.inv_mem (K₀.inv_mem hu)) hu (inv_inv u), ← Category.assoc]
    rw [← hx', hxe]
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact (Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)).symm

end UpperTheory.Gal.FiniteEtaleModels
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFEtExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem card_of_pb {K : Type} [Field K] [IsAlgClosed K] {Y Y' : Scheme.{0}} (s : Y' ⟶ Y)
    (x : Spec (CommRingCat.of K) ⟶ Y) (B : Type) [CommRing B] [Algebra K B] [Module.Finite K B] [Algebra.Etale K B]
    (f : Spec (CommRingCat.of B) ⟶ Y')
    (h : IsPullback f (Spec.map (CommRingCat.ofHom (algebraMap K B))) s x) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} = Module.finrank K B := by
  have hcomp : ∀ g : B →ₐ[K] K, Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 _ := by
    intro g
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (g : B →+* K).comp (algebraMap K B) = RingHom.id K := by
      ext z; simp
    rw [this]
    exact Spec.map_id _
  let F : (B →ₐ[K] K) → {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} := fun g =>
    ⟨Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f, by
      rw [Category.assoc, h.w, ← Category.assoc, hcomp, Category.id_comp]⟩
  have hF : Function.Bijective F := by
    constructor
    · intro g g' e
      have e1 : Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f = Spec.map (CommRingCat.ofHom (g' : B →+* K)) ≫ f :=
        congrArg Subtype.val e
      have e2 : Spec.map (CommRingCat.ofHom (g : B →+* K)) = Spec.map (CommRingCat.ofHom (g' : B →+* K)) :=
        h.hom_ext e1 ((hcomp g).trans (hcomp g').symm)
      have e3 := Spec.map_injective e2
      have e4 : (g : B →+* K) = (g' : B →+* K) := by
        simpa using congrArg CommRingCat.Hom.hom e3
      exact AlgHom.coe_ringHom_injective e4
    · rintro ⟨y, hy⟩
      let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of B) := h.lift y (𝟙 _) (by rw [hy, Category.id_comp])
      have ht1 : t ≫ f = y := h.lift_fst _ _ _
      have ht2 : t ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) = 𝟙 _ := h.lift_snd _ _ _
      let g0 : CommRingCat.of B ⟶ CommRingCat.of K := Spec.preimage t
      have hg0 : Spec.map g0 = t := Spec.map_preimage t
      have hc : CommRingCat.ofHom (algebraMap K B) ≫ g0 = 𝟙 _ := by
        apply Spec.map_injective
        rw [Spec.map_comp, hg0, ht2, Spec.map_id]
      let g : B →ₐ[K] K := { g0.hom with
        commutes' := fun r => by
          have := congrArg (fun u => u.hom r) hc
          simpa using this }
      have hgg : CommRingCat.ofHom (g : B →+* K) = g0 := by
        ext z; rfl
      refine ⟨g, Subtype.ext ?_⟩
      change Spec.map (CommRingCat.ofHom (g : B →+* K)) ≫ f = y
      rw [hgg, hg0, ht1]
  rw [← Nat.card_congr (Equiv.ofBijective F hF)]
  obtain ⟨hfin, hsp⟩ := UpperTheory.Gal.crystallineComparison.splitsField_of K B K inferInstance
  haveI := Fintype.ofFinite (B →ₐ[K] K)
  let e : (TensorProduct K K B) ≃ₗ[K] ((B →ₐ[K] K) → K) :=
    LinearEquiv.ofBijective (UpperTheory.Gal.crystallineComparison.splitMap (fun z : B →ₐ[K] K => z)).toLinearMap hsp
  have e1 := e.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, (TensorProduct.lid K B).finrank_eq] at e1
  exact e1.symm

private theorem card_lifts {K : Type} [Field K] [IsAlgClosed K] {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) [IsFinite s] [Etale s]
    (x : Spec (CommRingCat.of K) ⟶ Y) (z : Spec (CommRingCat.of K)) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ Y' // y ≫ s = x} = Scheme.Hom.finrank s (x z) := by
  haveI : Etale (pullback.snd s x) := inferInstance
  haveI : IsAffine (pullback s x) := isAffine_of_isAffineHom (pullback.snd s x)
  let e := (pullback s x).isoSpec
  let φ : CommRingCat.of K ⟶ Γ(pullback s x, ⊤) := Spec.preimage (e.inv ≫ pullback.snd s x)
  have hφ : Spec.map φ = e.inv ≫ pullback.snd s x := Spec.map_preimage _
  have hfinφ : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hetφ : Etale (Spec.map φ) := by rw [hφ]; infer_instance
  letI : Algebra K Γ(pullback s x, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite K Γ(pullback s x, ⊤) := ((IsFinite.SpecMap_iff φ).mp hfinφ : φ.hom.Finite)
  haveI : Algebra.Etale K Γ(pullback s x, ⊤) :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hetφ : φ.hom.Etale)
  have hpb : IsPullback (e.inv ≫ pullback.fst s x) (Spec.map φ) s x := by
    rw [hφ]
    exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e.symm (by simp) (by simp)
  rw [card_of_pb s x Γ(pullback s x, ⊤) _ hpb]
  have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb z
  rw [← h1]
  have h2 := Scheme.Hom.finrank_SpecMap_algebraMap K Γ(pullback s x, ⊤) z
  rw [Module.rankAtStalk_eq_finrank_of_free] at h2
  exact h2.symm

theorem UpperTheory.Gal.FiniteEtaleModels.fEtExt_holds :
    FEtExt := by
  intro O E _ _ _ _ _ Y Y' pY s d hfl hfin het hd
  have key : ∀ y₀ : Y, Scheme.Hom.finrank s y₀ = d := by
    intro y₀
    have hg := Flat.generalizingMap pY
    have hsp : (⊥ : PrimeSpectrum O) ⤳ pY y₀ := (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
    obtain ⟨y₁, h1, h2⟩ := hg hsp
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point Y y₁
    let pt : Spec (CommRingCat.of k) := (⊥ : PrimeSpectrum k)
    have ha1 : a pt = y₁ := by
      have : a pt ∈ Set.range a := ⟨pt, rfl⟩
      rw [ha] at this
      exact this
    let f : CommRingCat.of O ⟶ CommRingCat.of k := Spec.preimage (a ≫ pY)
    have hf : Spec.map f = a ≫ pY := Spec.map_preimage _
    have hpt : (Spec.map f) pt = (⊥ : PrimeSpectrum O) := by
      rw [hf, Scheme.Hom.comp_apply, ha1, h2]
    have hinj : Function.Injective f.hom := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro r hr
      have h3 : r ∈ (PrimeSpectrum.comap f.hom (⊥ : PrimeSpectrum k)).asIdeal := by
        simpa [PrimeSpectrum.comap_asIdeal] using hr
      have h4 : PrimeSpectrum.comap f.hom (⊥ : PrimeSpectrum k) = (⊥ : PrimeSpectrum O) := hpt
      rw [h4] at h3
      simpa using h3
    let g : E →+* k := IsFractionRing.lift hinj
    let σ : sp k ⟶ sp E := Spec.map (CommRingCat.ofHom g)
    have hσ : a ≫ pY = σ ≫ gen O E := by
      rw [← hf, gen, ← Spec.map_comp]
      congr 1
      ext z
      simp [g]
    have h3 := hd k a σ hσ
    rw [card_lifts s a pt, ha1] at h3
    have h5 := h1.map (Scheme.Hom.isLocallyConstant_finrank s).continuous
    rw [← h3]
    exact (specializes_iff_eq.mp h5).symm
  refine ⟨hfin, het, fun K _ _ x => ?_⟩
  rw [card_lifts s x (⊥ : PrimeSpectrum K), key]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PSigmaFEt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

private theorem exists_sigma_point {W : Scheme.{0}} {I : Type} (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ ∐ fun _ : I => W) :
    ∃ (i : I) (y' : Spec (CommRingCat.of K) ⟶ W), y' ≫ Sigma.ι (fun _ : I => W) i = y := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk (fun _ : I => W)).surjective (y pt)
  rw [sigmaMk_mk] at hw
  refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q pt]
  exact ⟨w, hw⟩

private theorem card_sigma_fibre {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Type) (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ Y) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y') // y ≫ (Sigma.desc fun _ : I => s) = x} =
      Nat.card I * Nat.card {y' : Spec (CommRingCat.of K) ⟶ Y' // y' ≫ s = x} := by
  let F : I × {y' : Spec (CommRingCat.of K) ⟶ Y' // y' ≫ s = x} →
      {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y') // y ≫ (Sigma.desc fun _ : I => s) = x} :=
    fun p => ⟨p.2.1 ≫ Sigma.ι (fun _ : I => Y') p.1, by simp [p.2.2]⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ h
      have h' : a ≫ Sigma.ι (fun _ : I => Y') i = b ≫ Sigma.ι (fun _ : I => Y') j :=
        congrArg Subtype.val h
      obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
      have hij : i = j := by
        by_contra hne
        exact (isEmpty_of_commSq_sigmaι_of_ne ⟨h'⟩ hne).false pt
      subst hij
      have hab : a = b := (cancel_mono _).1 h'
      subst hab
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨i, y', rfl⟩ := exists_sigma_point K y
      exact ⟨⟨i, y', by simpa using hy⟩, rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective F hF)).symm

theorem UpperTheory.Gal.FiniteEtaleModels.sigmaFEt_holds :
    SigmaFEt := by
  intro Y Y' s d I _ h
  obtain ⟨hf, he, hc⟩ := h
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hfold := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y' k
  let i : (∐ fun _ : I => Y') ≅ ∐ fun _ : Fin k => Y' :=
    Sigma.whiskerEquiv (f := fun _ : I => Y') (g := fun _ : Fin k => Y') e fun _ => Iso.refl Y'
  have hd : (Sigma.desc fun _ : I => s) = i.hom ≫ (Sigma.desc fun _ : Fin k => 𝟙 Y') ≫ s := by
    apply Sigma.hom_ext
    intro a
    simp [i]
  refine ⟨by rw [hd]; infer_instance, ?_, fun K _ _ x => ?_⟩
  · have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ => inferInstance
  · rw [card_sigma_fibre, hc K x]
end

