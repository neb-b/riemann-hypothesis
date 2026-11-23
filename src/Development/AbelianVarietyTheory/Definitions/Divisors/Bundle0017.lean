module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero
section
noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

section act
variable {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
  {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}

theorem IsEtLev.congr (h : IsEtLev o w0 r lv) {x y : D.La} (hxy : x - y ∈ wSub D w0 r) : lv x = lv y := by
  have : x = y + (x - y) := by abel
  rw [this, h.1, h.2.2.1 _ hxy, _root_.mul_one]

theorem IsEtLev.congr_mk (h : IsEtLev o w0 r lv) {x y : D.La}
    (hxy : Submodule.Quotient.mk (p := wSub D w0 r) x = Submodule.Quotient.mk y) : lv x = lv y :=
  h.congr ((Submodule.Quotient.eq _).1 hxy)

def liftAct (g : LevGrp D w0 r) (x : D.La) : D.La :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose

theorem mk_liftAct (g : LevGrp D w0 r) (x : D.La) :
    Submodule.Quotient.mk (p := wSub D w0 r) (liftAct g x) = g (Submodule.Quotient.mk x) :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose_spec

end act

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
section
noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def IsHecke (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : Obj b (N * k) s) (o' : Obj b N s)
    (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta (g x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (heckeSub o g N) (fun h => (transl h.1).left) ψ.left ∧
    Nonempty (LBIso (lbPow o.P (k ^ 2 / c)) (o'.P.pull (sq2 ψ))) ∧ c ∣ k ^ 2

def IsHeckeMap (g : D.La →ₗ[D.O] D.La) (c k N : ℕ) (F : RepFam b N) (F' : RepFam b (N * k))
    (π : F'.X ⟶ F.X) : Prop :=
  π ≫ F.s = F'.s ∧ ∃ (o' : Obj b N F'.s) (ψ : F'.univ.A ⟶ o'.A), IsHecke g c k N F'.univ o' ψ ∧
    Nonempty (ObjMap o' F.univ π)

end GlobalTheory.UPel.HT.Hecke
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Dieu

section Isogeny

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {G H : PDivGroup p k}

def IsIsog (f : G ⟶ H) : Prop :=
  ∃ (n : ℕ) (g : H ⟶ G), f ≫ g = (p : ℤ_[p]) ^ n • 𝟙 G ∧ g ≫ f = (p : ℤ_[p]) ^ n • 𝟙 H

def HasLogDeg (f : G ⟶ H) (e : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n, N ≤ n → Module.finrank k (G.A n ⧸ kerIdeal (f.app n)) = p ^ e

end Isogeny

structure IsDM {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    {N : Type} [AddCommGroup N] [Module (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (V : N →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)] N) : Prop where
  free : Module.Free (WittVector p k) N
  finite : Module.Finite (WittVector p k) N
  F_V : ∀ x, F (V x) = p • x
  V_F : ∀ x, V (F x) = p • x

theorem p_eq_zero (p : ℕ) (k : Type) [Field k] [CharP k p] : (p : k) = 0 := CharP.cast_eq_zero k p

structure Base (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop) : Type 1 where

  M : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), P k G →
    ModuleCat.{0} (WittVector p k)

  smap : ∀ {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (h' : P k' G') (h : P k G),
    SemiHom σ G' G → (M G h →+ M G' h')

  red : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G),
    M G h →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] PDivGroup.RigExt G
  free : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G),
    Module.Free (WittVector p k) (M G h)
  finite : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G),
    Module.Finite (WittVector p k) (M G h)
  red_surjective : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G),
    Function.Surjective (red G h)
  red_eq_zero : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G)
    (m : M G h), red G h m = 0 ↔ ∃ n, m = p • n
  smap_smul : ∀ {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (h' : P k' G') (h : P k G) (s : SemiHom σ G' G)
    (a : WittVector p k) (m : M G h), smap h' h s (a • m) = WittVector.map σ a • smap h' h s m
  smap_id : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (m : M G h),
    smap h h (SemiHom.ofHom (𝟙 G)) m = m
  smap_add : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G H : PDivGroup p k} (hG : P k G) (hH : P k H)
    (f g : G ⟶ H) (m : M H hH),
    smap hG hH (SemiHom.ofHom (f + g)) m = smap hG hH (SemiHom.ofHom f) m + smap hG hH (SemiHom.ofHom g) m
  smap_comp : ∀ {k k' k'' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Field k''] [CharP k'' p] [PerfectRing k'' p] {σ : k →+* k'} {τ : k' →+* k''}
    {υ : k →+* k''} {G'' : PDivGroup p k''} {G' : PDivGroup p k'} {G : PDivGroup p k} (h'' : P k'' G'')
    (h' : P k' G') (h : P k G) (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G),
    (∀ n a, u.app n a = t.app n (s.app n a)) → ∀ m : M G h, smap h'' h u m = smap h'' h' t (smap h' h s m)
  red_smap : ∀ {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p]
    {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (h' : P k' G') (h : P k G) (s : SemiHom σ G' G)
    (m : M G h), red G' h' (smap h' h s m) = SemiHom.rig s (red G h m)

namespace Base

variable {p : ℕ} [Fact p.Prime] {P Q : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop} (B : Base p P)
  {k : Type} [Field k] [CharP k p] [PerfectRing k p]

def map {G H : PDivGroup p k} (hG : P k G) (hH : P k H) (f : G ⟶ H) :
    B.M H hH →ₗ[WittVector p k] B.M G hG where
  toFun := B.smap hG hH (SemiHom.ofHom f)
  map_add' := map_add _
  map_smul' a m := by rw [B.smap_smul, WittVector.map_id]

def F (G : PDivGroup p k) (h : P k G) :
    B.M G h →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] B.M G h where
  toFun := B.smap h h (absFrob (p_eq_zero p k) G)
  map_add' := map_add _
  map_smul' a m := by
    rw [B.smap_smul, WittVector.frobenius_eq_map_frobenius]
    congr 3
    exact RingHom.ext fun r => frobRing_apply _ r

def Katz : Prop :=
  ∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) {d : ℕ}
      (c : Katz.Chart G d) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (hμ : Katz.IsLaw μ), c.IsLawOf μ →
      (B.M G h ≃ₗ[WittVector p k] Katz.Mod p hμ),
    ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) {d : ℕ}
      (c : Katz.Chart G d) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (hμ : Katz.IsLaw μ) (hc : c.IsLawOf μ),
      KatzF.IsF p hμ (fun x => e G h c hμ hc (B.F G h ((e G h c hμ hc).symm x))) ∧
      ∀ (H : PDivGroup p k) (h' : P k H) {d' : ℕ} (c' : Katz.Chart H d')
        {ν : Fin d' → MvPowerSeries (Fin d' ⊕ Fin d') k} (hν : Katz.IsLaw ν) (hc' : c'.IsLawOf ν) (f : G ⟶ H)
        (φ : Fin d' → MvPowerSeries (Fin d) k), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → c.IsMapOf c' f φ →
        KatzF.IsPull p hμ hν φ (fun x => e G h c hμ hc (B.map h h' f ((e H h' c' hν hc').symm x)))

def EtDual (C : Base p Q) : Prop :=
  ∃ e : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (hd : Q k G.dual),
      G.IsEt → (B.M G h ≃ₗ[WittVector p k] Module.Dual (WittVector p k) (C.M G.dual hd)),
    ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : P k G) (hd : Q k G.dual)
      (hG : G.IsEt),
      (∀ x y, e G h hd hG (B.F G h x) (C.F G.dual hd y) = p * WittVector.frobenius (e G h hd hG x y)) ∧
      ∀ (H : PDivGroup p k) (h' : P k H) (hd' : Q k H.dual) (hH : H.IsEt) (f : G ⟶ H) x y,
        e G h hd hG (B.map h h' f x) y = e H h' hd' hH x (C.map hd' hd (dualHom G H f) y)

end Base

structure Theory (p : ℕ) [Fact p.Prime] : Type 1 where

  base : Base p fun _ _ _ => True
  katz : base.Katz
  etDual : base.EtDual base

  V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k),
    base.M G trivial →ₛₗ[((WittVector.frobeniusEquiv p k).symm : WittVector p k →+* WittVector p k)]
      base.M G trivial
  F_V : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (m : base.M G trivial),
    base.F G trivial (V G m) = p • m
  V_F : ∀ {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (m : base.M G trivial),
    V G (base.F G trivial m) = p • m

namespace Theory

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k k' : Type} [Field k] [CharP k p] [PerfectRing k p]
  [Field k'] [CharP k' p] [PerfectRing k' p]

abbrev M (G : PDivGroup p k) : Type := T.base.M G trivial

abbrev map {G H : PDivGroup p k} (f : G ⟶ H) : T.M H →ₗ[WittVector p k] T.M G := T.base.map trivial trivial f

abbrev smap {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (s : SemiHom σ G' G) : T.M G →+ T.M G' :=
  T.base.smap trivial trivial s

abbrev F (G : PDivGroup p k) :
    T.M G →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] T.M G := T.base.F G trivial

abbrev red (G : PDivGroup p k) :
    T.M G →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] PDivGroup.RigExt G :=
  T.base.red G trivial

end Theory

section Examples

end Examples

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

def SRelBy {h n' n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B'}
    {s : S ⟶ Sp B} (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (d' d : ℕ) (f : S' ⟶ S) (φ : c'.A.left ⟶ c.A.left) :
    Prop :=
  IsGrpPullback c'.A c.A f φ ∧ (∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂)) ∧
    ∀ a, (c'.lev a ^ d').left ≫ φ = f ≫ (c.lev a ^ d).left

def SRel {h n' n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B'}
    {s : S ⟶ Sp B} (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (d' d : ℕ) (f : S' ⟶ S) : Prop :=
  ∃ φ, SRelBy c' c d' d f φ

theorem sRel_one_one_iff {h n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}}
    {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} (c' : SiegPre h n ζ' s') (c : SiegPre h n ζ s) (f : S' ⟶ S) :
    SRel c' c 1 1 f ↔ SiegPB c' c f := by
  unfold SRel SRelBy SiegPB
  simp only [pow_one]
  constructor
  · rintro ⟨φ, hpb, ⟨φ₂, hsq, hiso⟩, hlev⟩
    exact ⟨φ, φ₂, hpb, hsq, hiso, hlev⟩
  · rintro ⟨φ, φ₂, hpb, hsq, hiso, hlev⟩
    exact ⟨φ, hpb, ⟨φ₂, hsq, hiso⟩, hlev⟩

structure SQuot {h N : ℕ} {o' : Type} [CommRing o'] {ζ' : o'} (F : SFam h N ζ') (n : ℕ) {o : Type} [CommRing o] (ζ : o)
    (j : o →+* o') where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h n ζ s

  princ : univ.Principal

  π : F.X ⟶ X

  base : π ≫ s = F.s ≫ spMap j

  fin : IsFinite π

  etale : Etale π

  onto : Surjective π

  low : SRel F.univ univ (N / n) 1 π

  fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'),
    y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → y ≫ π = y' ≫ π

end GlobalTheory.SiegLev
end
end

