module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsUnitNatOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

private theorem isUnit_nat_of {E : Type} [Field E] [CharZero E] {V : Scheme.{0}} (s : V ⟶ Sp E) (n : ℕ) (hn : n ≠ 0) :
    IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
  have hE : IsUnit ((n : E)) := (Nat.cast_ne_zero.mpr hn).isUnit
  have h1 : IsUnit ((n : Γ(Sp E, ⊤))) := by
    have := hE.map (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom
    simpa using this
  have := h1.map s.appTop.hom
  simpa using this

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'}

private theorem qmap_cast {N₁ N c : ℕ} {V Y : Scheme.{0}} {s : V ⟶ Sp R'} {t : Y ⟶ Sp R} {a : GObj gb N₁ s} {u : Obj b N t}
    {f f' : V ⟶ Y} (h : f = f') (n : QMap a u f c) : ∃ n' : QMap a u f' c, n'.φ = n.φ := by
  subst h
  exact ⟨n, rfl⟩

private theorem rigid_of (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q) {S₁ S₂ : Scheme.{0}}
    {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {f f' : S₁ ⟶ S₂}
    (m : ObjMap o₁ o₂ f) (m' : ObjMap o₁ o₂ f') (h : f = f') : m.φ = m'.φ := by
  subst h
  exact (hO q D R b N hN hNq S₁ S₂ S₂ s₁ s₂ s₂ o₁ o₂ o₂ f (𝟙 _)).1 m m'

private theorem read_tj {N : ℕ} {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c) {V : Scheme.{0}}
    (x : V ⟶ M.X) (s₀ : V ⟶ Sp R) (hx : x ≫ M.s = s₀) (o₁ o₂ : Obj b N s₀) (m : ObjMap o₁ M.univ x) (ψ₀ : o₁.A ⟶ o₂.A)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (_ : y ≫ Tj.s = x) (m₀ : ObjMap o₁ Tj.o y) (m₁ : ObjMap o₂ Tj.o' y),
      m₀.φ ≫ Tj.ψ.left = ψ₀.left ≫ m₁.φ := by
  subst hx
  obtain ⟨y, ⟨hy, m₀, m₁, h⟩, -⟩ := Tj.univ V x o₁ o₂ m ψ₀ hu hi ht
  exact ⟨y, hy, m₀, m₁, h⟩

private theorem read_core (hQ : QComp) (hO : UpperTheory.Gal.crystallineComparison.Mod.ObjTri) {N N₁ N₂ c₁ c₂ : ℕ} (hN : 3 ≤ N) (hNq : N.Coprime q)
    {M : Model b N} {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (Tj : TjD M r w j c)
    {V Y₁ Y₂ : Scheme.{0}} {s : V ⟶ Sp R'} {s₀ : V ⟶ Sp R} {t₁ : Y₁ ⟶ Sp R} {t₂ : Y₂ ⟶ Sp R}
    {a : GObj gb N₁ s} {a' : GObj gb N₂ s} {o₁ o₂ : Obj b N s₀} {u₁ : Obj b N t₁} {u₂ : Obj b N t₂}
    (n₁ : QMap a o₁ (𝟙 V) c₁) (n₂ : QMap a' o₂ (𝟙 V) c₂) {j₁ : V ⟶ Y₁} {j₂ : V ⟶ Y₂}
    (k₁ : QMap a u₁ j₁ c₁) (k₂ : QMap a' u₂ j₂ c₂) {f : Y₁ ⟶ M.X} {π : Y₂ ⟶ M.X}
    (mf : ObjMap u₁ M.univ f) (mπ : ObjMap u₂ M.univ π)
    (hb₁ : (j₁ ≫ f) ≫ M.s = s₀) (hb₂ : (j₂ ≫ π) ≫ M.s = s₀)
    (ψ' : a.A.left ⟶ a'.A.left) (ψ₀ : o₁.A ⟶ o₂.A) (hψ : n₁.φ ≫ ψ₀.left = ψ' ≫ n₂.φ)
    (hu : IsUnit ((q : ℕ) : Γ(V, ⊤))) (hi : ES.IsPIsog c o₁ o₂ ψ₀) (ht : ES.IsTj r w j o₁ o₂ ψ₀) :
    ∃ (y : V ⟶ Tj.Y) (fa : a.A.left ⟶ Tj.o.A.left) (fb : a'.A.left ⟶ Tj.o'.A.left),
      y ≫ Tj.s = j₁ ≫ f ∧ y ≫ Tj.t = j₂ ≫ π ∧ IsGrpPullback a.A Tj.o.A y fa ∧ IsGrpPullback a'.A Tj.o'.A y fb ∧
      fa ≫ Tj.ψ.left = ψ' ≫ fb ∧ fa ≫ Tj.ms.φ = k₁.φ ≫ mf.φ ∧ fb ≫ Tj.mt.φ = k₂.φ ≫ mπ.φ := by
  obtain ⟨k₁', hk₁'⟩ := qmap_cast (Category.id_comp j₁).symm k₁
  obtain ⟨k₂', hk₂'⟩ := qmap_cast (Category.id_comp j₂).symm k₂
  obtain ⟨m₁, hm₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Y₁ s s₀ t₁ a o₁ u₁ (𝟙 V) j₁).2.2.1 inferInstance n₁ k₁'
  obtain ⟨m₂, hm₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Y₂ s s₀ t₂ a' o₂ u₂ (𝟙 V) j₂).2.2.1 inferInstance n₂ k₂'
  obtain ⟨mx, hmx⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₁ mf
  obtain ⟨mz, hmz⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂ mπ
  obtain ⟨y, hy, m₀, m', hsq⟩ := read_tj Tj (j₁ ≫ f) s₀ hb₁ o₁ o₂ mx ψ₀ hu hi ht
  obtain ⟨e₁, he₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m' Tj.mt
  obtain ⟨e₀, he₀⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₀ Tj.ms
  have hbt : (y ≫ Tj.t) ≫ M.s = s₀ := by
    rw [Category.assoc, ← Tj.st, ← Category.assoc, hy, hb₁]
  have yt : y ≫ Tj.t = j₂ ≫ π := (M.rep V s₀ o₂).unique ⟨hbt, ⟨e₁⟩⟩ ⟨hb₂, ⟨mz⟩⟩
  obtain ⟨p₁, hp₁⟩ := (hQ q D R R' b gb N₁ N c₁ V V Tj.Y s s₀ (Tj.s ≫ M.s) a o₁ Tj.o (𝟙 V) y).1 n₁ m₀
  obtain ⟨p₂, hp₂⟩ := (hQ q D R R' b gb N₂ N c₂ V V Tj.Y s s₀ (Tj.s ≫ M.s) a' o₂ Tj.o' (𝟙 V) y).1 n₂ m'
  have r₀ : m₀.φ ≫ Tj.ms.φ = m₁.φ ≫ mf.φ := by
    rw [← he₀, ← hmx]
    exact rigid_of hO hN hNq e₀ mx hy
  have r₁ : m'.φ ≫ Tj.mt.φ = m₂.φ ≫ mπ.φ := by
    rw [← he₁, ← hmz]
    exact rigid_of hO hN hNq e₁ mz yt
  refine ⟨y, n₁.φ ≫ m₀.φ, n₂.φ ≫ m'.φ, hy, yt, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p₁', hp₁'⟩ := qmap_cast (Category.id_comp y) p₁
    have := p₁'.cart
    rw [hp₁', hp₁] at this
    exact this
  · obtain ⟨p₂', hp₂'⟩ := qmap_cast (Category.id_comp y) p₂
    have := p₂'.cart
    rw [hp₂', hp₂] at this
    exact this
  · rw [Category.assoc, hsq, ← Category.assoc, hψ, Category.assoc]
  · rw [Category.assoc, r₀, ← Category.assoc, ← hm₁, hk₁']
  · rw [Category.assoc, r₁, ← Category.assoc, ← hm₂, hk₂']

end

theorem UpperTheory.Gal.FiniteEtaleModels.bRead_of :
    IsogG → QObj → QComp → UpperTheory.Gal.crystallineComparison.Mod.ObjTri → BRead := by
  intro hI hQO hQC hO p _ D G L _ E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hle hin h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂
    C₁ C₂ W f mf hf e he he0 Tj
  have h3 : 3 ≤ N₀ := X₁.lev.1
  have hcq : N₀.Coprime q := X₁.lev.2.1
  have hM₁ : M₁.1 = N₀ * c₁ := hn₁.1
  have hM₂ : M₂.1 = N₀ * c₂ := hn₂.1
  have pos₁ : 0 < M₁.1 := by have := M₁.2.1; omega
  have pos₂ : 0 < M₂.1 := by have := M₂.2.1; omega
  obtain ⟨o₁, ⟨n₁⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₁.1 N₀ c₁ hM₁ pos₁ hcq _ _ (T.M M₁).univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := hQO q (datAt S.atq S.sp) (Ow w) E S.b gb (algebraMap (Ow w) E) S.mat M₂.1 N₀ c₂ hM₂ pos₂ hcq _ _ W.o
  obtain ⟨ψ₀, hψ, hi, ht⟩ := hI p D G L E gb q r 𝔴 𝔴' S.atq S.sp S.std.m1 hmax hu (Ow w) S.b N₀ hcq i e he h 1 htj hint (one_mem _) M₁ M₂ c₁ c₂
    hM₁ hM₂ _ _ (T.M M₁).univ W.o W.ψ (by rw [_root_.mul_one]; exact W.trans) _ o₁ o₂ n₁ n₂
  obtain ⟨k₂, hk₂⟩ := (hQC q (datAt S.atq S.sp) (Ow w) E S.b gb M₂.1 N₀ c₂ (T.M M₂).X X₂.Y.X X₂.Y.X (T.M M₂).s X₂.Y.s X₂.Y.s
    (T.M M₂).univ X₂.Y.univ X₂.Y.univ C₂.j (𝟙 _)).2.2.2 _ (T.M M₁).s W.o W.π W.φ C₂.m
  have hb₁ : (C₁.j ≫ f) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, hf]
    exact C₁.ov
  have hb₂ : ((W.π ≫ C₂.j) ≫ X₂.π) ≫ X₂.M.s = (T.M M₁).s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, Category.assoc, X₂.ov]
    refine (congrArg (W.π ≫ ·) C₂.ov).trans ?_
    simp only [← Category.assoc, W.ov]
  have hun : IsUnit ((q : ℕ) : Γ((T.M M₁).X, ⊤)) := isUnit_nat_of (T.M M₁).s q (Fact.out : q.Prime).ne_zero
  obtain ⟨y, fa, fb, ys, yt, ca, cb, sq, ms, mt⟩ := read_core hQC hO h3 hcq Tj n₁ n₂ C₁.m k₂ mf X₂.mπ hb₁ hb₂ W.ψ.left ψ₀ hψ hun hi ht
  exact ⟨⟨y, ys, by rw [yt, Category.assoc], fa, fb, ca, cb, sq, ms, by rw [mt, hk₂, Category.assoc]⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.KerAtLift
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private theorem pt_one_iff (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (e : x₀.left = x.left ≫ φ) : x = 1 ↔ x₀ = 1 := by
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (by rw [e, GlobalTheory.GlueGrpLaw.one_left h T])
  · intro h0
    refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
    · rw [← e, h0, GlobalTheory.GlueGrpLaw.one_left h T]
    · rw [Over.w x, Over.w (1 : T ⟶ G')]

end

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w : Ideal (𝓞 D.F)} {j c : ℕ}

private theorem kerAt_lift (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (a' : Over.mk z ⟶ T.o.A) :
    KerAt T z (a'.left ≫ T.ms.φ) ↔ a' ≫ T.ψ = 1 := by
  refine ⟨fun h => h a' rfl, fun h b hb => ?_⟩
  have : b = a' := Over.OverMorphism.ext (T.ms.cart.1.hom_ext hb (by rw [Over.w b, Over.w a']))
  rw [this]; exact h

end

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫} {k : ℕ} {T : KS L gb k}
  {N₀ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₀ 𝔟₁} {X₂ : Ext S N₀ 𝔟₂} {𝔴' : Ideal (𝓞 D.F)} {i : ℕ} {h : G.GAf} {M₁ M₂ : Lv p}
  {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}

private theorem ker_read {C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁} {C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂} {W : Wit T h M₁ M₂}
    {f : X₁.Y.X ⟶ X₂.M.X} {mf : ObjMap X₁.Y.univ X₂.M.univ f} {c : ℕ} {Tj : TjD X₂.M r 𝔴' i c} (P : BPt C₁ C₂ W mf Tj)
    {Ω : Type} [Field Ω] (z : Sp Ω ⟶ (T.M M₁).X) (e : 𝟙_ (Over (T.M M₁).X) ⟶ (T.M M₁).univ.A) :
    KerAt Tj (z ≫ P.y) (z ≫ e.left ≫ C₁.m.φ ≫ mf.φ) ↔ toUnit (Over.mk z) ≫ e ≫ W.ψ = 1 := by
  let a' : Over.mk (z ≫ P.y) ⟶ Tj.o.A := Over.homMk (z ≫ e.left ≫ P.fa) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [P.ca.1.w, ← Category.assoc e.left, Over.w e, Over.tensorUnit_hom]
    exact congrArg (z ≫ ·) (Category.id_comp P.y))
  have h1 := kerAt_lift Tj (z ≫ P.y) a'
  have h2 : a'.left ≫ Tj.ms.φ = z ≫ e.left ≫ C₁.m.φ ≫ mf.φ := by
    simp only [a', Over.homMk_left, Category.assoc, P.ms]
  rw [h2] at h1
  rw [h1]
  refine (pt_one_iff P.cb (toUnit (Over.mk z) ≫ e ≫ W.ψ) (a' ≫ Tj.ψ) ?_).symm
  simp only [a', Over.comp_left, Over.homMk_left, Over.toUnit_left, Over.mk_hom, Category.assoc, P.sq]

end

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R} {gb : GBase D.toG R'}
  {N₀ N₁ : ℕ} {𝔟 𝔴' : Ideal (𝓞 D.F)}

private theorem cls_read (hb : 𝔟 ≤ 𝔴') (Y : EtModel b N₀ 𝔟 1) (M : Model b N₀) {f : Y.X ⟶ M.X} (mf : ObjMap Y.univ M.univ f)
    {X : Scheme.{0}} {s : X ⟶ Sp R'} {o : GObj gb N₁ s} {β : R →+* R'} {c : ℕ} {a : 𝓞 D.F} (C : Cls Y β o c a)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X) (g : Over.mk ((x ≫ C.j) ≫ f) ⟶ M.univ.A)
    (hg : ES.KilledBy M.univ 𝔴' g) :
    ∃ d : D.La, ∀ z : Sp Ω ⟶ X, z ≫ C.j = x ≫ C.j → g.left = z ≫ (o.eta d).left ≫ C.m.φ ≫ mf.φ := by
  let g₁ : Over.mk (x ≫ C.j) ⟶ Y.univ.A :=
    Over.homMk (mf.cart.1.lift g.left (x ≫ C.j) (Over.w g)) (by simp)
  have hg₁ : g₁.left ≫ mf.φ = g.left := by simp [g₁]
  have hk : ∀ c ∈ 𝔟 ^ 1, g₁ ≫ Y.univ.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
    refine (pt_one_iff mf.cart _ (g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O c)) ?_).2 (hg c (hb (by simpa using hc)))
    simp only [Over.comp_left, Category.assoc]
    rw [mf.act, ← Category.assoc, hg₁]
  obtain ⟨y, hy⟩ := (Y.isLev.2.2.2 Ω (x ≫ C.j)).2 g₁ hk
  refine ⟨algebraMap (𝓞 D.F) D.O a • y, fun z hz => ?_⟩
  have hl := C.lv y
  rw [← hg₁, ← hy, reassoc_of% hl, reassoc_of% hz]
  simp [Over.toUnit_left]

end

end UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.bKer_of :
    SecInjG → TrEtaPt → BKer := by
  intro hS hT
  unfold BKer
  intro p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂ C₁ C₂ W f mf hf
    e he hpos Tj P Ω _ _ x x' hxx'
  have : CharZero Ω :=
    charZero_of_injective_ringHom (Spec.preimage (x ≫ (T.M M₁).s)).hom.injective
  have hb' : 𝔟₁ ≤ 𝔴' := hb.trans Ideal.mul_le_right
  refine hS q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 hSc.m1 r 𝔴' i e hmax hu hi hpos X₂.M Tj Ω ((x ≫ C₁.j) ≫ f)
    (x ≫ P.y) (x' ≫ P.y) ?_ ?_ ?_
  · rw [Category.assoc, Category.assoc, P.ys]
  · rw [Category.assoc, P.ys, ← Category.assoc, hxx', Category.assoc]
  intro g hg
  obtain ⟨d, hd⟩ := cls_read (D := datAt S.atq S.sp) hb' X₁.Y X₂.M mf C₁ x g hg
  have k₁ : KerAt Tj (x ≫ P.y) g.left ↔ toUnit (Over.mk x) ≫ (T.M M₁).univ.eta d ≫ W.ψ = 1 := by
    rw [hd x rfl]; exact ker_read P x _
  have k₂ : KerAt Tj (x' ≫ P.y) g.left ↔ toUnit (Over.mk x') ≫ (T.M M₁).univ.eta d ≫ W.ψ = 1 := by
    rw [hd x' hxx'.symm]; exact ker_read P x' _
  exact k₁.trans (((hT p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω x d).1.trans
    (hT p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω x' d).1.symm).trans k₂.symm)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiesAbsHolds
section
namespace UpperTheory.Gal.FiniteEtaleModels

theorem liesAbs_holds : LiesAbs :=
  liesAbs_of (lPts_holds lGrp_holds) (lCount_holds lSigPt_holds lSigFin_holds) lIdx_holds sigmaFEt_holds

end UpperTheory.Gal.FiniteEtaleModels
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.MOne
section
open NumberField GlobalTheory.UPel.HT

theorem UpperTheory.Gal.FiniteEtaleModels.O.mOne :
    UpperTheory.Gal.FiniteEtaleModels.O.MOne := by
  intro q _ D hm
  haveI := D.freeLa
  haveI := D.finLa
  have hb : Function.Bijective (algebraMap (𝓞 D.F) D.O) :=
    ⟨D.algebraMap_injective hm, Datum.algebraMap_surjective_of_m_eq_one q D hm⟩
  have hfin : Module.Finite D.O D.La := Module.Finite.of_restrictScalars_finite ℤ D.O D.La
  refine ⟨hb, ?_, hfin⟩
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective _ hb
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  have hsmul : ∀ (r : 𝓞 D.F) (x : D.La), r • x = algebraMap (𝓞 D.F) D.O r • x :=
    fun _ _ => rfl
  haveI : IsScalarTower ℤ (𝓞 D.F) D.La :=
    ⟨fun n r x => by rw [hsmul, hsmul, map_zsmul, smul_assoc]⟩
  have htors : Submodule.torsion (𝓞 D.F) D.La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨r, hr⟩, hx⟩
    have hx' : r • x = 0 := hx
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {r}))
    have hN : Ideal.absNorm (Ideal.span {r}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact hr0
    have hz : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x = 0 := by
      have h1 : ((Ideal.absNorm (Ideal.span {r}) : ℕ) : ℤ) • x =
          ((Ideal.absNorm (Ideal.span {r}) : ℕ) : 𝓞 D.F) • x := by
        rw [natCast_zsmul]
        exact (Nat.cast_smul_eq_nsmul (𝓞 D.F) _ x).symm
      rw [h1, ← hs, mul_smul, hx', smul_zero]
    exact (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hN)
  haveI : Module.Flat (𝓞 D.F) D.La := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htors
  haveI : Module.Finite (𝓞 D.F) D.La := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.FinitePresentation (𝓞 D.F) D.La := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 D.F) D.La := Module.Flat.projective_of_finitePresentation
  haveI h1 : RingHomInvPair (e : 𝓞 D.F →+* D.O) (e.symm : D.O →+* 𝓞 D.F) :=
    RingHomInvPair.of_ringEquiv e
  haveI h2 : RingHomInvPair (e.symm : D.O →+* 𝓞 D.F) (e : 𝓞 D.F →+* D.O) :=
    RingHomInvPair.symm _ _
  let f : D.La ≃ₛₗ[(e : 𝓞 D.F →+* D.O)] D.La :=
    { AddEquiv.refl D.La with map_smul' := fun _ _ => rfl }
  exact Module.Projective.of_equiv f
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OEpsEx
section
theorem UpperTheory.Gal.FiniteEtaleModels.O.epsEx :
    UpperTheory.Gal.FiniteEtaleModels.O.EpsEx := by
  intro A _ _ _ 𝔟₁ 𝔟₂ a₁ a₂ M₁ M₂ t hpos hM hle h₁ h₂
  unfold UpperTheory.Gal.Int.Geo.IsGen at h₁ h₂
  have hM1 : (M₁ : A) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  have hMc : (M₁ : A) = (t : A) * (M₂ : A) := by rw [hM]; push_cast; ring
  set I₁ := Ideal.span {a₁} ⊔ Ideal.span {(M₁ : A)} with hI₁
  have hI₁0 : I₁ ≠ ⊥ := by
    intro h
    have hmem : (M₁ : A) ∈ I₁ := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.mem_bot] at hmem
    exact hM1 hmem
  have h𝔟0 : 𝔟₁ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    exact hM1 h₁
  have hkey : ∀ {J : Ideal A}, J * 𝔟₂ ≤ Ideal.span {(M₁ : A)} → J ≤ I₁ := by
    intro J hJ
    have h3 : J * 𝔟₁ ≤ I₁ * 𝔟₁ := by
      rw [h₁]
      exact le_trans (Ideal.mul_mono_right hle) hJ
    rw [← Ideal.dvd_iff_le] at h3 ⊢
    exact (mul_dvd_mul_iff_right h𝔟0).mp h3
  have hta : (t : A) * a₂ ∈ I₁ := by
    have hsp : Ideal.span {(t : A) * a₂} ≤ I₁ := by
      apply hkey
      rw [← Ideal.span_singleton_mul_span_singleton, mul_assoc, hMc,
        ← Ideal.span_singleton_mul_span_singleton, ← h₂]
      exact Ideal.mul_mono_right (Ideal.mul_mono_left le_sup_left)
    exact hsp (Ideal.mem_span_singleton_self _)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hta
  obtain ⟨ε, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  refine ⟨ε, ⟨-d, by rw [← hyz]; ring⟩, ?_⟩
  have hJK : I₁ * Ideal.span {ε} ⊔ Ideal.span {(M₁ : A)} =
      Ideal.span {(t : A)} * (Ideal.span {a₂} ⊔ Ideal.span {(M₂ : A)}) := by
    rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_mul_span_singleton, ← hMc, hI₁, Ideal.sup_mul,
      Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
    apply le_antisymm
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · rw [Ideal.span_singleton_le_iff_mem]
        have hae : a₁ * ε = (t : A) * a₂ - d * M₁ := by rw [← hyz]; ring
        rw [hae]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      · rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    · refine sup_le ?_ le_sup_right
      rw [Ideal.span_singleton_le_iff_mem, ← hyz]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_sup_left ?_))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      rw [mul_comm]
      exact Ideal.mem_span_singleton_self _
  apply mul_left_cancel₀ hI₁0
  rw [h₁, ← mul_assoc, Ideal.mul_sup, h₁, hJK, mul_assoc, h₂,
    Ideal.span_singleton_mul_span_singleton, ← hMc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OTResim
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.FiniteEtaleModels.O

theorem tResim : TResim := by
  intro G k _ Q _ act e I g hg
  have hn : ∀ n : ℕ, 0 < n → ∀ z : G.La, I.ev n (n • z) = 1 := fun n h0 z =>
    (I.ker n h0 _).2 ⟨z, rfl⟩
  have hadd : ∀ n : ℕ, 0 < n → ∀ (x z : G.La), I.ev n (x + n • z) = I.ev n x := by
    intro n h0 x z
    rw [I.add, hn n h0, mul_one]
  refine ⟨{ ζ := I.ζ
            ζ_prim := I.ζ_prim
            ζ_pow := I.ζ_pow
            ev := fun n x => if 0 < n then I.ev n (g n x) else I.ev n x
            add := ?_
            lin := ?_
            ker := ?_
            onto := ?_
            tower := ?_
            isom := ?_ }, ?_⟩
  · intro n x y
    by_cases h0 : 0 < n
    · simp only [if_pos h0, map_add (f := _), I.add]
    · simp only [if_neg h0, I.add]
  · intro n b x
    by_cases h0 : 0 < n
    · simp only [if_pos h0]
      obtain ⟨z, hz⟩ := hg.lin n h0 b x
      rw [hz, hadd n h0, I.lin]
    · simp only [if_neg h0, I.lin]
  · intro n h0 x
    simp only [if_pos h0]
    rw [I.ker n h0]
    constructor
    · rintro ⟨y, hy⟩
      exact hg.inj n h0 x y hy
    · rintro ⟨v, rfl⟩
      exact ⟨g n v, map_nsmul (g n) n v⟩
  · intro n h0 q
    simp only [if_pos h0]
    rw [I.onto n h0]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, z, hy⟩ := hg.onto n h0 x
      exact ⟨y, by rw [hy, hadd n h0]⟩
    · rintro ⟨x, hx⟩
      exact ⟨g n x, hx⟩
  · intro n m hn0 hm0 x
    have h0 : 0 < n * m := Nat.mul_pos hn0 hm0
    simp only [if_pos h0, if_pos hn0]
    rw [I.tower n m hn0 hm0]
    obtain ⟨z, hz⟩ := hg.tow n m hn0 hm0 x
    rw [hz, hadd n hn0]
  · intro n h0 x y
    simp only [if_pos h0]
    have h := I.isom n h0 (g n x) (g n y)
    obtain ⟨c, hc⟩ := hg.iso n h0 x y
    have hz : I.ζ n ^ (n : ℤ) = 1 := by
      rw [zpow_natCast]
      exact (I.ζ_prim n h0).pow_eq_one
    have hE : I.ζ n ^ (2 * G.EF (g n x) (g n y)) = I.ζ n ^ (2 * G.EF x y) := by
      have : 2 * G.EF (g n x) (g n y) = 2 * G.EF x y + (n : ℤ) * (2 * c) := by
        linarith [hc]
      rw [this, zpow_add, zpow_mul (I.ζ n) (n : ℤ), hz, one_zpow, mul_one]
    rw [hE] at h
    exact h
  · intro n h0 x
    simp only [if_pos h0]

end UpperTheory.Gal.FiniteEtaleModels.O
end
end

