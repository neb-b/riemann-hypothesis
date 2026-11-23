module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleChernClassEqKummerClass
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtaleChernClass

open GlobalTheory.CatH (face toLast)

universe w

section Cochains

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{w} R)

theorem d_zero_apply (f : Cn F 0) (s : ComposableArrows C 1) :
    d F 0 f s = (show F.obj (s.obj (Fin.last 1)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 1)) from (F.map (s.map' 0 1)).hom (f (face 1 s))) := by
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_two]
  have e0 : toLast (0 : Fin 2) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 2) s = s.map' 0 1 := rfl
  rw [e0, e1, F.map_id]
  simp [sub_eq_add_neg]
  rfl

theorem d_one_apply (f : Cn F 1) (s : ComposableArrows C 2) :
    d F 1 f s = (show F.obj (s.obj (Fin.last 2)) from f (face 0 s)) - (show F.obj (s.obj (Fin.last 2)) from f (face 1 s)) +
      (show F.obj (s.obj (Fin.last 2)) from (F.map (s.map' 1 2)).hom (f (face 2 s))) := by
  change ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (f (face i s)) = _
  rw [Fin.sum_univ_three]
  have e0 : toLast (0 : Fin 3) s = 𝟙 _ := s.map_id _
  have e1 : toLast (1 : Fin 3) s = 𝟙 _ := s.map_id _
  have e2 : toLast (2 : Fin 3) s = s.map' 1 2 := rfl
  rw [e0, e1, e2, F.map_id]
  simp [sub_eq_add_neg]
  rfl

end Cochains

theorem close_sum {M : Type*} [AddCommGroup M] (tce tbe tbc kv kw ku kvw i : M)
    (h₁ : tce - tbe + tbc = kv + kw - kvw) (h₂ : kvw = ku + i) :
    (-1 : ℤ) ^ 1 • ((tce - kw) - (tbe - ku) + (tbc - kv)) = i := by
  have e : tce = kv + kw - kvw + tbe - tbc := by rw [← h₁]; abel
  rw [e, h₂]
  simp only [pow_one, neg_smul, one_smul]
  abel

theorem u_congr {X : Scheme.{0}} (D : LineData X) {V : Scheme.{0}} {a a' b b' : V ⟶ D.Y}
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) (ha : a = a') (hb : b = b') :
    D.u a b h = D.u a' b' h' := by
  subst ha hb; rfl

theorem etale_chern_class_eq_kummer_class : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.ResGood → CrystallineSemistableComparison.E.StCol → CrystallineSemistableComparison.E.FirstChernCoboundary → CrystallineSemistableComparison.E.KumPow →
    CrystallineSemistableComparison.E.EtaleFirstChernKummer := by
  intro hES hRG hSC hCP hKP hGen hKum hC1 q _ C _ P X Y D L hL hInv x hx z Λ
  obtain ⟨a, η, θ, hRep, hηn, hθn, hdη, hdiff, hcoc⟩ := hCP hC1 q X D L hL hInv x hx
  have hθc : ∀ (V : Scheme.{0}) (b b' c : V ⟶ D.Y) (h : b ≫ D.f = c ≫ D.f) (h' : b' ≫ D.f = c ≫ D.f),
      b = b' → θ V b c h = θ V b' c h' := by
    intro V b b' c h h' e
    subst e
    rfl
  have hG : (P.res 1).Good := hRG hGen q C P 1
  obtain ⟨hιd, hdd, hinj, -, -⟩ := hSC ℤ C P.L (P.res 1) hG
  have hpp : ∀ {c c' : C} (φ : c ⟶ c'), ((P.S.map φ).unop ≫ Λ.p c) ≫ D.f = Λ.p c' ≫ D.f := by
    intro c c' φ
    rw [Category.assoc, Λ.hp, Λ.hp, Y.nat]
  let A₀ : ∀ {c c' : C} (φ : c ⟶ c'), Sec ((res _ (tw q 1)).X 0) (P.U c') := fun {c c'} φ =>
    θ _ ((P.S.map φ).unop ≫ Λ.p c) (Λ.p c') (hpp φ) - kumT q _ (Λ.r φ)
  let a₁ : Cn ((P.res 1).K 1) 0 := fun s => η _ (Λ.p (s.obj 0))
  let a₀ : Cn ((P.res 1).K 0) 1 := fun s => A₀ (s.map' 0 1)
  have h1 : (P.res 1).dvC 1 0 a₁ = Y.glob 1 2 a := by
    funext s
    refine (hdη _ (Λ.p (s.obj 0))).trans ?_
    rw [Λ.hp]
    rfl
  have h2 : (-1 : ℤ) ^ 0 • d ((P.res 1).K 1) 0 a₁ = (P.res 1).dvC 0 1 a₀ := by
    funext s
    rw [pow_zero, one_smul, d_zero_apply]
    have e := hdiff _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1)) _ (Λ.hr _)
    rw [← hηn] at e
    exact e
  have h3 : (-1 : ℤ) ^ 1 • d ((P.res 1).K 0) 1 a₀ = (P.res 1).ιC 2 z := by
    funext s
    rw [Pi.smul_apply, d_one_apply]
    let g := (P.S.map (s.map' 1 2)).unop
    have hg : g ≫ (P.S.map (s.map' 0 1)).unop = (P.S.map (s.map' 0 2)).unop := by
      have e : s.map' 0 2 = s.map' 0 1 ≫ s.map' 1 2 := s.map_comp _ _
      rw [e, P.S.map_comp, unop_comp]
    have hb : g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0) =
        (P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0) := by
      rw [← Category.assoc, hg]
    have hbc' : (g ≫ (P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      have e : ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = Λ.p (s.obj 1) ≫ D.f := hpp (s.map' 0 1)
      rw [Category.assoc g, e, Category.assoc]
    have hbc : ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) ≫ D.f = (g ≫ Λ.p (s.obj 1)) ≫ D.f := by
      rw [← hb]
      exact hbc'
    let v := Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1))
    let w := Λ.r (s.map' 1 2)
    let u := Λ.r (s.map' 0 2)
    have hv : v ^ q = D.u _ _ hbc := by
      change Units.map g.appTop.hom.toMonoidHom (Λ.r (s.map' 0 1)) ^ q = _
      rw [← map_pow, Λ.hr, ← D.nat]
      exact u_congr D _ _ hb rfl
    have hw : w ^ q = D.u (g ≫ Λ.p (s.obj 1)) (Λ.p (s.obj 2)) (hpp (s.map' 1 2)) := Λ.hr _
    have hc := hcoc _ _ _ _ hbc (hpp (s.map' 1 2)) v w hv hw
    have hk := hKP hKum q _ (P.ζ (s.obj (Fin.last 2))) (z s) (v * w * u⁻¹) u (Λ.hz s)
    rw [inv_mul_cancel_right] at hk
    have hn : ((((P.res 1).K 0).map (s.map' 1 2)).hom (a₀ (face 2 s))) =
        θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc - kumT q _ v := by
      have t₁ : Sec.res g (θ _ ((P.S.map (s.map' 0 1)).unop ≫ Λ.p (s.obj 0)) (Λ.p (s.obj 1)) (hpp (s.map' 0 1))) =
          θ _ ((P.S.map (s.map' 0 2)).unop ≫ Λ.p (s.obj 0)) (g ≫ Λ.p (s.obj 1)) hbc :=
        (hθn _ _ g _ _ _ hbc').trans (hθc _ _ _ _ _ _ hb)
      have t₂ : Sec.res g (kumT q _ (Λ.r (s.map' 0 1))) = kumT q _ v := (hKum q).1 _ _ g _ (P.ζ _).2.1
      exact (map_sub _ _ _).trans (congrArg₂ (· - ·) t₁ t₂)
    rw [hn]
    exact close_sum _ _ _ _ _ _ _ _ hc hk
  have hSt : (P.res 1).St z 2 0 (Y.glob 1 2 a) := ⟨a₁, h1, a₀, h2.symm, rfl, h3.symm⟩
  have hz : d P.L 2 z = 0 := by
    apply hinj 3
    rw [map_zero, ← hιd, ← h3, map_smul, d_d, smul_zero]
  exact ⟨hz, ((hES hGen q C P X Y 1 2 x).2 _ ⟨a, hRep, z, hz, hSt, rfl⟩).symm⟩

end GlobalTheory.CompanionTheory.EtaleChernClass
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquiv
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.ZModDual

private theorem finite_dual_zmod_and_card_le (n : ℕ) [NeZero n] (X : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] :
    Finite (Module.Dual (ZMod n) X) ∧ Nat.card (Module.Dual (ZMod n) X) ≤ Nat.card X := by
  have hfin : Finite (Module.Dual (ZMod n) X) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod n) X => (φ : X → ZMod n)) DFunLike.coe_injective
  refine ⟨hfin, ?_⟩
  letI := Fintype.ofFinite X
  let e : Module.Dual (ZMod n) X → AddChar X ℂ :=
    fun φ => (ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom
  have he : Function.Injective e := by
    intro φ ψ h
    ext x
    have hx := DFunLike.congr_fun h x
    exact ZMod.injective_stdAddChar hx
  calc Nat.card (Module.Dual (ZMod n) X) ≤ Nat.card (AddChar X ℂ) :=
        Nat.card_le_card_of_injective e he
    _ = Nat.card X := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

theorem equiv_dual_of_injective_pair :
    ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X]
      [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y],
      (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) →
      (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) →
      Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  intro n _ X Y _ _ _ _ _ _ hf hg
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  obtain ⟨hXf, hXc⟩ := finite_dual_zmod_and_card_le n X
  obtain ⟨hYf, hYc⟩ := finite_dual_zmod_and_card_le n Y
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := Nat.card_le_card_of_injective g hg
  have hXY : Nat.card X = Nat.card Y := by omega
  refine ⟨⟨LinearEquiv.ofBijective f ⟨hf, ?_⟩⟩, hXY⟩
  exact (hf.bijective_of_nat_card_le (by omega)).2

end GlobalTheory.CompanionTheory.ZModDual
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsKumPow
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KumPowProof

theorem isKum_pow {q : ℕ} {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v : (Γ(U, ⊤))ˣ) (k : ℕ) :
    ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ k * v → t U w = t U v + k • resGen 1 ζ := by
  induction k with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw, zero_smul, add_zero]
  | succ k ih =>
    intro w hw
    have hw' : (w : Γ(U, ⊤)) = ζ.1 * (ζ.1 ^ k * v) := by rw [hw]; ring
    obtain ⟨z, hz⟩ : IsUnit (ζ.1 ^ k * v) := isUnit_of_mul_isUnit_right (hw' ▸ w.isUnit)
    rw [ht.2 U ζ z w (by rw [hw', hz]), ih z hz, succ_nsmul, add_assoc]

theorem res_smap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun m => m.hom x) h).symm

theorem kumPow : LcCover → RepRoot → KapSpec → PrimAlg → KumPow := by
  intro hL _ hK _ hKum q _ U ζ f r v hr
  have ht : IsKum q (kumT q) := hKum q
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  obtain ⟨W, j, hf, -, -, hG⟩ := hL U (ZMod q) f
  obtain ⟨y, -, huniq⟩ := hG (ZMod q) ((res _ (tw q 1)).X 0) (fun a => Sec.res (j a) (kumT q U (r * v)))
  refine (huniq _ fun a => rfl).trans (huniq _ fun a => ?_).symm
  have hra : (j a).appTop.hom r.val = (primRes (j a) ζ).1 ^ a.val := hr (W a) (j a) a (hf a)
  have hlc : Sec.res (j a) (kap 1 ζ f) = (ULift.up a : ULift.{1} (ZMod q)) • twGen 1 (primRes (j a) ζ) :=
    (hK q 1 U ζ f).1 (W a) (j a) a (hf a)
  have hup : (ULift.up a : ULift.{1} (ZMod q)) = a.val • (1 : ULift.{1} (ZMod q)) :=
    ULift.ext (by change a = a.val • (1 : ZMod q); simp)
  have hsm : Sec.res (j a) (kap 1 ζ f) = a.val • twGen 1 (primRes (j a) ζ) := by
    rw [hlc, hup, smul_assoc, one_smul]
  have hkey := isKum_pow ht (primRes (j a) ζ) (Units.map (j a).appTop.hom.toMonoidHom v) a.val
    (Units.map (j a).appTop.hom.toMonoidHom (r * v)) (by
      change (j a).appTop.hom (r.val * v.val) = _ * (j a).appTop.hom v.val
      rw [map_mul, hra])
  have e1 : Sec.res (j a) (kumT q U (r * v)) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom (r * v)) :=
    ht.1 _ _ (j a) _ hq
  have e2 : Sec.res (j a) (kumT q U v) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom v) :=
    ht.1 _ _ (j a) _ hq
  have e3 : Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) = a.val • resGen 1 (primRes (j a) ζ) := by
    rw [res_smap, hsm]
    exact map_nsmul _ _ _
  have e0 : Sec.res (j a) (kumT q U v + Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) =
      Sec.res (j a) (kumT q U v) + Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) := map_add _ _ _
  rw [e0, e1, e2, e3, hkey]

end GlobalTheory.CompanionTheory.KumPowProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLCRes
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KapSpecProof

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  delta GlobalTheory.EtC.Sec.res
  rw [op_comp, Functor.map_comp]
  rfl

theorem primRes_comp {q : ℕ} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    primRes (k ≫ g) ζ = primRes k (primRes g ζ) := by
  apply Subtype.ext
  delta CrystallineSemistableComparison.E.primRes
  rfl

theorem sec_subsingleton (hL : LcCover) {U : Scheme.{0}} [IsEmpty U] (G : Shv R) :
    Subsingleton (Sec G U) := by
  let f0 : LocallyConstant U Empty :=
    ⟨fun u => isEmptyElim u, fun s => by
      convert isOpen_empty
      ext u
      exact isEmptyElim u⟩
  obtain ⟨W, j, -, -, -, hglue⟩ := hL U Empty f0
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => a.elim)
  exact ⟨fun x x' => (hz x (fun a => a.elim)).trans (hz x' (fun a => a.elim)).symm⟩

theorem sec_ext (hL : LcCover) {ι : Type} {U : Scheme.{0}} (f : LocallyConstant U ι) (G : Shv R)
    (x y : Sec G U)
    (h : ∀ (V : Scheme.{0}) (g : V ⟶ U) (a : ι), (∀ v : V, f (g v) = a) → Sec.res g x = Sec.res g y) :
    x = y := by
  obtain ⟨W, j, hWf, -, -, hglue⟩ := hL U ι f
  obtain ⟨z, -, hz⟩ := hglue R G (fun a => Sec.res (j a) x)
  exact (hz x (fun a => rfl)).trans (hz y (fun a => (h (W a) (j a) a (hWf a)).symm)).symm

variable {q : ℕ} {i : ℤ}

theorem isLC_unique (hL : LcCover) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x y : Sec (tw q i) U} (hx : IsLC i ζ f x) (hy : IsLC i ζ f y) :
    x = y := by
  refine sec_ext hL f _ x y fun V g a hga => ?_
  delta CrystallineSemistableComparison.E.IsLC at hx hy
  rw [hx V g a hga, hy V g a hga]

theorem isLC_exists (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤))
    (f : LocallyConstant U (ZMod q)) : ∃ x : Sec (tw q i) U, IsLC i ζ f x := by
  delta CrystallineSemistableComparison.E.IsLC
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  obtain ⟨W, j, -, hfac, -, hglue⟩ := hL U (ZMod q) f
  obtain ⟨x, hx, -⟩ := hglue (ZMod q) (tw q i)
    (fun a => (⟨a⟩ : ULift (ZMod q)) • twGen i (primRes (j a) ζ))
  refine ⟨x, fun V g a ha => ?_⟩
  obtain ⟨k, rfl⟩ := hfac V g a ha
  rw [res_comp, hx a, hres_smul, ((hR q i (W a) (primRes (j a) ζ)).1 V k).1, ← primRes_comp]

theorem isLC_add (hL : LcCover) (hR : RepRoot) {U : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f f' : LocallyConstant U (ZMod q)} {x x' : Sec (tw q i) U} (hx : IsLC i ζ f x)
    (hx' : IsLC i ζ f' x') : IsLC i ζ (f + f') (x + x') := by
  delta CrystallineSemistableComparison.E.IsLC at hx hx' ⊢
  intro V g a ha
  have hres_smul : ∀ {V W : Scheme.{0}} (g : V ⟶ W) (c : ULift (ZMod q)) (y : Sec (tw q i) W),
      Sec.res g (c • y) = c • Sec.res g y := fun g c y => by
    delta GlobalTheory.EtC.Sec.res
    exact map_smul _ c y
  have hcont : Continuous (fun v : V => g v) := g.continuous
  let F2 : LocallyConstant V (ZMod q × ZMod q) :=
    ⟨fun v => (f (g v), f' (g v)), IsLocallyConstant.comp₂ (f.isLocallyConstant.comp_continuous hcont)
      (f'.isLocallyConstant.comp_continuous hcont) Prod.mk⟩
  refine sec_ext hL F2 _ _ _ fun V' g' b hb => ?_
  rcases isEmpty_or_nonempty V' with hV | ⟨⟨v⟩⟩
  · haveI := sec_subsingleton hL (U := V') (tw q i)
    exact Subsingleton.elim _ _
  have hb1 : ∀ v, f ((g' ≫ g) v) = b.1 := fun v => congrArg Prod.fst (hb v)
  have hb2 : ∀ v, f' ((g' ≫ g) v) = b.2 := fun v => congrArg Prod.snd (hb v)
  have hres_add : ∀ (y y' : Sec (tw q i) U),
      Sec.res (g' ≫ g) (y + y') = Sec.res (g' ≫ g) y + Sec.res (g' ≫ g) y' := fun y y' => by
    delta GlobalTheory.EtC.Sec.res
    exact map_add _ y y'
  have hab : a = b.1 + b.2 := by
    rw [← ha (g' v), ← hb1 v, ← hb2 v]
    rfl
  rw [← res_comp, hres_add, hx V' (g' ≫ g) b.1 hb1, hx' V' (g' ≫ g) b.2 hb2, ← add_smul, hres_smul,
    ((hR q i V (primRes g ζ)).1 V' g').1, ← primRes_comp, hab]
  rfl

theorem isLC_res {U V : Scheme.{0}} {ζ : Prim q Γ(U, ⊤)}
    {f : LocallyConstant U (ZMod q)} {x : Sec (tw q i) U} (hx : IsLC i ζ f x) (g : V ⟶ U) :
    IsLC i (primRes g ζ) (lcRes q g f) (Sec.res g x) := by
  delta CrystallineSemistableComparison.E.IsLC at hx ⊢
  intro W h a ha
  rw [← res_comp, hx W (h ≫ g) a ?_, primRes_comp]
  intro w
  exact ha w

theorem kapSpec : LcCover → RepRoot → KapSpec := by
  intro hL hR q i U ζ f
  have hk : ∀ {U' : Scheme.{0}} (ζ' : Prim q Γ(U', ⊤)) (f' : LocallyConstant U' (ZMod q)),
      IsLC i ζ' f' (kap i ζ' f') := by
    intro U' ζ' f'
    have hex : ∃ κ : LocallyConstant U' (ZMod q) →+ Sec (tw q i) U', ∀ f'', IsLC i ζ' f'' (κ f'') := by
      choose c hc using fun f'' : LocallyConstant U' (ZMod q) => isLC_exists hL hR (i := i) ζ' f''
      refine ⟨{ toFun := c, map_zero' := ?_, map_add' := fun a b => ?_ }, hc⟩
      · have h := isLC_unique hL (hc (0 + 0)) (isLC_add hL hR (hc 0) (hc 0))
        simpa using h
      · exact isLC_unique hL (hc (a + b)) (isLC_add hL hR (hc a) (hc b))
    delta CrystallineSemistableComparison.E.kap
    exact GlobalTheory.EtC.pick_spec hex f'
  refine ⟨hk ζ f, fun x hx => isLC_unique hL hx (hk ζ f), fun V g => ?_⟩
  exact isLC_unique hL (isLC_res (hk ζ f) g) (hk _ _)

end GlobalTheory.CompanionTheory.KapSpecProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapOneEqTwGen
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRoot

theorem kap_one_eq_twGen (hRep : CrystallineSemistableComparison.E.RepRoot) (hKap : CrystallineSemistableComparison.E.KapSpec) {q : ℕ} (i : ℤ) {U : Scheme.{0}}
    (ζ : Prim q Γ(U, ⊤)) : kap i ζ 1 = twGen i ζ := by
  refine ((hKap q i U ζ 1).2.1 (twGen i ζ) ?_).symm
  intro V g a h
  rw [((hRep q i U ζ).1 V g).1]
  by_cases hV : Nonempty V
  · obtain ⟨v⟩ := hV
    have ha : (1 : ZMod q) = a := h v
    subst ha
    exact (one_smul _ _).symm
  · have hV' : IsEmpty V := not_nonempty_iff.1 hV
    have h0 := (hKap q i U ζ 1).1 V g 0 (fun v => hV'.elim v)
    have h1 := (hKap q i U ζ 1).1 V g 1 (fun v => hV'.elim v)
    have hz : twGen i (primRes g ζ) = 0 := by
      have e : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) =
          (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) := h1.symm.trans h0
      have e1 : (ULift.up (1 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) = twGen i (primRes g ζ) :=
        one_smul _ _
      have e0 : (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • twGen i (primRes g ζ) = 0 := zero_smul _ _
      rw [e1, e0] at e
      exact e
    rw [hz, smul_zero]

theorem d_one_eq_zero {C : Type 1} [Category.{0} C] {R : Type} [CommRing R] (A : C ⥤ CommAlgCat.{0} R) :
    d (modF A) 0 (fun s => (1 : A.obj (s.obj (Fin.last 0)))) = 0 := by
  funext s
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (A.map (GlobalTheory.CatH.toLast i s)).hom 1 = (0 : A.obj _)
  rw [Fin.sum_univ_two, map_one, map_one]
  simp

theorem etRoot_of_spec : CrystallineSemistableComparison.E.EtSpec → CrystallineSemistableComparison.E.RepRoot → CrystallineSemistableComparison.E.KapSpec → CrystallineSemistableComparison.E.EtRoot := by
  intro hEt hRep hKap hGen q _ C _ P X Y ζ hζ i
  refine ((hEt hGen q C P X Y i 0 (rootClass i ζ)).2 _ ?_).symm
  refine ⟨resGen i ζ, (hRep q i X ζ).2, ?_⟩
  refine ⟨fun s => (1 : (lcF P.S q).obj (s.obj (Fin.last 0))), d_one_eq_zero (lcF P.S q), ?_, rfl⟩
  refine ⟨rfl, ?_⟩
  funext s
  change Sec.map (resι _ (tw q i)) (kap i (P.ζ (s.obj (Fin.last 0))) 1) = Sec.res (Y.y (s.obj (Fin.last 0))) (resGen i ζ)
  rw [kap_one_eq_twGen hRep hKap, ((hRep q i X ζ).1 _ _).2, hζ]
  rfl

end GlobalTheory.CompanionTheory.EdgeRoot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcCover
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.LcCoverProof

theorem lcCover : CrystallineSemistableComparison.E.LcCover := by
  intro U ι f
  let O : ι → U.Opens := fun a => ⟨f ⁻¹' {a}, f.isLocallyConstant.isOpen_fiber a⟩
  have hcov : iSup O = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨f x, rfl⟩
  have hval : ∀ (a : ι) (v : (O a).toScheme), f ((O a).ι v) = a := fun a v => v.2
  refine ⟨fun a => (O a).toScheme, fun a => (O a).ι, hval, ?_, ?_, ?_⟩
  · intro V g a hg
    have hr : Set.range g ⊆ Set.range (O a).ι := by
      rintro _ ⟨v, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hg v
    exact ⟨IsOpenImmersion.lift (O a).ι g hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro x y h
    refine U.sheaf.eq_of_locally_eq' O ⊤ (fun a => homOfLE le_top) hcov.ge x y fun a => ?_
    have e : O a ≤ (O a).ι ''ᵁ ⊤ := by simp
    have hm : U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op =
        U.presheaf.map (homOfLE (x := (O a).ι ''ᵁ ⊤) le_top).op ≫ U.presheaf.map (homOfLE e).op := by
      rw [← Functor.map_comp]
      rfl
    have := congrArg (U.presheaf.map (homOfLE e).op).hom (h a)
    change (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom x =
      (U.presheaf.map (homOfLE le_top : O a ⟶ ⊤).op).hom y
    rw [hm]
    exact this
  · intro R _ G x
    have hG := (isSheaf_iff_isSheaf_of_type _ _).1
      ((Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.property)
    have hS : Sieve.ofArrows (fun a => (O a).toScheme) (fun a => (O a).ι) ∈ Scheme.etaleTopology U :=
      Scheme.zariskiTopology_le_etaleTopology _
        (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hcov))
    have hsf := hG _ hS
    rw [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hsf
    refine hsf x ?_
    intro a b Z gi gj h
    by_cases hab : a = b
    · subst hab
      have : gi = gj := by rwa [cancel_mono] at h
      rw [this]
    · have hE : IsEmpty Z := ⟨fun z => hab (by
        have h1 := hval a (gi z)
        have h2 := hval b (gj z)
        rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, h2] at h1
        exact h1.symm)⟩
      have hz := (Sheaf.isTerminalOfBotCover G Z (Scheme.bot_mem_grothendieckTopology Z)).isZero
      have := ModuleCat.subsingleton_of_isZero hz
      exact Subsingleton.elim _ _

end GlobalTheory.CompanionTheory.LcCoverProof
end

