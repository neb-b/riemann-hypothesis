module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatUnique
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem map_restrict {V : Scheme.{0}} {d : ℕ} (M : Matrix (Fin d) (Fin d) Γ(V, ⊤))
    {U P : V.Opens} (s : (P : Scheme.{0}) ⟶ U) (hs : s ≫ U.ι = P.ι) :
    (M.map U.ι.appTop.hom).map s.appTop.hom = M.map P.ι.appTop.hom := by
  ext m l
  simp only [Matrix.map_apply, ← hs, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatUnique :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B a b M → GMat B a b M' → M = M' := by
  intro K _ W Z Y q i π D d B V a b M M' hM hM'
  ext m l
  refine sectionExt _ _ fun x => ?_
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := hM x
  obtain ⟨U', α', β', a₁', b₁', hx', ha', hb', hL'⟩ := hM' x
  have hs : V.homOfLE (inf_le_left : U ⊓ U' ≤ U) ≫ U.ι = (U ⊓ U').ι := Scheme.homOfLE_ι _ _
  have hs' : V.homOfLE (inf_le_right : U ⊓ U' ≤ U') ≫ U'.ι = (U ⊓ U').ι := Scheme.homOfLE_ι _ _
  generalize V.homOfLE (inf_le_left : U ⊓ U' ≤ U) = s at hs
  generalize V.homOfLE (inf_le_right : U ⊓ U' ≤ U') = s' at hs'
  have pt : ((U ⊓ U' : V.Opens) : Scheme.{0}) := ⟨x, hx, hx'⟩
  have eα : α = α' := by
    refine sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (s ≫ a₁) (s' ≫ a₁') pt ?_
    change (s ≫ a₁) ≫ wI B α = (s' ≫ a₁') ≫ wI B α'
    rw [Category.assoc, Category.assoc, ← ha, ← ha', ← Category.assoc, ← Category.assoc, hs, hs']
  have eβ : β = β' := by
    refine sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (s ≫ b₁) (s' ≫ b₁') pt ?_
    change (s ≫ b₁) ≫ wI B β = (s' ≫ b₁') ≫ wI B β'
    rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, hs, hs']
  subst eα eβ
  have h₁ := locMatNat B α β s _ _ hL
  have h₂ := locMatNat B α β s' _ _ hL'
  rw [map_restrict M s hs, ← Category.assoc, hs] at h₁
  rw [map_restrict M' s' hs', ← Category.assoc, hs'] at h₂
  have e := locMatUnique B α β _ _ _ h₁ h₂
  exact ⟨U ⊓ U', ⟨hx, hx'⟩, congrFun (congrFun e m) l⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GvChart
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem appLE_pull {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (N : C.Opens)
    (h : ⊤ ≤ g ⁻¹ᵁ N) (h' : ⊤ ≤ (f ≫ g) ⁻¹ᵁ N) (a : Γ(C, N)) :
    f.appTop.hom ((g.appLE N ⊤ h).hom a) = ((f ≫ g).appLE N ⊤ h').hom a := by
  have e : g.appLE N ⊤ h ≫ f.appTop = (f ≫ g).appLE N ⊤ h' :=
    by
      have e0 : f.appTop = f.appLE ⊤ ⊤ le_rfl := Scheme.Hom.app_eq_appLE ..
      rw [e0]
      exact Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ h le_rfl
  rw [← e]
  rfl

private theorem appLE_congr {A C : Scheme.{0}} {f g : A ⟶ C} (e : f = g) (N : C.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ N) (h' : ⊤ ≤ g ⁻¹ᵁ N) (a : Γ(C, N)) :
    (f.appLE N ⊤ h).hom a = (g.appLE N ⊤ h').hom a := by
  subst e
  rfl

section
variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
  {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ}

private theorem u_pull (B : Blow q i π D d) (α β : B.ι) (k l : Fin d) {V' V : Scheme.{0}}
    (s : V' ⟶ V) (y : V ⟶ Y) (h₁ : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h₂ : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l)
    (h₁' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c α).C k) (h₂' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c β).C l) :
    D.u (secOf B α k (s ≫ y) h₁') (secOf B β l (s ≫ y) h₂')
        ((secOf_f B α k (s ≫ y) h₁').trans (secOf_f B β l (s ≫ y) h₂').symm) =
      Units.map s.appTop.hom.toMonoidHom
        (D.u (secOf B α k y h₁) (secOf B β l y h₂)
          ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm)) := by
  have key : ∀ (a b : V' ⟶ D.Y) (ha : a = s ≫ secOf B α k y h₁) (hb : b = s ≫ secOf B β l y h₂)
      (h : a ≫ D.f = b ≫ D.f), D.u a b h = Units.map s.appTop.hom.toMonoidHom
        (D.u (secOf B α k y h₁) (secOf B β l y h₂)
          ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm)) := by
    intro a b ha hb h
    subst ha hb
    exact D.nat s _ _ _
  exact key _ _ (chartNat B α k s y h₁ h₁').2 (chartNat B β l s y h₂ h₂').2 _

private theorem left_pull (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V' V : Scheme.{0}}
    (s : V' ⟶ V) (y : V ⟶ Y) (h₁ : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k)
    (h₁' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c α).C k) (G : Matrix (Fin d) (Fin d) Γ(V, ⊤)) (m : Fin d) :
    s.appTop.hom (G.mulVec (uV B α k y h₁) m) =
      (G.map s.appTop.hom).mulVec (uV B α k (s ≫ y) h₁') m := by
  rw [RingHom.map_mulVec]
  congr 1
  funext n
  exact ((chartNat B α k s y h₁ h₁').1 n).symm

private theorem right_pull (B : Blow q i π D d) (α β : B.ι) (k l : Fin d) {V' V : Scheme.{0}}
    (s : V' ⟶ V) (y : V ⟶ Y) (h₁ : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h₂ : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l)
    (h₁' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c α).C k) (h₂' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c β).C l) (m : Fin d) :
    s.appTop.hom (((((D.u (secOf B α k y h₁) (secOf B β l y h₂)
        ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm))⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) •
          uV B β l y h₂) m) =
      ((((D.u (secOf B α k (s ≫ y) h₁') (secOf B β l (s ≫ y) h₂')
        ((secOf_f B α k (s ≫ y) h₁').trans (secOf_f B β l (s ≫ y) h₂').symm))⁻¹ : (Γ(V', ⊤))ˣ) : Γ(V', ⊤)) •
          uV B β l (s ≫ y) h₂') m := by
  rw [u_pull B α β k l s y h₁ h₂ h₁' h₂', ← map_inv]
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  rw [(chartNat B β l s y h₂ h₂').1 m]
  rfl

end

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gvChart :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (y : V ⟶ Y) (p : V ⟶ W), y ≫ π = p ≫ i → ∀ (α β : B.ι) (k l : Fin d) (h₁ : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h₂ : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → M.mulVec (uV B α k y h₁) = (((D.u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm))⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • uV B β l y h₂ := by
  intro K _ W Z Y q i π D d B V y p hyp α β k l h₁ h₂ M hL
  funext m
  refine sectionExt _ _ fun x => ?_
  obtain ⟨U, N, hxU, -, n₁, n₂, hU, G, hG, hM⟩ := hL x
  have hxN : π (y x) ∈ N := by
    have h := hU (show (⟨x, hxU⟩ : U) ∈ (⊤ : (U : Scheme.{0}).Opens) from trivial)
    have e : π (y x) = i (p x) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hyp]
    rw [e]
    exact h
  have hyP : y x ∈ (B.c α).C k ⊓ (B.c β).C l ⊓ π ⁻¹ᵁ N :=
    ⟨⟨h₁ (show x ∈ (⊤ : V.Opens) from trivial), h₂ (show x ∈ (⊤ : V.Opens) from trivial)⟩, hxN⟩
  obtain ⟨Q, hQ, hyQ, hQP⟩ := exists_isAffineOpen_mem_and_subset hyP
  have hq1 : ⊤ ≤ Q.ι ⁻¹ᵁ (B.c α).C k := fun z _ => (hQP z.2).1.1
  have hq2 : ⊤ ≤ Q.ι ⁻¹ᵁ (B.c β).C l := fun z _ => (hQP z.2).1.2
  have hqN : ⊤ ≤ (Q.ι ≫ π) ⁻¹ᵁ N := fun z _ => (hQP z.2).2
  have E := gvNzd B Q.ι α β k l hq1 hq2 n₁ n₂ hqN G hG (nzdRes B β l Q hQ hq2)
  let U' : V.Opens := U ⊓ y ⁻¹ᵁ Q
  have hxU' : x ∈ U' := ⟨hxU, hyQ⟩
  have hr : Set.range (U'.ι ≫ y) ⊆ Set.range Q.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  let s : (U' : Scheme.{0}) ⟶ Q := IsOpenImmersion.lift Q.ι (U'.ι ≫ y) hr
  have hs : s ≫ Q.ι = U'.ι ≫ y := IsOpenImmersion.lift_fac _ _ _
  let r : (U' : Scheme.{0}) ⟶ U := V.homOfLE inf_le_left
  have hr' : r ≫ U.ι = U'.ι := Scheme.homOfLE_ι _ _
  have em : r ≫ U.ι ≫ p ≫ i = s ≫ Q.ι ≫ π := by
    rw [← Category.assoc r, hr', ← Category.assoc s, hs, Category.assoc, hyp]
  have hh : ⊤ ≤ (s ≫ Q.ι ≫ π) ⁻¹ᵁ N := fun z _ => hqN (show s z ∈ (⊤ : (Q : Scheme.{0}).Opens) from trivial)
  have hh' : ⊤ ≤ (r ≫ U.ι ≫ p ≫ i) ⁻¹ᵁ N := em ▸ hh
  have hM' : M.map U'.ι.appTop.hom = (G.map ((Q.ι ≫ π).appLE N ⊤ hqN).hom).map s.appTop.hom := by
    ext a b
    simp only [Matrix.map_apply]
    have e1 := congrFun (congrFun hM a) b
    simp only [Matrix.map_apply] at e1
    have e2 : U'.ι.appTop.hom (M a b) = r.appTop.hom (U.ι.appTop.hom (M a b)) := by
      rw [← hr']
      rfl
    rw [e2, e1, appLE_pull r _ N hU hh', appLE_pull s _ N hqN hh]
    exact appLE_congr em N _ _ _
  have hs1 : ⊤ ≤ (s ≫ Q.ι) ⁻¹ᵁ (B.c α).C k := fun z _ => hq1 (show s z ∈ (⊤ : (Q : Scheme.{0}).Opens) from trivial)
  have hs2 : ⊤ ≤ (s ≫ Q.ι) ⁻¹ᵁ (B.c β).C l := fun z _ => hq2 (show s z ∈ (⊤ : (Q : Scheme.{0}).Opens) from trivial)
  have E1 := congrArg s.appTop.hom (congrFun E m)
  rw [left_pull B α k s Q.ι hq1 hs1 _ m, right_pull B α β k l s Q.ι hq1 hq2 hs1 hs2 m] at E1
  have key : ∀ (y₂ : (U' : Scheme.{0}) ⟶ Y) (_ : s ≫ Q.ι = y₂) (a₁ : ⊤ ≤ y₂ ⁻¹ᵁ (B.c α).C k)
      (a₂ : ⊤ ≤ y₂ ⁻¹ᵁ (B.c β).C l),
      ((G.map ((Q.ι ≫ π).appLE N ⊤ hqN).hom).map s.appTop.hom).mulVec (uV B α k y₂ a₁) m =
        ((((D.u (secOf B α k y₂ a₁) (secOf B β l y₂ a₂)
          ((secOf_f B α k y₂ a₁).trans (secOf_f B β l y₂ a₂).symm))⁻¹ : (Γ((U' : Scheme.{0}), ⊤))ˣ) :
            Γ((U' : Scheme.{0}), ⊤)) • uV B β l y₂ a₂) m := by
    intro y₂ e a₁ a₂
    subst e
    exact E1
  have h₁' : ⊤ ≤ (U'.ι ≫ y) ⁻¹ᵁ (B.c α).C k := fun z _ => h₁ (show z.1 ∈ (⊤ : V.Opens) from trivial)
  have h₂' : ⊤ ≤ (U'.ι ≫ y) ⁻¹ᵁ (B.c β).C l := fun z _ => h₂ (show z.1 ∈ (⊤ : V.Opens) from trivial)
  refine ⟨U', hxU', ?_⟩
  rw [left_pull B α k U'.ι y h₁ h₁' M m, right_pull B α β k l U'.ι y h₁ h₂ h₁' h₂' m, hM']
  exact key _ hs _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatExists
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma appTop_appLE {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (k : A ⟶ C) (h : f ≫ g = k)
    (N : C.Opens) (e₁ : ⊤ ≤ g ⁻¹ᵁ N) (e₂ : ⊤ ≤ k ⁻¹ᵁ N) (s : Γ(C, N)) :
    f.appTop.hom ((g.appLE N ⊤ e₁).hom s) = (k.appLE N ⊤ e₂).hom s := by
  subst h
  have e₀ : (⊤ : A.Opens) ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have h₀ : f.appLE ⊤ ⊤ e₀ = f.appTop := Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)
  have h := Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ e₁ e₀
  rw [h₀] at h
  rw [← h]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W), (∀ x : V, (p ≫ i) x ∈ B.V α ⊓ B.V β) → ∃ M : Matrix (Fin d) (Fin d) Γ(V, ⊤), LocMat B α β p M := by
  intro K _ W Z Y q i π D d B α β V p hp
  have hN : ∀ x : V, ∃ N : Z.Opens, IsAffineOpen N ∧ (p ≫ i) x ∈ N ∧ N ≤ B.V α ⊓ B.V β := fun x => by
    obtain ⟨N, h1, h2, h3⟩ := exists_isAffineOpen_mem_and_subset (hp x)
    exact ⟨N, h1, h2, h3⟩
  choose N hNa hNx hNle using hN
  have h₁ : ∀ x, N x ≤ B.V α := fun x => (hNle x).trans inf_le_left
  have h₂ : ∀ x, N x ≤ B.V β := fun x => (hNle x).trans inf_le_right
  choose G hG using fun x => trExists B α β (hNa x) (h₁ x) (h₂ x)
  let U : V → V.Opens := fun x => (p ≫ i) ⁻¹ᵁ N x
  have hxU : ∀ x, x ∈ U x := hNx
  have hU : ∀ x, ⊤ ≤ ((U x).ι ≫ p ≫ i) ⁻¹ᵁ N x := by
    intro x y _
    exact y.2
  let Mx : ∀ x, Matrix (Fin d) (Fin d) Γ((U x : Scheme.{0}), ⊤) := fun x =>
    (G x).map (((U x).ι ≫ p ≫ i).appLE (N x) ⊤ (hU x)).hom
  have hL : ∀ x, LocMat B α β ((U x).ι ≫ p) (Mx x) := by
    intro x y
    have hT : ⊤ ≤ ((⊤ : (U x : Scheme.{0}).Opens).ι ≫ ((U x).ι ≫ p) ≫ i) ⁻¹ᵁ N x := by
      intro z _
      exact z.1.2
    refine ⟨⊤, N x, trivial, hNa x, h₁ x, h₂ x, hT, G x, hG x, ?_⟩
    ext a b
    exact appTop_appLE _ _ _ (by simp) _ _ _ _
  have hglue : ∀ a b, ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = Mx x a b := by
    intro a b
    refine glueSection U hxU (fun x => Mx x a b) ?_
    intro x y S f f' hff
    have n1 := locMatNat B α β f ((U x).ι ≫ p) (Mx x) (hL x)
    have n2 := locMatNat B α β f' ((U y).ι ≫ p) (Mx y) (hL y)
    have e : f ≫ (U x).ι ≫ p = f' ≫ (U y).ι ≫ p := by
      rw [← Category.assoc, hff, Category.assoc]
    rw [e] at n1
    have := locMatUnique B α β _ _ _ n1 n2
    exact congrFun (congrFun this a) b
  choose M hM using hglue
  refine ⟨Matrix.of M, fun x => ⟨U x, N x, hxU x, hNa x, h₁ x, h₂ x, hU x, G x, hG x, ?_⟩⟩
  ext a b
  exact hM a b x
end

