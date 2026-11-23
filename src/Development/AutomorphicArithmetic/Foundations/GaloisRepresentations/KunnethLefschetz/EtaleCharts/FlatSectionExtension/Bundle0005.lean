module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatUnique
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem appLE_factor {A W Z : Scheme.{0}} (f : A ⟶ W) (i : W ⟶ Z) (c : A ⟶ Z) (hc : c = f ≫ i)
    {N N'' : Z.Opens} (hle : N'' ≤ N)
    (h : ⊤ ≤ c ⁻¹ᵁ N) (h'' : ⊤ ≤ f ⁻¹ᵁ (i ⁻¹ᵁ N'')) (g : Γ(Z, N)) :
    (c.appLE N ⊤ h).hom g =
      (f.appLE (i ⁻¹ᵁ N'') ⊤ h'').hom ((i.app N'').hom ((Z.presheaf.map (homOfLE hle).op).hom g)) := by
  subst hc
  have h1 : (f ≫ i).appLE N ⊤ h = Z.presheaf.map (homOfLE hle).op ≫ (f ≫ i).appLE N'' ⊤ (by simpa using h'') := by
    rw [Scheme.Hom.map_appLE]
  rw [h1, Scheme.Hom.comp_appLE]
  rfl

private theorem res_isTr {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z}
    {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {N N'' : Z.Opens} (hle : N'' ≤ N)
    (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β) (G : Matrix (Fin d) (Fin d) Γ(Z, N)) (hG : IsTr B α β h₁ h₂ G) :
    IsTr B α β (hle.trans h₁) (hle.trans h₂) (G.map (Z.presheaf.map (homOfLE hle).op).hom) := by
  intro m
  have e : ∀ (γ : B.ι) (hγ : N ≤ B.V γ) (l : Fin d), tN B γ (hle.trans hγ) l =
      (Z.presheaf.map (homOfLE hle).op).hom (tN B γ hγ l) := by
    intro γ hγ l
    simp only [tN, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e β h₂ m, hG m, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, e α h₁ l]
  rfl

private theorem pull_eq {V W Z : Scheme.{0}} (i : W ⟶ Z) (p : V ⟶ W) {U A : V.Opens} (hA : A ≤ U) {N : Z.Opens}
    (hU : ⊤ ≤ (U.ι ≫ p ≫ i) ⁻¹ᵁ N) (hA' : ⊤ ≤ (A.ι ≫ p ≫ i) ⁻¹ᵁ N) (s : Γ(V, ⊤)) (g : Γ(Z, N))
    (hs : U.ι.appTop.hom s = ((U.ι ≫ p ≫ i).appLE N ⊤ hU).hom g) :
    A.ι.appTop.hom s = ((A.ι ≫ p ≫ i).appLE N ⊤ hA').hom g := by
  have e : V.homOfLE hA ≫ U.ι = A.ι := Scheme.homOfLE_ι _ _
  have h1 : A.ι.appTop.hom s = (V.homOfLE hA).appTop.hom (U.ι.appTop.hom s) := by
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  rw [h1, hs]
  have cg : ∀ (f g : (A : Scheme.{0}) ⟶ Z) (_ : f = g) (h : ⊤ ≤ f ⁻¹ᵁ N) (h' : ⊤ ≤ g ⁻¹ᵁ N),
      f.appLE N ⊤ h = g.appLE N ⊤ h' := by
    rintro f _ rfl _ _
    rfl
  have h3 : (V.homOfLE hA).appTop = (V.homOfLE hA).appLE ⊤ ⊤ (le_of_eq rfl) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have h2 : (A.ι ≫ p ≫ i).appLE N ⊤ hA' =
      (U.ι ≫ p ≫ i).appLE N ⊤ hU ≫ (V.homOfLE hA).appTop := by
    rw [h3]
    exact (cg _ _ (by rw [← e, Category.assoc]) _ _).trans
      (Scheme.Hom.appLE_comp_appLE (V.homOfLE hA) (U.ι ≫ p ≫ i) N ⊤ ⊤ hU (le_of_eq rfl)).symm
  rw [h2]
  rfl

private theorem pt_mem {V W Z : Scheme.{0}} (i : W ⟶ Z) (p : V ⟶ W) (U : V.Opens) {N : Z.Opens}
    (y : (U : Scheme.{0})) : (U.ι ≫ p ≫ i) y ∈ N ↔ (p ≫ i) y.1 ∈ N := by
  have : (U.ι ≫ p ≫ i) y = (p ≫ i) y.1 := by
    rw [Scheme.Hom.comp_apply]
    rfl
  rw [this]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatUnique :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B α β p M' → M = M' := by
  intro K _ W Z Y q i π D d B α β V p M M' hM hM'
  ext m l
  refine sectionExt _ _ fun x => ?_
  obtain ⟨U, N, hx, hN, h₁, h₂, hU, G, hG, hMG⟩ := hM x
  obtain ⟨U', N', hx', hN', h₁', h₂', hU', G', hG', hMG'⟩ := hM' x
  have hzN : (p ≫ i) x ∈ N := (pt_mem i p U ⟨x, hx⟩).1 (hU (show (⟨x, hx⟩ : (U : Scheme.{0})) ∈ (⊤ : (U : Scheme.{0}).Opens) from trivial))
  have hzN' : (p ≫ i) x ∈ N' := (pt_mem i p U' ⟨x, hx'⟩).1 (hU' (show (⟨x, hx'⟩ : (U' : Scheme.{0})) ∈ (⊤ : (U' : Scheme.{0}).Opens) from trivial))
  obtain ⟨N'', hN'', hz, hsub⟩ := exists_isAffineOpen_mem_and_subset (U := N ⊓ N') (x := (p ≫ i) x) ⟨hzN, hzN'⟩
  have hle : N'' ≤ N := fun _ h => (hsub h).1
  have hle' : N'' ≤ N' := fun _ h => (hsub h).2
  let A : V.Opens := U ⊓ U' ⊓ (p ≫ i) ⁻¹ᵁ N''
  have hAU : A ≤ U := fun _ h => h.1.1
  have hAU' : A ≤ U' := fun _ h => h.1.2
  have hxA : x ∈ A := ⟨⟨hx, hx'⟩, hz⟩
  have hAz : ∀ y : (A : Scheme.{0}), (A.ι ≫ p ≫ i) y ∈ N'' := fun y => (pt_mem i p A y).2 y.2.2
  have hAN'' : ⊤ ≤ (A.ι ≫ p) ⁻¹ᵁ (i ⁻¹ᵁ N'') := by
    intro y _
    have := hAz y
    rw [← Category.assoc, Scheme.Hom.comp_apply] at this
    exact this
  have hAN : ⊤ ≤ (A.ι ≫ p ≫ i) ⁻¹ᵁ N := fun y _ => hle (hAz y)
  have hAN' : ⊤ ≤ (A.ι ≫ p ≫ i) ⁻¹ᵁ N' := fun y _ => hle' (hAz y)
  refine ⟨A, hxA, ?_⟩
  have e1 := pull_eq i p hAU hU hAN (M m l) (G m l) (congrFun (congrFun hMG m) l)
  have e2 := pull_eq i p hAU' hU' hAN' (M' m l) (G' m l) (congrFun (congrFun hMG' m) l)
  have t := trUnique B α β hN'' (hle.trans h₁) (hle.trans h₂)
    (G.map (Z.presheaf.map (homOfLE hle).op).hom) (G'.map (Z.presheaf.map (homOfLE hle').op).hom)
    (res_isTr B α β hle h₁ h₂ G hG) (res_isTr B α β hle' h₁' h₂' G' hG') m l
  rw [e1, e2, appLE_factor (A.ι ≫ p) i _ (Category.assoc _ _ _).symm hle hAN hAN'',
    appLE_factor (A.ι ≫ p) i _ (Category.assoc _ _ _).symm hle' hAN' hAN'']
  exact congrArg _ t
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.NzdRes
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem flat_mem_nzd {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) (hφ : φ.Flat) {a : A}
    (ha : a ∈ nonZeroDivisors A) : φ a ∈ nonZeroDivisors R := by
  algebraize [φ]
  have hreg : IsSMulRegular R a := Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  refine mem_nonZeroDivisors_iff_right.2 fun x hx => hreg ?_
  change a • x = a • (0 : R)
  rw [Algebra.smul_def, smul_zero, mul_comm]
  exact hx

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.nzdRes :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (β : B.ι) (l : Fin d) (Q : Y.Opens), IsAffineOpen Q → ∀ (h : ⊤ ≤ Q.ι ⁻¹ᵁ (B.c β).C l), (Q.ι.appLE ((B.c β).C l) ⊤ h).hom ((π.appLE (B.V β) ((B.c β).C l) ((B.c β).C_le l)).hom ((B.c β).t l)) ∈ nonZeroDivisors Γ((Q : Scheme.{0}), ⊤) := by
  intro K _ W Z Y q i π D d B β l Q hQ h
  have : IsAffine (Q : Scheme.{0}) := hQ
  have hfl : (Q.ι.appLE ((B.c β).C l) ⊤ h).hom.Flat :=
    HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) Q.ι inferInstance
      ⟨(B.c β).C l, (B.c β).C_aff l⟩ ⟨⊤, isAffineOpen_top _⟩ h
  exact flat_mem_nzd _ hfl (nzdChart B β l)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.OntoField
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem exists_basicOpen_of_span {V : Scheme.{0}} {d : ℕ} (v : Fin d → Γ(V, ⊤))
    (h : Ideal.span (Set.range v) = ⊤) (x : V) : ∃ k, x ∈ V.basicOpen (v k) := by
  by_contra hn
  push_neg at hn
  let φ : Γ(V, ⊤) →+* V.presheaf.stalk x := (V.presheaf.germ ⊤ x trivial).hom
  have hle : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ := by
    rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    have := hn k
    rw [Scheme.mem_basicOpen_top] at this
    exact (IsLocalRing.mem_maximalIdeal _).2 this
  rw [h] at hle
  have h1 : (1 : Γ(V, ⊤)) ∈ (IsLocalRing.maximalIdeal (V.presheaf.stalk x)).comap φ := hle trivial
  have h2 : φ 1 ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk x) := h1
  rw [map_one] at h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 isUnit_one

private theorem isUnit_restrict {V : Scheme.{0}} (s : Γ(V, ⊤)) (U : V.Opens) (hU : U ≤ V.basicOpen s) :
    IsUnit (U.ι.appTop.hom s) := by
  have h0 : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le s)).op).hom s) :=
    RingedSpace.isUnit_res_basicOpen _ _
  have hle : ⊤ ≤ U.ι ⁻¹ᵁ V.basicOpen s := by
    intro z _
    exact hU z.2
  have h1 : U.ι.appTop = V.presheaf.map (homOfLE (V.basicOpen_le s)).op ≫ U.ι.appLE (V.basicOpen s) ⊤ hle := by
    rw [Scheme.Hom.map_appLE]
    exact Scheme.Hom.app_eq_appLE U.ι
  rw [h1]
  exact h0.map (U.ι.appLE (V.basicOpen s) ⊤ hle).hom

private theorem uV_congr {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)}
    {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d)
    {V : Scheme.{0}} {f g : V ⟶ Y} (e : f = g) (h : ⊤ ≤ f ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ g ⁻¹ᵁ (B.c α).C k) :
    uV B α k f h = uV B α k g h' := by
  subst e; rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.ontoField :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hsq : IsPullback j r π i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ {V : Scheme.{0}} (a₀ : V ⟶ WP B) (v₀ : Um d Γ(V, ⊤)) (x : V), ∃ (U : V.Opens) (a : (U : Scheme.{0}) ⟶ TP B j) (u : (Γ((U : Scheme.{0}), ⊤))ˣ), x ∈ U ∧ a ≫ rhoP B j r hsq.w = U.ι ≫ a₀ ∧ a.appTop.hom ∘ v = (u : Γ((U : Scheme.{0}), ⊤)) • (U.ι.appTop.hom ∘ v₀.1) := by
  intro K _ W Z Y q i π D d B T j r hsq v hv V a₀ v₀ x
  obtain ⟨U₀, α, a₁, hx₀, ha₁⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a₀ x
  obtain ⟨k, hk⟩ := exists_basicOpen_of_span v₀.1 v₀.2 x
  let U : V.Opens := U₀ ⊓ V.basicOpen (v₀.1 k)
  obtain ⟨e, he⟩ := isUnit_restrict (v₀.1 k) U inf_le_right
  let a₂ : (U : Scheme.{0}) ⟶ (oW B α : Scheme.{0}) := V.homOfLE (inf_le_left : U ≤ U₀) ≫ a₁
  let p : (U : Scheme.{0}) ⟶ W := a₂ ≫ (oW B α).ι
  have hp : ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α := by
    intro z _
    have hz : (a₂ z).1 ∈ oW B α := (a₂ z).2
    exact hz
  let w : Fin d → Γ((U : Scheme.{0}), ⊤) := fun m => (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 m)
  have hwk : w k = 1 := by
    change (↑e⁻¹ : Γ((U : Scheme.{0}), ⊤)) * U.ι.appTop.hom (v₀.1 k) = 1
    rw [← he]; exact e.inv_mul
  obtain ⟨y, hy, hyr, huv⟩ := chartLift B j r hsq α k p hp w hwk
  have hrange : Set.range y ⊆ Set.range (oT B j (α, k)).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : (y ≫ j) z ∈ (B.c α).C k := hy (Set.mem_univ z)
    rw [Scheme.Hom.comp_apply] at hz
    exact hz
  let y₁ : (U : Scheme.{0}) ⟶ (oT B j (α, k) : Scheme.{0}) := IsOpenImmersion.lift (oT B j (α, k)).ι y hrange
  have hy₁ : y₁ ≫ (oT B j (α, k)).ι = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨h', hv', -, hrho⟩ := pieceFacts B j r hsq.w v hv (α, k) y₁
  have hpath : (y₁ ≫ tI B j (α, k)) ≫ eP B j ≫ j = y ≫ j := by
    have : tI B j (α, k) ≫ eP B j = (oT B j (α, k)).ι := by
      simp [tI, eP]
    rw [← hy₁, Category.assoc, reassoc_of% this, Category.assoc]
  have hmap : y₁ ≫ rhoC B j r hsq.w (α, k) = a₂ := by
    rw [← cancel_mono (oW B α).ι]
    have : rhoC B j r hsq.w (α, k) ≫ (oW B α).ι = (oT B j (α, k)).ι ≫ r := IsOpenImmersion.lift_fac _ _ _
    rw [Category.assoc, this, reassoc_of% hy₁, hyr]
  refine ⟨U, y₁ ≫ tI B j (α, k), e⁻¹, ⟨hx₀, hk⟩, ?_, ?_⟩
  · rw [hrho, hmap]
    have hι : U.ι ≫ a₀ = V.homOfLE (inf_le_left : U ≤ U₀) ≫ U₀.ι ≫ a₀ := by
      rw [← Category.assoc, Scheme.homOfLE_ι]
    rw [hι, ha₁]
    simp only [a₂, Category.assoc]
    rfl
  · rw [hv', uV_congr B α k hpath h' hy, huv]
    rfl
end

