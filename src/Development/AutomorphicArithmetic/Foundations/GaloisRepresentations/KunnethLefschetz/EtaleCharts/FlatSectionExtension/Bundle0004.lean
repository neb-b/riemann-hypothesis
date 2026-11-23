module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.RegSeq

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ExistsV
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.existsV :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y), ∃ v : Fin d → Γ(TP B j, ⊤), IsV B j v ∧ Ideal.span (Set.range v) = ⊤ := by
  intro K _ W Z Y q i π D d B T j
  classical
  let X : B.ι × Fin d → Scheme.{0} := fun p => (oT B j p : Scheme.{0})
  choose v hv _ using fun m : Fin d =>
    sigmaSection X (fun p => uV B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p) m)
  refine ⟨v, fun p m => hv m p, ?_⟩
  choose b hb _ using fun m : Fin d =>
    sigmaSection X (fun p => if p.2 = m then (1 : Γ(X p, ⊤)) else 0)
  obtain ⟨s, -, hs⟩ := sigmaSection X (fun _ => 1)
  have h1 : (∑ m, b m * v m) = 1 := by
    have e2 := hs 1 (fun p => map_one _)
    have e1 : (∑ m, b m * v m) = s := by
      refine hs _ fun p => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_mul, hb, hv]
      simp [uSelf]
    rw [e1, e2]
  rw [Ideal.eq_top_iff_one, ← h1]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨m, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatComp
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem map_map_appTop {A B C : Scheme.{0}} {d : ℕ} (f : A ⟶ B) (g : B ⟶ C)
    (M : Matrix (Fin d) (Fin d) Γ(C, ⊤)) :
    (M.map g.appTop.hom).map f.appTop.hom = M.map (f ≫ g).appTop.hom := by
  ext m n
  simp only [Matrix.map_apply, Scheme.Hom.comp_appTop]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatComp :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b k : V ⟶ WP B) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), a ≫ cP B = b ≫ cP B → GMat B a b M → GMat B b k M' → GMat B a k (M' * M) := by
  intro K _ W Z Y q i π D d B V a b k M M' hab h₁ h₂ x
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := h₁ x
  obtain ⟨U', β', γ, b₂, k₂, hx', hb', hk', hL'⟩ := h₂ x
  let e : ((U ⊓ U' : V.Opens) : Scheme.{0}) ⟶ U := V.homOfLE inf_le_left
  let e' : ((U ⊓ U' : V.Opens) : Scheme.{0}) ⟶ U' := V.homOfLE inf_le_right
  have he : e ≫ U.ι = (U ⊓ U').ι := V.homOfLE_ι _
  have he' : e' ≫ U'.ι = (U ⊓ U').ι := V.homOfLE_ι _
  have hβ : β = β' := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun α : B.ι => (oW B α : Scheme.{0})) (e ≫ b₁) (e' ≫ b₂)
      (⟨x, hx, hx'⟩ : ((U ⊓ U' : V.Opens) : Scheme.{0})) ?_
    change (e ≫ b₁) ≫ wI B β = (e' ≫ b₂) ≫ wI B β'
    rw [Category.assoc, Category.assoc, ← hb, ← hb', ← Category.assoc, ← Category.assoc, he, he']
  subst hβ
  refine ⟨U ⊓ U', α, γ, e ≫ a₁, e' ≫ k₂, ⟨hx, hx'⟩, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← ha, ← Category.assoc, he]
  · rw [Category.assoc, ← hk', ← Category.assoc, he']
  · have n₁ := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat B α β e _ _ hL
    have n₂ := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat B β γ e' _ _ hL'
    rw [map_map_appTop, he, ← Category.assoc, he] at n₁
    rw [map_map_appTop, he', ← Category.assoc, he', ← hab] at n₂
    have := UpperTheory.Gal.KunnethLefschetz.G.PX.locMatComp B α β γ _ _ _ n₁ n₂
    rwa [← Matrix.map_mul] at this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatLoc
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatLoc :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a b : V ⟶ WP B) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)) (α β : B.ι) (a₁ : V ⟶ (oW B α : Scheme.{0})) (b₁ : V ⟶ (oW B β : Scheme.{0})), a = a₁ ≫ wI B α → b = b₁ ≫ wI B β → GMat B a b M → LocMat B α β (a ≫ cP B) M := by
  intro K _ W Z Y q i π D d B V a b M α β a₁ b₁ ha hb hG
  refine UpperTheory.Gal.KunnethLefschetz.G.PX.locMatLocal B α β (a ≫ cP B) M fun x => ?_
  obtain ⟨U, α', β', a', b', hx, h1, h2, hL⟩ := hG x
  have e1 : α' = α := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun γ : B.ι => (oW B γ : Scheme.{0})) a' (U.ι ≫ a₁) (⟨x, hx⟩ : U) ?_
    have h : a' ≫ wI B α' = (U.ι ≫ a₁) ≫ wI B α := by
      rw [← h1, ha, Category.assoc]
    exact h
  have e2 : β' = β := by
    refine UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj (fun γ : B.ι => (oW B γ : Scheme.{0})) b' (U.ι ≫ b₁) (⟨x, hx⟩ : U) ?_
    have h : b' ≫ wI B β' = (U.ι ≫ b₁) ≫ wI B β := by
      rw [← h2, hb, Category.assoc]
    exact h
  subst e1 e2
  exact ⟨U, hx, hL⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatNat
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V' V : Scheme.{0}} (s : V' ⟶ V) (a b : V ⟶ WP B) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), GMat B a b M → GMat B (s ≫ a) (s ≫ b) (M.map s.appTop.hom) := by
  intro K _ W Z Y q i π D d B V' V s a b M h x'
  obtain ⟨U, α, β, a₁, b₁, hx, ha, hb, hL⟩ := h (s x')
  have hι : (s ∣_ U) ≫ U.ι = (s ⁻¹ᵁ U).ι ≫ s := morphismRestrict_ι s U
  refine ⟨s ⁻¹ᵁ U, α, β, (s ∣_ U) ≫ a₁, (s ∣_ U) ≫ b₁, hx, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← ha, reassoc_of% hι]
  · rw [Category.assoc, ← hb, reassoc_of% hι]
  · have h2 := locMatNat B α β (s ∣_ U) _ _ hL
    have e1 : (s ∣_ U) ≫ U.ι ≫ a ≫ cP B = (s ⁻¹ᵁ U).ι ≫ (s ≫ a) ≫ cP B := by
      rw [← Category.assoc, hι]; simp only [Category.assoc]
    have e2 : ((M.map U.ι.appTop.hom).map (s ∣_ U).appTop.hom) =
        ((M.map s.appTop.hom).map (s ⁻¹ᵁ U).ι.appTop.hom) := by
      ext m l
      simp only [Matrix.map_apply]
      have h3 : U.ι.appTop ≫ (s ∣_ U).appTop = s.appTop ≫ (s ⁻¹ᵁ U).ι.appTop := by
        rw [← Scheme.Hom.comp_appTop, hι, Scheme.Hom.comp_appTop]
      exact congrArg (fun f => f.hom (M m l)) h3
    rw [e1, e2] at h2
    exact h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GMatOne
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gMatOne :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (a : V ⟶ WP B), GMat B a a 1 := by
  intro K _ W Z Y q i π D d B V a x
  obtain ⟨U, α, a₁, hx, ha⟩ := sigmaLocal (fun α : B.ι => (oW B α : Scheme.{0})) a x
  refine ⟨U, α, α, a₁, a₁, hx, ha, ha, ?_⟩
  have hc : U.ι ≫ a ≫ cP B = a₁ ≫ (oW B α).ι := by
    have h : wI B α ≫ cP B = (oW B α).ι := by
      simp [wI, cP]
    rw [← Category.assoc, show U.ι ≫ a = a₁ ≫ wI B α from ha, Category.assoc, h]
  have h1 : (1 : Matrix (Fin d) (Fin d) Γ(V, ⊤)).map U.ι.appTop.hom = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1]
  refine locMatOne B α _ fun y => ?_
  rw [hc, Category.assoc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
  exact (a₁ y).2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.NzdChart
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.nzdChart :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d), (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k) ∈ nonZeroDivisors Γ(Y, (B.c α).C k) := by
  intro K _ W Z Y q i π D d B α k
  exact UpperTheory.Gal.KunnethLefschetz.G.PX.chartNzdAlg
    (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x)
    (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom
    (B.c α).t ((B.c α).u k) k
    (UpperTheory.Gal.KunnethLefschetz.G.PX.etaleSplit B α) ((B.c α).surj k) ((B.c α).rel k)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.PieceFacts
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem e1 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) :
    tI B j p ≫ eP B j = (oT B j p).ι := by
  unfold tI eP
  rw [Sigma.ι_desc]

private theorem e2 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (p : B.ι × Fin d) :
    tI B j p ≫ tauP B j = secOf B p.1 p.2 ((oT B j p).ι ≫ j) (oT_le B j p) := by
  unfold tI tauP
  rw [Sigma.ι_desc]

private theorem e3 {K : Type} [CommRing K] {W Z Y T : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
    {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) (p : B.ι × Fin d) :
    tI B j p ≫ rhoP B j r hw = rhoC B j r hw p ≫ wI B p.1 := by
  unfold tI rhoP
  rw [Sigma.ι_desc]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.pieceFacts :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i) (v : Fin d → Γ(TP B j, ⊤)), IsV B j v → ∀ (p : B.ι × Fin d) {V : Scheme.{0}} (a₁ : V ⟶ (oT B j p : Scheme.{0})), ∃ h : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p.1).C p.2, (a₁ ≫ tI B j p).appTop.hom ∘ v = uV B p.1 p.2 _ h ∧ (a₁ ≫ tI B j p) ≫ tauP B j = secOf B p.1 p.2 _ h ∧ (a₁ ≫ tI B j p) ≫ rhoP B j r hw = (a₁ ≫ rhoC B j r hw p) ≫ wI B p.1 := by
  intro K _ W Z Y q i π D d B T j r hw v hv p V a₁
  have ey : (a₁ ≫ tI B j p) ≫ eP B j ≫ j = a₁ ≫ (oT B j p).ι ≫ j := by
    rw [Category.assoc, ← Category.assoc (tI B j p), e1]
  have hle : ⊤ ≤ (a₁ ≫ (oT B j p).ι ≫ j) ⁻¹ᵁ (B.c p.1).C p.2 := by
    intro x _
    have := oT_le B j p (Set.mem_univ (a₁ x))
    simpa using this
  have key : ∀ (y' : V ⟶ Y) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c p.1).C p.2), y' = a₁ ≫ (oT B j p).ι ≫ j →
      (a₁ ≫ tI B j p).appTop.hom ∘ v = uV B p.1 p.2 y' h' ∧
        (a₁ ≫ tI B j p) ≫ tauP B j = secOf B p.1 p.2 y' h' := by
    rintro y' h' rfl
    obtain ⟨n1, n2⟩ := chartNat B p.1 p.2 a₁ ((oT B j p).ι ≫ j) (oT_le B j p) h'
    refine ⟨?_, ?_⟩
    · funext m
      rw [n1 m, ← hv p m]
      rw [Function.comp_apply, Scheme.Hom.comp_appTop]
      rfl
    · rw [n2, Category.assoc, e2]
  have h : ⊤ ≤ ((a₁ ≫ tI B j p) ≫ eP B j ≫ j) ⁻¹ᵁ (B.c p.1).C p.2 := by
    rw [ey]; exact hle
  obtain ⟨k1, k2⟩ := key _ h ey
  exact ⟨h, k1, k2, by rw [Category.assoc, e3, Category.assoc]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.TrExists
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.trExists :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β), ∃ G : Matrix (Fin d) (Fin d) Γ(Z, N), IsTr B α β h₁ h₂ G := by
  intro K _ W Z Y q i π D d B α β N hN h₁ h₂
  have key : ∀ m, ∃ c : Fin d → Γ(Z, N), ∑ l, c l * tN B α h₁ l = tN B β h₂ m := by
    intro m
    have hm : tN B β h₂ m ∈ Ideal.span (Set.range (tN B α h₁)) := by
      rw [← kerRes B α hN h₁, kerRes B β hN h₂]
      exact Ideal.subset_span ⟨m, rfl⟩
    exact Ideal.mem_span_range_iff_exists_fun.1 hm
  choose G hG using key
  exact ⟨Matrix.of G, fun m => (hG m).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.TrUnique
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma flat_of_etale {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (h : f.Etale) : f.Flat := by
  letI := f.toAlgebra
  haveI : Algebra.Etale A B := h
  exact (inferInstance : Module.Flat A B)

private lemma flat_res {X : Scheme.{0}} {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U) :
    (X.presheaf.map (homOfLE h).op).hom.Flat := by
  have e : V ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U := h
  have h1 := HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) (Q := RingHom.Flat) (𝟙 X)
    (inferInstance : AlgebraicGeometry.Flat (𝟙 X)) ⟨U, hU⟩ ⟨V, hV⟩ e
  have h2 : (𝟙 X : X ⟶ X).appLE U V e = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE]
    exact Category.id_comp _
  simpa only [h2] using h1

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.trUnique :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h₁ : N ≤ B.V α) (h₂ : N ≤ B.V β) (G G' : Matrix (Fin d) (Fin d) Γ(Z, N)), IsTr B α β h₁ h₂ G → IsTr B α β h₁ h₂ G' → ∀ m l, (i.app N).hom (G m l) = (i.app N).hom (G' m l) := by
  intro K _ W Z Y q i π D d B α β N hN h₁ h₂ G G' hG hG' m l
  let φ₀ : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α) :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t
  let φ : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, N) :=
    (Z.presheaf.map (homOfLE h₁).op).hom.comp φ₀
  have hflat : φ.Flat :=
    RingHom.Flat.comp (flat_of_etale φ₀ (etaleSplit B α)) (flat_res (B.c α).affine hN h₁)
  have hX : ∀ l, φ (MvPolynomial.X l) = tN B α h₁ l := by
    intro l
    simp [φ, φ₀, tN]
  have hfun : (fun l => φ (MvPolynomial.X l)) = tN B α h₁ := funext hX
  have hzero : ∑ l, (G m l - G' m l) * φ (MvPolynomial.X l) = 0 := by
    simp only [hX, sub_mul, Finset.sum_sub_distrib]
    rw [← hG m, ← hG' m, sub_self]
  have key := UpperTheory.Gal.KunnethLefschetz.G.regSeq _ _ d φ hflat (fun l => G m l - G' m l)
    (by rw [hzero]; exact zero_mem _) l
  rw [hfun, ← kerRes B α hN h₁, RingHom.mem_ker, map_sub] at key
  exact sub_eq_zero.mp key
end

