module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.BlowupChartRelation
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z}
  {D : E.LineData Y} {d : ℕ}

private theorem blowup_chart_relation (B : Blow q i π D d) (α : B.ι) (k n : Fin d) :
    (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t n) =
      (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k) * (B.c α).u k n := by
  have hmem : (MvPolynomial.C ((B.c α).t n) - MvPolynomial.C ((B.c α).t k) * MvPolynomial.X n :
      MvPolynomial (Fin d) Γ(Z, B.V α)) ∈
      RingHom.ker (MvPolynomial.eval₂Hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom) ((B.c α).u k)) := by
    rw [(B.c α).rel k]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨n, rfl⟩)
  have h0 := RingHom.mem_ker.mp hmem
  rw [map_sub, map_mul, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_C] at h0
  exact sub_eq_zero.mp h0

private theorem res_chain {V : Scheme.{0}} (y : V ⟶ Y) {A N : Z.Opens} {C : Y.Opens} (hC : C ≤ π ⁻¹ᵁ A)
    (h : ⊤ ≤ y ⁻¹ᵁ C) (n : N ≤ A) (hy : ⊤ ≤ (y ≫ π) ⁻¹ᵁ N) (s : Γ(Z, A)) :
    (y.appLE C ⊤ h).hom ((π.appLE A C hC).hom s) =
      ((y ≫ π).appLE N ⊤ hy).hom ((Z.presheaf.map (homOfLE n).op).hom s) := by
  have e1 := Scheme.Hom.appLE_comp_appLE y π A C ⊤ hC h
  have e2 := Scheme.Hom.map_appLE (y ≫ π) hy (homOfLE n).op
  have : π.appLE A C hC ≫ y.appLE C ⊤ h = Z.presheaf.map (homOfLE n).op ≫ (y ≫ π).appLE N ⊤ hy := by
    rw [e1, e2]
  exact congrArg (fun φ => φ.hom s) this

private theorem top_inv {V : Scheme.{0}} {C : Y.Opens} (g : V ⟶ (C : Scheme.{0})) (h : ⊤ ≤ (g ≫ C.ι) ⁻¹ᵁ C) (s : Γ(Y, C)) :
    g.appTop.hom (C.topIso.inv.hom s) = ((g ≫ C.ι).appLE C ⊤ h).hom s := by
  have e0 : (⊤ : (C : Scheme.{0}).Opens) ≤ C.ι ⁻¹ᵁ C := fun x _ => x.2
  have e1 := Scheme.Hom.appLE_comp_appLE g C.ι C ⊤ ⊤ e0 (fun x _ => trivial)
  have e2 : C.ι.appLE C ⊤ e0 = C.topIso.inv := by
    simp only [Scheme.Hom.appLE, Scheme.Opens.ι_app, Scheme.Opens.topIso_inv, Scheme.Opens.toScheme_presheaf_map]
    refine (Y.presheaf.map_comp _ _).symm.trans ?_
    exact congrArg _ (Subsingleton.elim _ _)
  have e3 : g.appLE ⊤ ⊤ (fun x _ => trivial) = g.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg (g.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)
  rw [e2, e3] at e1
  exact congrArg (fun φ => φ.hom s) e1

private theorem f_sec (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y : V ⟶ Y)
    (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) :
    B.f (secOf B α k y h) =
      (y.appLE ((B.c α).C k) ⊤ h).hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k)) := by
  unfold secOf
  rw [B.f_nat, B.f_σ]
  have hg : IsOpenImmersion.lift ((B.c α).C k).ι y (chart_range B α k y h) ≫ ((B.c α).C k).ι = y :=
    IsOpenImmersion.lift_fac _ _ _
  have := top_inv (IsOpenImmersion.lift ((B.c α).C k).ι y (chart_range B α k y h)) (by rw [hg]; exact h)
    ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k))
  rw [this]
  simp only [hg]

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.gvNzd :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {V : Scheme.{0}} (y : V ⟶ Y) (α β : B.ι) (k l : Fin d) (h₁ : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h₂ : ⊤ ≤ y ⁻¹ᵁ (B.c β).C l) {N : Z.Opens} (n₁ : N ≤ B.V α) (n₂ : N ≤ B.V β) (hy : ⊤ ≤ (y ≫ π) ⁻¹ᵁ N) (G : Matrix (Fin d) (Fin d) Γ(Z, N)), IsTr B α β n₁ n₂ G → (y.appLE ((B.c β).C l) ⊤ h₂).hom ((π.appLE (B.V β) ((B.c β).C l) ((B.c β).C_le l)).hom ((B.c β).t l)) ∈ nonZeroDivisors Γ(V, ⊤) → (G.map ((y ≫ π).appLE N ⊤ hy).hom).mulVec (uV B α k y h₁) = (((D.u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm))⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) • uV B β l y h₂ := by
  intro K _ W Z Y q i π D d B V y α β k l h₁ h₂ N n₁ n₂ hy G hG hnz
  set a := ((y ≫ π).appLE N ⊤ hy).hom with ha
  set Tk := (y.appLE ((B.c α).C k) ⊤ h₁).hom ((π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).t k)) with hTk
  set Tl := (y.appLE ((B.c β).C l) ⊤ h₂).hom ((π.appLE (B.V β) ((B.c β).C l) ((B.c β).C_le l)).hom ((B.c β).t l)) with hTl
  set u := D.u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm) with hu
  have hα : ∀ n, a (tN B α n₁ n) = Tk * uV B α k y h₁ n := by
    intro n
    have := res_chain y ((B.c α).C_le k) h₁ n₁ hy ((B.c α).t n)
    rw [blowup_chart_relation, map_mul] at this
    exact this.symm
  have hβ : ∀ n, a (tN B β n₂ n) = Tl * uV B β l y h₂ n := by
    intro n
    have := res_chain y ((B.c β).C_le l) h₂ n₂ hy ((B.c β).t n)
    rw [blowup_chart_relation, map_mul] at this
    exact this.symm
  have hf : Tk = (u : Γ(V, ⊤)) * Tl := by
    have := B.f_u (secOf B α k y h₁) (secOf B β l y h₂) ((secOf_f B α k y h₁).trans (secOf_f B β l y h₂).symm)
    rwa [f_sec, f_sec] at this
  funext m
  have hm : Tl * uV B β l y h₂ m = Tk * (G.map a).mulVec (uV B α k y h₁) m := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hβ, hG m, map_sum, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, hα, Matrix.map_apply]
    ring
  rw [hf] at hm
  have h3 : Tl * (uV B β l y h₂ m - (u : Γ(V, ⊤)) * (G.map a).mulVec (uV B α k y h₁) m) = 0 := by
    rw [mul_sub, hm]; ring
  have h4 := sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hnz _ (by rwa [mul_comm] at h3))
  rw [Pi.smul_apply, smul_eq_mul, h4, Units.inv_mul_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartInj
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma appLE_univ_congr_of_eq {V Z : Scheme.{0}} {f g : V ⟶ Z} (hfg : f = g) (U : Z.Opens)
    (e : ⊤ ≤ f ⁻¹ᵁ U) (e' : ⊤ ≤ g ⁻¹ᵁ U) : f.appLE U ⊤ e = g.appLE U ⊤ e' := by
  subst hfg; rfl

private lemma appLE_lift_eq {Y V : Scheme.{0}} (C : Y.Opens) (l : V ⟶ (C : Scheme.{0}))
    (h : ⊤ ≤ (l ≫ C.ι) ⁻¹ᵁ C) : (l ≫ C.ι).appLE C ⊤ h = C.topIso.inv ≫ l.appTop := by
  rw [← Scheme.Hom.appLE_comp_appLE l C.ι C ⊤ ⊤ (by simp) (by simp), Scheme.Hom.appTop,
    Scheme.Hom.app_eq_appLE, Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  simp
  congr 1

private lemma eq_of_appLE_eq {Y V : Scheme.{0}} (C : Y.Opens) (hC : IsAffineOpen C) (y y' : V ⟶ Y)
    (h : ⊤ ≤ y ⁻¹ᵁ C) (h' : ⊤ ≤ y' ⁻¹ᵁ C) (e : y.appLE C ⊤ h = y'.appLE C ⊤ h') : y = y' := by
  have r : ∀ z : V ⟶ Y, ⊤ ≤ z ⁻¹ᵁ C → Set.range z ⊆ Set.range C.ι := by
    rintro z hz _ ⟨x, rfl⟩
    simpa using hz (Set.mem_univ x)
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ C.ι = y := ⟨_, IsOpenImmersion.lift_fac C.ι y (r y h)⟩
  obtain ⟨l', rfl⟩ : ∃ l, l ≫ C.ι = y' := ⟨_, IsOpenImmersion.lift_fac C.ι y' (r y' h')⟩
  haveI : IsAffine (C : Scheme.{0}) := hC
  rw [appLE_lift_eq, appLE_lift_eq] at e
  have e2 : l.appTop = l'.appTop := (cancel_epi C.topIso.inv).mp e
  rw [ext_of_isAffine e2]

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartInj :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V : Scheme.{0}} (y y' : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), y ≫ π = y' ≫ π → uV B α k y h = uV B α k y' h' → y = y' := by
  intro K _ W Z Y q i π D d B α k V y y' h h' hπ hu
  have hle := (B.c α).C_le k
  refine eq_of_appLE_eq _ ((B.c α).C_aff k) y y' h h' ?_
  have hpi : ∀ r : Γ(Z, B.V α), (y.appLE _ ⊤ h).hom ((π.appLE (B.V α) _ hle).hom r) =
      (y'.appLE _ ⊤ h').hom ((π.appLE (B.V α) _ hle).hom r) := by
    intro r
    have e1 := Scheme.Hom.appLE_comp_appLE y π (B.V α) ((B.c α).C k) ⊤ hle h
    have e2 := Scheme.Hom.appLE_comp_appLE y' π (B.V α) ((B.c α).C k) ⊤ hle h'
    have e3 := e1.trans ((appLE_univ_congr_of_eq hπ (B.V α) _ _).trans e2.symm)
    exact congrArg (fun t => t.hom r) e3
  have hP := MvPolynomial.ringHom_ext
    (f := (y.appLE _ ⊤ h).hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (g := (y'.appLE _ ⊤ h').hom.comp (MvPolynomial.eval₂Hom (π.appLE (B.V α) _ hle).hom ((B.c α).u k)))
    (fun r => by simpa using hpi r)
    (fun m => by simpa [uV] using congrFun hu m)
  refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
  obtain ⟨P, rfl⟩ := (B.c α).surj k s
  exact congrArg (fun t => t P) hP
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartLift
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem fromSpec_appLE_top {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) : hU.fromSpec.appLE U ⊤ h = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _ using 2
  exact CategoryTheory.Functor.map_id _ _

private theorem appLE_top_top {V X : Scheme.{0}} (a : V ⟶ X) (e : (⊤ : V.Opens) ≤ a ⁻¹ᵁ ⊤) :
    a.appLE ⊤ ⊤ e = a.appTop := by
  change a.app ⊤ ≫ V.presheaf.map (homOfLE e).op = a.app ⊤
  exact (congrArg (a.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)

private theorem exists_hom_of_ring {V X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U) ⟶ Γ(V, ⊤)) :
    ∃ (y : V ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ U), y.appLE U ⊤ h = f := by
  have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have e₂ : (⊤ : V.Opens) ≤ (V.toSpecΓ ≫ Spec.map f) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  refine ⟨(V.toSpecΓ ≫ Spec.map f) ≫ hU.fromSpec, ?_, ?_⟩
  · exact e₂.trans (Scheme.Hom.preimage_mono _ e₁)
  · rw [← Scheme.Hom.appLE_comp_appLE _ _ U ⊤ ⊤ e₁ e₂, fromSpec_appLE_top]
    have : (V.toSpecΓ ≫ Spec.map f).appLE ⊤ ⊤ e₂ = (Spec.map f).appTop ≫ (Scheme.ΓSpecIso Γ(V, ⊤)).hom := by
      rw [appLE_top_top, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    rw [this, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

private theorem hom_eq_of_appLE {V X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (a b : V ⟶ X)
    (ha : ⊤ ≤ a ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ U) (h : a.appLE U ⊤ ha = b.appLE U ⊤ hb) : a = b := by
  have key : ∀ (c : V ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ U), ∃ c' : V ⟶ Spec Γ(X, U), c' ≫ hU.fromSpec = c ∧
      c'.appTop = (Scheme.ΓSpecIso Γ(X, U)).hom ≫ c.appLE U ⊤ hc := by
    intro c hc
    have hr : Set.range c ⊆ Set.range hU.fromSpec := by
      rw [hU.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact hc (Set.mem_univ x)
    refine ⟨IsOpenImmersion.lift hU.fromSpec c hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    have e₁ : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
    have e₂ : (⊤ : V.Opens) ≤ (IsOpenImmersion.lift hU.fromSpec c hr) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    have := Scheme.Hom.appLE_comp_appLE (IsOpenImmersion.lift hU.fromSpec c hr) hU.fromSpec U ⊤ ⊤ e₁ e₂
    rw [fromSpec_appLE_top, appLE_top_top] at this
    have h2 : (IsOpenImmersion.lift hU.fromSpec c hr ≫ hU.fromSpec).appLE U ⊤
        (by rw [IsOpenImmersion.lift_fac]; exact hc) = c.appLE U ⊤ hc := by
      simp only [IsOpenImmersion.lift_fac]
    rw [← this.trans h2, Iso.hom_inv_id_assoc]
  obtain ⟨a', ha', ea⟩ := key a ha
  obtain ⟨b', hb', eb⟩ := key b hb
  rw [← ha', ← hb', ext_of_isAffine (f := a') (g := b') (by rw [ea, eb, h])]

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartLift :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W), IsPullback j r π i → ∀ (α : B.ι) (k : Fin d) {V : Scheme.{0}} (p : V ⟶ W), ⊤ ≤ (p ≫ i) ⁻¹ᵁ B.V α → ∀ (w : Fin d → Γ(V, ⊤)), w k = 1 → ∃ (y : V ⟶ T) (h : ⊤ ≤ (y ≫ j) ⁻¹ᵁ (B.c α).C k), y ≫ r = p ∧ uV B α k (y ≫ j) h = w := by
  intro K _ W Z Y q i π D d B T j r hpb α k V p hp w hk
  have ht : ∀ m, ((p ≫ i).appLE (B.V α) ⊤ hp).hom ((B.c α).t m) = 0 := by
    intro m
    have hm : (B.c α).t m ∈ RingHom.ker (i.app (B.V α)).hom := by
      rw [(B.c α).ker]
      exact Ideal.subset_span ⟨m, rfl⟩
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.mem_ker.mp hm, map_zero]
  let ψ := MvPolynomial.eval₂Hom (π.appLE (B.V α) ((B.c α).C k) ((B.c α).C_le k)).hom ((B.c α).u k)
  let φ : MvPolynomial (Fin d) Γ(Z, B.V α) →+* Γ(V, ⊤) :=
    MvPolynomial.eval₂Hom ((p ≫ i).appLE (B.V α) ⊤ hp).hom w
  have hφC : ∀ a, φ (MvPolynomial.C a) = ((p ≫ i).appLE (B.V α) ⊤ hp).hom a := fun a =>
    MvPolynomial.eval₂_C _ _ _
  have hker : RingHom.ker ψ ≤ RingHom.ker φ := by
    change RingHom.ker (MvPolynomial.eval₂Hom _ _) ≤ _
    rw [(B.c α).rel k, Ideal.span_le]
    rintro x (rfl | ⟨m, rfl⟩)
    · simp [φ, hk]
    · change φ _ = 0
      rw [map_sub, map_mul, hφC, hφC, ht, ht, zero_mul, sub_zero]
  let f : Γ(Y, (B.c α).C k) →+* Γ(V, ⊤) := RingHom.liftOfSurjective ψ ((B.c α).surj k) ⟨φ, hker⟩
  have hf : ∀ x, f (ψ x) = φ x := fun x =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨φ, hker⟩ x
  obtain ⟨y₀, h₀, hy₀⟩ := exists_hom_of_ring ((B.c α).C_aff k) (CommRingCat.ofHom f)
  have hπ : ⊤ ≤ (y₀ ≫ π) ⁻¹ᵁ B.V α := h₀.trans (Scheme.Hom.preimage_mono _ ((B.c α).C_le k))
  have hc : y₀ ≫ π = p ≫ i := by
    refine hom_eq_of_appLE (B.c α).affine _ _ hπ hp ?_
    rw [← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ ((B.c α).C_le k) h₀, hy₀]
    ext a
    have := hf (MvPolynomial.C a)
    simpa [ψ, φ] using this
  have hyj : hpb.lift y₀ p hc ≫ j = y₀ := hpb.lift_fst _ _ _
  refine ⟨hpb.lift y₀ p hc, by rw [hyj]; exact h₀, hpb.lift_snd _ _ _, ?_⟩
  have gen : ∀ (y' : V ⟶ Y) (e : y' = y₀) (h : ⊤ ≤ y' ⁻¹ᵁ (B.c α).C k), uV B α k y' h = w := by
    intro y' e h
    have hy' : Scheme.Hom.appLE y' _ ⊤ h = CommRingCat.ofHom f := by
      subst e
      exact hy₀
    funext m
    have := hf (MvPolynomial.X m)
    simp only [ψ, φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    unfold uV
    rw [hy']
    exact this
  exact gen _ hyj _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartNat
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) (k : Fin d) {V' V : Scheme.{0}} (s : V' ⟶ V) (y : V ⟶ Y) (h : ⊤ ≤ y ⁻¹ᵁ (B.c α).C k) (h' : ⊤ ≤ (s ≫ y) ⁻¹ᵁ (B.c α).C k), (∀ m, uV B α k (s ≫ y) h' m = s.appTop.hom (uV B α k y h m)) ∧ secOf B α k (s ≫ y) h' = s ≫ secOf B α k y h := by
  intro K _ W Z Y q i π D d B α k V' V s y h h'
  constructor
  · intro m
    have hs : (⊤ : V'.Opens) ≤ s ⁻¹ᵁ (⊤ : V.Opens) := le_rfl
    have key : (s ≫ y).appLE ((B.c α).C k) ⊤ h' = y.appLE ((B.c α).C k) ⊤ h ≫ s.appTop := by
      have h1 := Scheme.Hom.appLE_comp_appLE s y ((B.c α).C k) ⊤ ⊤ h hs
      rw [← h1]
      congr 1
      simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
      change _ ≫ V'.presheaf.map (𝟙 _) = _
      rw [CategoryTheory.Functor.map_id, Category.comp_id]
    unfold uV
    rw [key]
    rfl
  · unfold secOf
    rw [← Category.assoc]
    congr 1
    symm
    apply IsOpenImmersion.lift_uniq
    rw [Category.assoc, IsOpenImmersion.lift_fac]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartNzdAlg
section
namespace UpperTheory.Gal.KunnethLefschetz.G.PX

section Chart

open CategoryTheory Limits MvPolynomial

end Chart

end UpperTheory.Gal.KunnethLefschetz.G.PX

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem chart_quotient_X_nonZeroDivisor {A : Type} [CommRing A] {D : ℕ} (j : Fin D) :
    IsSMulRegular (MvPolynomial (Fin D) (MvPolynomial (Fin D) A) ⧸
      Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A))
        (Set.range fun k => MvPolynomial.C (MvPolynomial.X k) -
          MvPolynomial.C (MvPolynomial.X j) * MvPolynomial.X k)))
      (MvPolynomial.X j : MvPolynomial (Fin D) A) := by
  classical
  set J : Ideal (MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) :=
    Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A))
      (Set.range fun k => MvPolynomial.C (MvPolynomial.X k) -
        MvPolynomial.C (MvPolynomial.X j) * MvPolynomial.X k)) with hJdef
  have hgen1 : (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) ∈ J :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hgen2 : ∀ k, (MvPolynomial.C (MvPolynomial.X k) - MvPolynomial.C (MvPolynomial.X j) *
      MvPolynomial.X k : MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) ∈ J :=
    fun k => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  let Z : Fin D → Polynomial (MvPolynomial (Fin D) A) :=
    fun k => if k = j then 1 else Polynomial.C (MvPolynomial.X k)
  let θ0 : MvPolynomial (Fin D) A →+* Polynomial (MvPolynomial (Fin D) A) :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun k => Polynomial.X * Z k)
  let Θ : MvPolynomial (Fin D) (MvPolynomial (Fin D) A) →+* Polynomial (MvPolynomial (Fin D) A) :=
    MvPolynomial.eval₂Hom θ0 Z
  let Λ : Polynomial (MvPolynomial (Fin D) A) →+* MvPolynomial (Fin D) (MvPolynomial (Fin D) A) :=
    Polynomial.eval₂RingHom
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp MvPolynomial.C) MvPolynomial.X)
      (MvPolynomial.C (MvPolynomial.X j))
  have hZj : Z j = 1 := by simp [Z]
  have hZk : ∀ k, k ≠ j → Z k = Polynomial.C (MvPolynomial.X k) := fun k hk => by simp [Z, hk]
  have hJ : J ≤ RingHom.ker Θ := by
    rw [hJdef, Ideal.span_le]
    rintro x (rfl | ⟨k, rfl⟩)
    · simp [Θ, hZj]
    · simp [Θ, θ0, hZj]
  have hθ : (Ideal.Quotient.mk J).comp (Λ.comp θ0) = (Ideal.Quotient.mk J).comp MvPolynomial.C := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [Λ, θ0]
    · intro k
      by_cases hk : k = j
      · subst hk
        simp [Λ, θ0, hZj]
      · have e := (Ideal.Quotient.eq (I := J)).mpr (hgen2 k)
        simp [Λ, θ0, hZk k hk, e]
  have hΛ : (Ideal.Quotient.mk J).comp (Λ.comp Θ) = Ideal.Quotient.mk J := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have := congrArg (fun F => F c) hθ
      simpa [Θ] using this
    · intro k
      by_cases hk : k = j
      · subst hk
        have e := (Ideal.Quotient.eq (I := J)).mpr hgen1
        simp [Θ, Λ, hZj, e]
      · simp [Θ, Λ, hZk k hk]
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro x hx
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : MvPolynomial.C (MvPolynomial.X j) * g ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (MvPolynomial (Fin D) A)
      (MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) (MvPolynomial (Fin D) (MvPolynomial (Fin D) A) ⧸ J)] at hx
    simpa [Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq] using hx
  have h2 : Θ (MvPolynomial.C (MvPolynomial.X j) * g) = 0 := hJ h1
  have h3 : Polynomial.X * Θ g = 0 := by
    simpa [Θ, θ0, hZj] using h2
  have h4 : Θ g = 0 := by
    refine Polynomial.ext fun n => ?_
    have := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q (n + 1)) h3
    simpa [Polynomial.coeff_X_mul] using this
  have h5 := congrArg (fun F => F g) hΛ
  simp only [RingHom.comp_apply, h4, map_zero] at h5
  exact h5.symm

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.chartNzdAlg :
    ∀ {A E R : Type} [CommRing A] [CommRing E] [CommRing R] {D : ℕ} (p : A →+* E) (ψ : E →+* R) (s : Fin D → E) (y : Fin D → R) (j : Fin D), (MvPolynomial.eval₂Hom p s).Etale → Function.Surjective (MvPolynomial.eval₂Hom ψ y) → RingHom.ker (MvPolynomial.eval₂Hom ψ y) = Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) E) (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * MvPolynomial.X k)) → ψ (s j) ∈ nonZeroDivisors R := by
  intro A E R _ _ _ D p ψ s y j hE hsurj hker
  classical
  letI : Algebra (MvPolynomial (Fin D) A) E := (MvPolynomial.eval₂Hom p s).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) A) E := hE
  have hX : ∀ k, algebraMap (MvPolynomial (Fin D) A) E (MvPolynomial.X k) = s k := fun k => by
    simp [RingHom.algebraMap_toAlgebra]
  set J : Ideal (MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) :=
    Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A))
      (Set.range fun k => MvPolynomial.C (MvPolynomial.X k) -
        MvPolynomial.C (MvPolynomial.X j) * MvPolynomial.X k)) with hJdef
  have hgen1 : (MvPolynomial.X j - 1 : MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) ∈ J :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hgen2 : ∀ k, (MvPolynomial.C (MvPolynomial.X k) - MvPolynomial.C (MvPolynomial.X j) *
      MvPolynomial.X k : MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) ∈ J :=
    fun k => Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
  have hreg : IsSMulRegular
      (TensorProduct (MvPolynomial (Fin D) A) E (MvPolynomial (Fin D) (MvPolynomial (Fin D) A) ⧸ J))
      (MvPolynomial.X j : MvPolynomial (Fin D) A) :=
    IsSMulRegular.lTensor E (chart_quotient_X_nonZeroDivisor j)
  let e2 := MvPolynomial.algebraTensorAlgEquiv (MvPolynomial (Fin D) A) (σ := Fin D) E
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := MvPolynomial (Fin D) A) E
    (MvPolynomial (Fin D) (MvPolynomial (Fin D) A)) E J
  let Φ : MvPolynomial (Fin D) E →ₐ[E]
      TensorProduct (MvPolynomial (Fin D) A) E (MvPolynomial (Fin D) (MvPolynomial (Fin D) A) ⧸ J) :=
    (e1.symm.toAlgHom).comp ((Ideal.Quotient.mkₐ E _).comp e2.symm.toAlgHom)
  have key : ∀ g, e2 (Algebra.TensorProduct.includeRight g) =
      MvPolynomial.map (algebraMap (MvPolynomial (Fin D) A) E) g := by
    intro g
    simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul]
  have hΦJ : ∀ g ∈ J, Φ (MvPolynomial.map (algebraMap (MvPolynomial (Fin D) A) E) g) = 0 := by
    intro g hg
    rw [← key g]
    simp only [Φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      AlgEquiv.symm_apply_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hg),
      map_zero]
  have hIΦ : RingHom.ker (MvPolynomial.eval₂Hom ψ y) ≤ RingHom.ker Φ := by
    rw [hker, Ideal.span_le]
    rintro x (rfl | ⟨k, rfl⟩)
    · have := hΦJ _ hgen1
      simpa using this
    · have := hΦJ _ (hgen2 k)
      simpa [hX] using this
  have hΦI : ∀ f, Φ f = 0 → f ∈ RingHom.ker (MvPolynomial.eval₂Hom ψ y) := by
    intro f hf
    have h1 : Ideal.Quotient.mk (J.map (Algebra.TensorProduct.includeRight
        (R := MvPolynomial (Fin D) A) (A := E))) (e2.symm f) = 0 := by
      have := congrArg e1 hf
      simpa [Φ] using this
    rw [Ideal.Quotient.eq_zero_iff_mem] at h1
    have h2 : J.map (Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin D) A) (A := E)) ≤
        (RingHom.ker (MvPolynomial.eval₂Hom ψ y)).comap e2 := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, Ideal.mem_comap, key, hker]
      have hJI : J ≤ (Ideal.span (insert (MvPolynomial.X j - 1 : MvPolynomial (Fin D) E)
          (Set.range fun k => MvPolynomial.C (s k) - MvPolynomial.C (s j) * MvPolynomial.X k))).comap
          (MvPolynomial.map (algebraMap (MvPolynomial (Fin D) A) E)) := by
        rw [hJdef, Ideal.span_le]
        rintro x (rfl | ⟨k, rfl⟩)
        · exact Ideal.subset_span (by simp)
        · exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨k, by simp [hX]⟩)
      exact hJI hg
    have := h2 h1
    simpa using this
  rw [mem_nonZeroDivisors_iff_right]
  intro r hr
  obtain ⟨f, rfl⟩ := hsurj r
  have h1 : f * MvPolynomial.C (s j) ∈ RingHom.ker (MvPolynomial.eval₂Hom ψ y) := by
    rw [RingHom.mem_ker, map_mul, MvPolynomial.eval₂Hom_C]
    exact hr
  have h2 : Φ (f * MvPolynomial.C (s j)) = 0 := hIΦ h1
  have h3 : (MvPolynomial.X j : MvPolynomial (Fin D) A) • Φ f =
      (MvPolynomial.X j : MvPolynomial (Fin D) A) • 0 := by
    rw [smul_zero, ← h2, map_mul, Algebra.smul_def, mul_comm]
    congr 1
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← hX j,
      ← IsScalarTower.algebraMap_apply]
  have h4 : Φ f = 0 := hreg h3
  have h5 := hΦI f h4
  simpa using h5
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.CoverComm
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.coverComm :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) {T : Scheme.{0}} (j : T ⟶ Y) (r : T ⟶ W) (hw : j ≫ π = r ≫ i), rhoP B j r hw ≫ cP B = eP B j ≫ r ∧ tauP B j ≫ D.f = eP B j ≫ j := by
  intro K _ W Z Y q i π D d B T j r hw
  constructor
  · refine Sigma.hom_ext _ _ fun p => ?_
    have h1 : wI B p.1 ≫ cP B = (oW B p.1).ι := by
      simp only [wI, cP, Sigma.ι_desc]
    have h2 : rhoC B j r hw p ≫ (oW B p.1).ι = (oT B j p).ι ≫ r := by
      simp only [rhoC, IsOpenImmersion.lift_fac]
    simp only [rhoP, eP, Sigma.ι_desc_assoc, Category.assoc, h1, h2]
  · refine Sigma.hom_ext _ _ fun p => ?_
    simp only [tauP, eP, Sigma.ι_desc_assoc, secOf_f]
end

