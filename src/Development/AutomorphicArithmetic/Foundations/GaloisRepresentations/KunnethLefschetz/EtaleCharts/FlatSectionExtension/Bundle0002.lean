module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.ChartRange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.EtaleSplit
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.etaleSplit :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι), (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)).Etale := by
  intro K _ W Z Y q i π D d B α
  let E : MvPolynomial (Fin (B.c α).n ⊕ Fin d) K ≃ₐ[K] MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) :=
    (MvPolynomial.renameEquiv K (Equiv.sumComm (Fin (B.c α).n) (Fin d))).trans
      (MvPolynomial.sumAlgEquiv K (Fin d) (Fin (B.c α).n))
  have h : (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t :
      MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)).comp
        (E : MvPolynomial (Fin (B.c α).n ⊕ Fin d) K →+* MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K)) =
      MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (Sum.elim (B.c α).x (B.c α).t) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [E, MvPolynomial.sumAlgEquiv_C_inl]
    · rintro (m | m) <;> simp [E, MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]
  have h' : (MvPolynomial.eval₂Hom (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (B.c α).x) (B.c α).t :
      MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* Γ(Z, B.V α)) =
      (MvPolynomial.eval₂Hom (Pb.strV q (B.V α)) (Sum.elim (B.c α).x (B.c α).t)).comp
        (E.symm : MvPolynomial (Fin d) (MvPolynomial (Fin (B.c α).n) K) →+* MvPolynomial (Fin (B.c α).n ⊕ Fin d) K) := by
    rw [← h]
    ext x
    all_goals simp
  rw [h']
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective E.symm.bijective) (B.c α).etale
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.GlueSection
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem presheaf_map_map_eq_map {V : Scheme.{0}} {A B C : V.Opens} (i : B ⟶ A) (j : C ⟶ B)
    (k : C ⟶ A) (t : Γ(V, A)) :
    (V.presheaf.map j.op).hom ((V.presheaf.map i.op).hom t) = (V.presheaf.map k.op).hom t := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.glueSection :
    ∀ {V : Scheme.{0}} (U : V → V.Opens) (_ : ∀ x, x ∈ U x) (s : ∀ x, Γ((U x : Scheme.{0}), ⊤)), (∀ (x y : V) {S : Scheme.{0}} (f : S ⟶ (U x : Scheme.{0})) (f' : S ⟶ (U y : Scheme.{0})), f ≫ (U x).ι = f' ≫ (U y).ι → f.appTop.hom (s x) = f'.appTop.hom (s y)) → ∃ s₀ : Γ(V, ⊤), ∀ x, (U x).ι.appTop.hom s₀ = s x := by
  intro V U hU s h
  have hcov : (⊤ : V.Opens) ≤ iSup U := fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  have compat : TopCat.Presheaf.IsCompatible V.sheaf.1 U (fun x => (U x).topIso.hom (s x)) := by
    intro x y
    have hc := h x y (V.homOfLE (inf_le_left : U x ⊓ U y ≤ U x)) (V.homOfLE inf_le_right)
      (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])
    rw [Scheme.homOfLE_appTop, Scheme.homOfLE_appTop] at hc
    have hc' := congrArg (U x ⊓ U y).topIso.hom.hom hc
    simp only [Scheme.Opens.topIso_hom] at hc'
    have ky : U x ⊓ U y ⟶ (U y).ι ''ᵁ ⊤ := homOfLE (inf_le_right.trans (U y).ι_image_top.ge)
    exact (presheaf_map_map_eq_map (V := V) (A := (U x).ι ''ᵁ ⊤) _ _
        (homOfLE (inf_le_left.trans (U x).ι_image_top.ge)) (s x)).trans
      ((presheaf_map_map_eq_map (V := V) (A := (U x).ι ''ᵁ ⊤) _ _ _ (s x)).symm.trans
        (hc'.trans (presheaf_map_map_eq_map (V := V) (A := (U y).ι ''ᵁ ⊤) _ _ ky (s y)))
        |>.trans (presheaf_map_map_eq_map (V := V) (A := (U y).ι ''ᵁ ⊤) _ _ ky (s y)).symm)
  obtain ⟨s₀, hs₀, -⟩ := V.sheaf.existsUnique_gluing' U ⊤ (fun x => homOfLE le_top) hcov _ compat
  refine ⟨s₀, fun x => ?_⟩
  have e := congrArg (U x).topIso.inv.hom (hs₀ x)
  rw [Iso.hom_inv_id_apply] at e
  rw [← e, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv]
  exact (presheaf_map_map_eq_map (V := V) _ _ _ s₀).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.HomExt
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.homExt :
    ∀ {V X : Scheme.{0}} (a b : V ⟶ X), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ U.ι ≫ a = U.ι ≫ b) → a = b := by
  intro V X a b h
  choose W hxW hW using h
  have hcov : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr ?_)
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  exact (V.openCoverOfIsOpenCover W hcov).hom_ext _ _ hW
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.KerRes
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.kerRes :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) {N : Z.Opens} (_ : IsAffineOpen N) (h : N ≤ B.V α), RingHom.ker (i.app N).hom = Ideal.span (Set.range (tN B α h)) := by
  intro K _ W Z Y q i π D d B α N hN h
  haveI := B.closed
  have hUV : (⟨N, hN⟩ : Z.affineOpens) ≤ ⟨B.V α, (B.c α).affine⟩ := h
  have key := i.ker.map_ideal hUV
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at key
  change Ideal.map _ (RingHom.ker (i.app (B.V α)).hom) = RingHom.ker (i.app N).hom at key
  rw [(B.c α).ker, Ideal.map_span, ← Set.range_comp] at key
  rw [← key]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatComp
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

namespace UpperTheory.Gal.KunnethLefschetz.G.PX

private lemma restr_sec {V Z : Scheme.{0}} (f : V ⟶ Z) {U U₂ : V.Opens} {N N₂ : Z.Opens}
    (hN : N₂ ≤ N) (hUU : U₂ ≤ U) (hU : ⊤ ≤ (U.ι ≫ f) ⁻¹ᵁ N) (hU₂ : ⊤ ≤ (U₂.ι ≫ f) ⁻¹ᵁ N₂)
    (s : Γ(V, ⊤)) (g : Γ(Z, N))
    (h : U.ι.appTop.hom s = ((U.ι ≫ f).appLE N ⊤ hU).hom g) :
    U₂.ι.appTop.hom s =
      ((U₂.ι ≫ f).appLE N₂ ⊤ hU₂).hom ((Z.presheaf.map (homOfLE hN).op).hom g) := by
  have e1 : U₂.ι.appTop = U.ι.appTop ≫ (V.homOfLE hUU).appTop := by
    rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_ι]
  have hT : (⊤ : (U₂ : Scheme.{0}).Opens) ≤ (V.homOfLE hUU) ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have e0 : (V.homOfLE hUU).appLE ⊤ ⊤ hT = (V.homOfLE hUU).appTop :=
    (Scheme.Hom.app_eq_appLE (V.homOfLE hUU)).symm
  have e2 : Z.presheaf.map (homOfLE hN).op ≫ (U₂.ι ≫ f).appLE N₂ ⊤ hU₂ =
      (U.ι ≫ f).appLE N ⊤ hU ≫ (V.homOfLE hUU).appTop := by
    rw [← e0, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [← Category.assoc, Scheme.homOfLE_ι]
  have e3 := congrArg (fun φ => φ.hom g) e2
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e3
  rw [e1, CommRingCat.hom_comp, RingHom.comp_apply, h, ← e3]

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)}
  {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ}

private lemma tN_res (B : Blow q i π D d) (α : B.ι) {N N₂ : Z.Opens} (h : N ≤ B.V α)
    (hN : N₂ ≤ N) (m : Fin d) :
    tN B α (hN.trans h) m = (Z.presheaf.map (homOfLE hN).op).hom (tN B α h m) := by
  simp only [tN]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma isTr_res (B : Blow q i π D d) (α β : B.ι) {N N₂ : Z.Opens} (h₁ : N ≤ B.V α)
    (h₂ : N ≤ B.V β) (hN : N₂ ≤ N) (G : Matrix (Fin d) (Fin d) Γ(Z, N))
    (hG : IsTr B α β h₁ h₂ G) :
    IsTr B α β (hN.trans h₁) (hN.trans h₂) (G.map (Z.presheaf.map (homOfLE hN).op).hom) := by
  intro m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tN_res B β h₂ hN, hG m, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, tN_res B α h₁ hN]
  rfl

private lemma isTr_comp (B : Blow q i π D d) (α β γ : B.ι) {N : Z.Opens} (h₁ : N ≤ B.V α)
    (h₂ : N ≤ B.V β) (h₃ : N ≤ B.V γ) (G G' : Matrix (Fin d) (Fin d) Γ(Z, N))
    (hG : IsTr B α β h₁ h₂ G) (hG' : IsTr B β γ h₂ h₃ G') :
    IsTr B α γ h₁ h₃ (G' * G) := by
  intro m
  rw [hG' m]
  simp only [hG _, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatComp :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β γ : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M M' : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B β γ p M' → LocMat B α γ p (M' * M) := by
  intro K _ W Z Y q i π D d B α β γ V p M M' h h' x
  obtain ⟨U, N, hx, hNa, h₁, h₂, hU, G, hG, hM⟩ := h x
  obtain ⟨U', N', hx', hNa', h₁', h₂', hU', G', hG', hM'⟩ := h' x
  have hxN : (p ≫ i) x ∈ N := hU (Set.mem_univ (⟨x, hx⟩ : (U : Scheme.{0})))
  have hxN' : (p ≫ i) x ∈ N' := hU' (Set.mem_univ (⟨x, hx'⟩ : (U' : Scheme.{0})))
  obtain ⟨N₂, hA, hxN₂, hle⟩ := exists_isAffineOpen_mem_and_subset (U := N ⊓ N') ⟨hxN, hxN'⟩
  have hl₁ : N₂ ≤ N := fun y hy => (hle hy).1
  have hl₂ : N₂ ≤ N' := fun y hy => (hle hy).2
  let U₂ : V.Opens := U ⊓ U' ⊓ (p ≫ i) ⁻¹ᵁ N₂
  have hUl : U₂ ≤ U := fun y hy => hy.1.1
  have hUl' : U₂ ≤ U' := fun y hy => hy.1.2
  have hU₂ : ⊤ ≤ (U₂.ι ≫ p ≫ i) ⁻¹ᵁ N₂ := by
    intro y _
    exact y.2.2
  refine ⟨U₂, N₂, ⟨⟨hx, hx'⟩, hxN₂⟩, hA, hl₁.trans h₁, hl₂.trans h₂', hU₂,
    G'.map (Z.presheaf.map (homOfLE hl₂).op).hom * G.map (Z.presheaf.map (homOfLE hl₁).op).hom,
    ?_, ?_⟩
  · exact isTr_comp B α β γ _ (hl₁.trans h₂) _ _ _ (isTr_res B α β h₁ h₂ hl₁ G hG)
      (isTr_res B β γ h₁' h₂' hl₂ G' hG')
  · rw [Matrix.map_mul, Matrix.map_mul]
    congr 1
    · ext a b
      exact restr_sec (p ≫ i) hl₂ hUl' hU' hU₂ _ _ (congrFun (congrFun hM' a) b)
    · ext a b
      exact restr_sec (p ≫ i) hl₁ hUl hU hU₂ _ _ (congrFun (congrFun hM a) b)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatLocal
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatLocal :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V : Scheme.{0}} (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ LocMat B α β (U.ι ≫ p) (M.map U.ι.appTop.hom)) → LocMat B α β p M := by
  intro K _ W Z Y q i π D d B α β V p M h x
  obtain ⟨U, hxU, hL⟩ := h x
  obtain ⟨U', N, hx', hN, h₁, h₂, hU', G, hT, hM⟩ := hL ⟨x, hxU⟩
  have he : (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι = U'.ι ≫ U.ι := U.ι.isoImage_hom_ι U'
  have hU'' : ⊤ ≤ ((U.ι ''ᵁ U').ι ≫ p ≫ i) ⁻¹ᵁ N := by
    rintro ⟨y, z, hz, rfl⟩ _
    have := @hU' (⟨z, hz⟩ : U'.toScheme) trivial
    exact this
  refine ⟨U.ι ''ᵁ U', N, ⟨⟨x, hxU⟩, hx', rfl⟩, hN, h₁, h₂, hU'', G, hT, ?_⟩
  ext a b
  have hinj : ∀ {A C : Scheme.{0}} (e : A ≅ C), Function.Injective e.hom.appTop.hom := by
    intro A C e
    have : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).1
  apply hinj (U.ι.isoImage U')
  have hab := congrFun (congrFun hM a) b
  simp only [Matrix.map_apply] at hab ⊢
  have e₁ : (U.ι.isoImage U').hom.appTop.hom (((U.ι ''ᵁ U').ι).appTop.hom (M a b)) = U'.ι.appTop.hom (U.ι.appTop.hom (M a b)) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, he]
  have e₂ : (U.ι.isoImage U').hom.appTop.hom ((((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'').hom (G a b)) = ((U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU').hom (G a b) := by
    have : ((U.ι ''ᵁ U').ι ≫ p ≫ i).appLE N ⊤ hU'' ≫ (U.ι.isoImage U').hom.appTop = (U'.ι ≫ (U.ι ≫ p) ≫ i).appLE N ⊤ hU' := by
      have hc : U'.ι ≫ (U.ι ≫ p) ≫ i = (U.ι.isoImage U').hom ≫ (U.ι ''ᵁ U').ι ≫ p ≫ i := by
        rw [reassoc_of% he]; simp
      simp only [hc]
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    exact congrArg (fun f => f.hom (G a b)) this
  rw [e₁, e₂, hab]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatNat
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

private theorem appLE_top_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  change _ = f.app ⊤
  rw [Scheme.Hom.app_eq_appLE]
  rfl

private theorem appLE_comp_appTop' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (N : Z.Opens)
    (h : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ N) (h' : (⊤ : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ N) :
    (f ≫ g).appLE N ⊤ h' = g.appLE N ⊤ h ≫ f.appTop := by
  have e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := fun _ _ => trivial
  rw [← appLE_top_eq f e]
  exact (Scheme.Hom.appLE_comp_appLE f g N ⊤ ⊤ h e).symm

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatNat :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α β : B.ι) {V' V : Scheme.{0}} (s : V' ⟶ V) (p : V ⟶ W) (M : Matrix (Fin d) (Fin d) Γ(V, ⊤)), LocMat B α β p M → LocMat B α β (s ≫ p) (M.map s.appTop.hom) := by
  intro K _ W Z Y q i π D d B α β V' V s p M h x'
  obtain ⟨U, N, hx, hN, h₁, h₂, hU, G, hG, hM⟩ := h (s x')
  have e : (s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i = (s ∣_ U) ≫ U.ι ≫ p ≫ i := by
    rw [← Category.assoc (s ∣_ U), morphismRestrict_ι]
    simp only [Category.assoc]
  have hU' : ⊤ ≤ ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i) ⁻¹ᵁ N := by
    rw [e]
    intro y _
    exact hU (Set.mem_univ ((s ∣_ U) y))
  refine ⟨s ⁻¹ᵁ U, N, hx, hN, h₁, h₂, hU', G, hG, ?_⟩
  have gen : ∀ (f g : ((s ⁻¹ᵁ U : V'.Opens) : Scheme.{0}) ⟶ Z) (_ : f = g) (hf : ⊤ ≤ f ⁻¹ᵁ N) (hg : ⊤ ≤ g ⁻¹ᵁ N),
      f.appLE N ⊤ hf = g.appLE N ⊤ hg := by
    rintro f g rfl _ _
    rfl
  have h3 : ((s ⁻¹ᵁ U).ι ≫ (s ≫ p) ≫ i).appLE N ⊤ hU' = (U.ι ≫ p ≫ i).appLE N ⊤ hU ≫ (s ∣_ U).appTop :=
    (gen _ _ e hU' (e ▸ hU')).trans (appLE_comp_appTop' _ _ N hU _)
  have h4 : ∀ a : Γ(V, ⊤), (s ∣_ U).appTop.hom (U.ι.appTop.hom a) = (s ⁻¹ᵁ U).ι.appTop.hom (s.appTop.hom a) := by
    intro a
    have e2 : ((s ∣_ U) ≫ U.ι).appTop = ((s ⁻¹ᵁ U).ι ≫ s).appTop := by rw [morphismRestrict_ι]
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at e2
    exact congrArg (fun φ => φ.hom a) e2
  ext m l
  have h1 := congrFun (congrFun hM m) l
  simp only [Matrix.map_apply] at h1 ⊢
  rw [h3, ← h4, h1]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.LocMatOne
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.locMatOne :
    ∀ {K : Type} [CommRing K] {W Z Y : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of K)} {i : W ⟶ Z} {π : Y ⟶ Z} {D : E.LineData Y} {d : ℕ} (B : Blow q i π D d) (α : B.ι) {V : Scheme.{0}} (p : V ⟶ W), (∀ x : V, (p ≫ i) x ∈ B.V α) → LocMat B α α p 1 := by
  intro K _ W Z Y q i π D d B α V p h x
  have hU : ⊤ ≤ (((⊤ : V.Opens).ι ≫ p ≫ i) ⁻¹ᵁ B.V α) := by
    intro y _
    exact h y.1
  refine ⟨⊤, B.V α, trivial, (B.c α).affine, le_rfl, le_rfl, hU, 1, ?_, ?_⟩
  · intro m
    simp [Matrix.one_apply]
  · rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _)]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SectionExt
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sectionExt :
    ∀ {V : Scheme.{0}} (s s' : Γ(V, ⊤)), (∀ x : V, ∃ U : V.Opens, x ∈ U ∧ U.ι.appTop.hom s = U.ι.appTop.hom s') → s = s' := by
  intro V s s' h
  choose U hxU hU using h
  refine TopCat.Sheaf.eq_of_locally_eq' V.sheaf (fun x => (U x).ι ''ᵁ ⊤) ⊤
    (fun x => homOfLE le_top) ?_ s s' ?_
  · intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, ⟨⟨y, hxU y⟩, trivial, rfl⟩⟩
  · intro x
    exact hU x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaDisj
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaDisj :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {S : Scheme.{0}} {p p' : σ} (f : S ⟶ X p) (f' : S ⟶ X p') (_ : S), f ≫ Sigma.ι X p = f' ≫ Sigma.ι X p' → p = p' := by
  intro σ X S p p' f f' s h
  have e : Sigma.ι X p (f s) = Sigma.ι X p' (f' s) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact congrArg Sigma.fst ((sigmaι_eq_iff X p p' _ _).mp e)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaLocal
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaLocal :
    ∀ {σ : Type} (X : σ → Scheme.{0}) {V : Scheme.{0}} (a : V ⟶ ∐ X) (x : V), ∃ (U : V.Opens) (p : σ) (a₁ : (U : Scheme.{0}) ⟶ X p), x ∈ U ∧ U.ι ≫ a = a₁ ≫ Sigma.ι X p := by
  intro σ X V a x
  obtain ⟨⟨p, z⟩, hz⟩ := (sigmaMk X).surjective (a x)
  rw [sigmaMk_mk] at hz
  have hr : Set.range ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) ⊆ Set.range (Sigma.ι X p) := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  refine ⟨a ⁻¹ᵁ (Sigma.ι X p).opensRange, p,
    IsOpenImmersion.lift (Sigma.ι X p) ((a ⁻¹ᵁ (Sigma.ι X p).opensRange).ι ≫ a) hr, ?_, ?_⟩
  · show a x ∈ (Sigma.ι X p).opensRange
    exact ⟨z, hz⟩
  · exact (IsOpenImmersion.lift_fac _ _ _).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FlatSectionExtension.SigmaSection
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto UpperTheory.Gal.KunnethLefschetz.G.PX

theorem UpperTheory.Gal.KunnethLefschetz.G.PX.sigmaSection :
    ∀ {σ : Type} (X : σ → Scheme.{0}) (f : ∀ p, Γ(X p, ⊤)), ∃ s : Γ(∐ X, ⊤), (∀ p, (Sigma.ι X p).appTop.hom s = f p) ∧ ∀ s' : Γ(∐ X, ⊤), (∀ p, (Sigma.ι X p).appTop.hom s' = f p) → s' = s := by
  intro σ X f
  let L := isLimitOfPreserves (Scheme.Γ ⋙ forget CommRingCat) (coproductIsCoproduct X).op
  let e : Γ(∐ X, ⊤) ≃ ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
    Types.isLimitEquivSections L
  have hproj : ∀ (s : Γ(∐ X, ⊤)) (p : σ), (e s).val (Opposite.op ⟨p⟩) = (Sigma.ι X p).appTop.hom s :=
    fun s p => Types.isLimitEquivSections_apply L (Opposite.op ⟨p⟩) s
  let sec : ((Discrete.functor X).op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
    ⟨fun j => f j.unop.as, by
      rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨h⟩⟩
      cases h
      rfl⟩
  refine ⟨e.symm sec, fun p => ?_, fun s' hs' => e.injective ?_⟩
  · rw [← hproj, Equiv.apply_symm_apply]
  · apply Subtype.ext
    funext j
    obtain ⟨⟨q⟩⟩ := j
    rw [hproj, hs', Equiv.apply_symm_apply]
end

