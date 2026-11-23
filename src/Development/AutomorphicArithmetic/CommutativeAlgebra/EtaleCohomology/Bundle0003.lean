module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitsOfSplitOn
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

private lemma splitOn_base {X' X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) (g : X' ⟶ X) {m : ℕ}
    (z : Fin m → (X ⟶ Z)) (H : SplitOn p x z) : SplitOn p (g ≫ x) fun i => g ≫ z i := by
  obtain ⟨h, hI⟩ := H
  have h' : ∀ i, (g ≫ z i) ≫ p = g ≫ x := fun i => by rw [Category.assoc, h i]
  refine ⟨h', ?_⟩
  let t : Fin m → (X ⟶ pullback p x) := fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])
  let t' : Fin m → (X' ⟶ pullback p (g ≫ x)) := fun i =>
    pullback.lift (g ≫ z i) (𝟙 X') (by rw [h' i, Category.id_comp])
  have ht1 : ∀ i, t i ≫ pullback.fst p x = z i := fun i => pullback.lift_fst _ _ _
  have ht2 : ∀ i, t i ≫ pullback.snd p x = 𝟙 X := fun i => pullback.lift_snd _ _ _
  have ht1' : ∀ i, t' i ≫ pullback.fst p (g ≫ x) = g ≫ z i := fun i => pullback.lift_fst _ _ _
  have ht2' : ∀ i, t' i ≫ pullback.snd p (g ≫ x) = 𝟙 X' := fun i => pullback.lift_snd _ _ _
  let f : pullback p (g ≫ x) ⟶ pullback p x :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by
      rw [pullback.condition, Category.assoc])
  have hf1 : f ≫ pullback.fst p x = pullback.fst p (g ≫ x) := pullback.lift_fst _ _ _
  have hf2 : f ≫ pullback.snd p x = pullback.snd p (g ≫ x) ≫ g := pullback.lift_snd _ _ _
  have hsq : IsPullback f (pullback.snd p (g ≫ x)) (pullback.snd p x) g := by
    have outer : IsPullback (pullback.fst p (g ≫ x)) (pullback.snd p (g ≫ x)) p (g ≫ x) :=
      IsPullback.of_hasPullback _ _
    have right : IsPullback (pullback.fst p x) (pullback.snd p x) p x := IsPullback.of_hasPullback _ _
    exact IsPullback.of_right (h₁₂ := pullback.fst p x) (v₁₃ := p) (h₂₂ := x) (by rwa [hf1]) hf2 right
  have hw : ∀ i, t' i ≫ f = g ≫ t i := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hf1, ht1, ht1']
    · rw [Category.assoc, Category.assoc, hf2, ht2, reassoc_of% ht2', Category.comp_id]
  have hleft : ∀ i, IsPullback (t' i) g f (t i) := by
    intro i
    have outer : IsPullback (𝟙 X') g g (𝟙 X) := IsPullback.of_horiz_isIso ⟨by simp⟩
    exact IsPullback.of_right (h₁₂ := pullback.snd p (g ≫ x)) (h₂₂ := pullback.snd p x) (v₁₃ := g)
      (by rwa [ht2, ht2']) (hw i) hsq.flip
  haveI : IsIso (Sigma.desc t) := hI
  let c : Cofan (fun _ : Fin m => X) := Cofan.mk (pullback p x) t
  have hc : IsColimit c := by
    let e : ∐ (fun _ : Fin m => X) ≅ pullback p x := asIso (Sigma.desc t)
    refine IsColimit.ofIsoColimit (coproductIsCoproduct (fun _ : Fin m => X)) (Cocone.ext e ?_)
    rintro ⟨j⟩
    simp [c, e]
  let c' : Cofan (fun _ : Fin m => X') := Cofan.mk (pullback p (g ≫ x)) t'
  let α : Discrete.functor (fun _ : Fin m => X') ⟶ Discrete.functor (fun _ : Fin m => X) :=
    Discrete.natTrans fun _ => g
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts hc
  obtain ⟨hc'⟩ := hu c' α f (by
      ext ⟨j⟩
      simpa [α, c, c'] using (hw j).symm) (by
      intro ⟨a⟩ ⟨b⟩ ⟨e⟩
      obtain rfl : a = b := e
      exact IsPullback.of_horiz_isIso ⟨by simp⟩) (by
      rintro ⟨j⟩
      exact hleft j)
  have e : Sigma.desc t' = (IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct _) hc').hom := by
    apply Sigma.hom_ext
    intro j
    rw [Sigma.ι_desc]
    exact ((coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩).symm
  show IsIso (Sigma.desc t')
  rw [e]
  infer_instance

private lemma splitOn_perm {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (x : X ⟶ Y) {m : ℕ}
    (z : Fin m → (X ⟶ Z)) (H : SplitOn p x z) (σ : Equiv.Perm (Fin m)) :
    SplitOn p x fun i => z (σ i) := by
  obtain ⟨h, hI⟩ := H
  refine ⟨fun i => h (σ i), ?_⟩
  have e : (Sigma.desc (fun i => pullback.lift (z (σ i)) (𝟙 X) (by rw [h (σ i), Category.id_comp])) :
      ∐ (fun _ : Fin m => X) ⟶ pullback p x) =
      (Sigma.reindex σ (fun _ : Fin m => X)).hom ≫
        Sigma.desc (fun i => pullback.lift (z i) (𝟙 X) (by rw [h i, Category.id_comp])) := by
    apply Sigma.hom_ext
    intro j
    have e1 : Sigma.ι (fun _ : Fin m => X) j ≫ (Sigma.reindex σ (fun _ : Fin m => X)).hom =
        Sigma.ι (fun _ : Fin m => X) (σ j) := Sigma.ι_reindex_hom σ (fun _ : Fin m => X) j
    rw [Sigma.ι_desc]
    refine Eq.symm ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) e1).trans ?_
    exact Sigma.ι_desc _ _
  rw [e]
  infer_instance

private lemma fromSpec_pb {Y Z : Scheme.{0}} (p : Z ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (hS : IsAffineOpen (p ⁻¹ᵁ U)) : IsPullback (Spec.map (p.app U)) hS.fromSpec hU.fromSpec p := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [Scheme.Hom.app_eq_appLE]
    exact (hU.SpecMap_appLE_fromSpec p hS le_rfl).symm
  · rw [hU.opensRange_fromSpec, hS.opensRange_fromSpec]

private lemma splits_of_splitOn {Y Z : Scheme.{0}} (p : Z ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (hS : IsAffineOpen (p ⁻¹ᵁ U)) (C : Type) [CommRing C] [Algebra Γ(Y, U) C] {m : ℕ} :
    letI : Algebra Γ(Y, U) Γ(Z, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
    ∀ ξ : Fin m → (Γ(Z, p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] C),
      SplitOn p (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) C)) ≫ hU.fromSpec)
        (fun i => Spec.map (CommRingCat.ofHom (ξ i).toRingHom) ≫ hS.fromSpec) → Splits ξ := by
  letI : Algebra Γ(Y, U) Γ(Z, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  intro ξ ⟨h, hI⟩
  have pbA := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(Y, U) C Γ(Z, p ⁻¹ᵁ U))
  have P := pbA.flip.paste_horiz (fromSpec_pb p hU hS).flip
  let Φ := Spec.map (CommRingCat.ofHom (splitMap ξ).toRingHom)
  let t : Fin m → (Spec (CommRingCat.of C) ⟶ pullback p (Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) C)) ≫ hU.fromSpec)) :=
    fun i => pullback.lift (Spec.map (CommRingCat.ofHom (ξ i).toRingHom) ≫ hS.fromSpec) (𝟙 _) (by rw [h i, Category.id_comp])
  have claim : sigmaSpec (fun _ : Fin m => CommRingCat.of C) ≫ Φ ≫ P.isoPullback.hom = Sigma.desc t := by
    apply Sigma.hom_ext
    intro j
    rw [ι_sigmaSpec_assoc, Sigma.ι_desc]
    let E : CommRingCat.of (C ⊗[Γ(Y, U)] Γ(Z, p ⁻¹ᵁ U)) ⟶ CommRingCat.of C :=
      CommRingCat.ofHom (splitMap ξ).toRingHom ≫ CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => C) j)
    have hE : Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin m => C) j)) ≫ Φ = Spec.map E :=
      (Spec.map_comp _ _).symm
    have hE1 : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := Γ(Y, U)) (A := C) (B := Γ(Z, p ⁻¹ᵁ U))) ≫ E = 𝟙 _ := by
      ext c
      simpa [E] using (splitMap_tmul ξ c 1 j).trans (by simp)
    have hE2 : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := Γ(Y, U)) (A := C) (B := Γ(Z, p ⁻¹ᵁ U))).toRingHom ≫ E =
        CommRingCat.ofHom (ξ j).toRingHom := by
      ext s
      simpa [E] using (splitMap_tmul ξ 1 s j).trans (by simp)
    rw [reassoc_of% hE]
    apply pullback.hom_ext
    · rw [Category.assoc, P.isoPullback_hom_fst, pullback.lift_fst, ← Spec.map_comp_assoc, hE2]
    · rw [Category.assoc, P.isoPullback_hom_snd, pullback.lift_snd, ← Spec.map_comp, hE1, Spec.map_id]
  haveI : IsIso (Sigma.desc t) := hI
  haveI : IsIso (sigmaSpec (fun _ : Fin m => CommRingCat.of C) ≫ Φ ≫ P.isoPullback.hom) := by
    rw [claim]; infer_instance
  haveI : IsIso (Φ ≫ P.isoPullback.hom) := IsIso.of_isIso_comp_left (sigmaSpec (fun _ : Fin m => CommRingCat.of C)) _
  haveI : IsIso Φ := IsIso.of_isIso_comp_right Φ P.isoPullback.hom
  exact isIso_SpecMap_iff.mp this

private lemma spec_fac {B : Type} [CommRing B] {X : Scheme.{0}} (w : Spec (CommRingCat.of B) ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hw : ⊤ ≤ w ⁻¹ᵁ V) :
    w = Spec.map (w.appLE V ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom) ≫ hV.fromSpec := by
  rw [Spec.map_comp, Category.assoc, hV.SpecMap_appLE_fromSpec w (isAffineOpen_top _) hw,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

private lemma app_comp_appLE {X Z Y : Scheme.{0}} (z : X ⟶ Z) (p : Z ⟶ Y) (y : X ⟶ Y) (e : z ≫ p = y) (U : Y.Opens)
    (V : X.Opens) (hy : V ≤ y ⁻¹ᵁ U) (hz : V ≤ z ⁻¹ᵁ (p ⁻¹ᵁ U)) :
    p.app U ≫ z.appLE (p ⁻¹ᵁ U) V hz = y.appLE U V hy := by
  subst e
  rw [Scheme.Hom.comp_appLE]

theorem splitRules : SplitRules := by
  refine ⟨fun p x g _ z H => ⟨splitOn_base p x g z H, fun σ => splitOn_perm p x z H σ⟩, ?_⟩
  intro l Y T U hU B _ y hy z hz hzy hsplit
  haveI := T.fin
  have hS : IsAffineOpen (T.p ⁻¹ᵁ U) := hU.preimage T.p
  letI := T.alg U
  letI : Algebra Γ(Y, U) B := ((y.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom).toAlgebra
  let ζ : Fin T.d → (Γ(T.Z, T.p ⁻¹ᵁ U) →ₐ[Γ(Y, U)] B) := fun i =>
    { ((z i).appLE (T.p ⁻¹ᵁ U) ⊤ (hz i) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom with
      commutes' := fun a => by
        have e := app_comp_appLE (z i) T.p y (hzy i) U ⊤ hy (hz i)
        have e' := congr($(e) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom)
        exact congr($(e').hom a) }
  refine ⟨ζ, ?_, fun i a => rfl⟩
  let C := Localization.Away (l : B)
  have e1 : awayPt l B ≫ y = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) C)) ≫ hU.fromSpec := by
    conv_lhs => rw [spec_fac y hU hy]
    rw [← Spec.map_comp_assoc]
    congr 2
  have e2 : ∀ i, awayPt l B ≫ z i = Spec.map (CommRingCat.ofHom
      ((IsScalarTower.toAlgHom Γ(Y, U) B C).comp (ζ i)).toRingHom) ≫ hS.fromSpec := by
    intro i
    conv_lhs => rw [spec_fac (z i) hS (hz i)]
    rw [← Spec.map_comp_assoc]
    rfl
  rw [e1, show (fun i => awayPt l B ≫ z i) = _ from funext e2] at hsplit
  exact splits_of_splitOn T.p hU hS C _ hsplit

end UpperTheory.Ru.crystallineComparison
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumSecEqZero
section
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

private theorem sum_sec_eq_zero (Pa : Parts C) (F : Coef C) (hF : Pa.Add F) {Q P : C ⥤ Type}
    {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) (h : Pa.LocZero a u)
    (c : ∀ A : C, P.obj A → F.obj A) (hc : c ∈ Sec P F) (A : C) (y : Q.obj A) :
    ∑ i, a i • c A ((u i).app A y) = 0 := by
  have hc' : ∀ {A B : C} (φ : A ⟶ B) (y : P.obj A), (F.map φ).hom (c A y) = c B (P.map φ y) := hc
  obtain ⟨S, hS, hs⟩ := h A y
  apply (hF A S hS).1
  funext s
  show (F.map (S.f s)).hom (∑ i, a i • c A ((u i).app A y)) = (F.map (S.f s)).hom 0
  have hnat : ∀ i, (F.map (S.f s)).hom (a i • c A ((u i).app A y)) =
      a i • c (S.B s) ((u i).app _ (Q.map (S.f s) y)) := by
    intro i
    rw [map_zsmul, hc' (S.f s) _, NatTrans.naturality_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum]
  simp only [hnat]
  rcases hs s with h0 | h0
  · have hL := congrArg
      (Finsupp.liftAddHom fun p : P.obj (S.B s) => zmultiplesHom (F.obj (S.B s)) (c (S.B s) p)) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum] using hL
  · apply (hF _ _ h0).1
    funext e
    exact e.elim

private theorem locSum_zero (Pa : Parts C) (T : Theory C) (F : Coef C) (hF : Pa.Add F)
    {Q P : C ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) (h : Pa.LocZero a u)
    (x : T.H P F 0) : ∑ i, a i • T.pull (u i) F 0 x = 0 := by
  apply (T.zero Q F).injective
  rw [map_zero]
  apply Subtype.ext
  funext A y
  let E : T.H Q F 0 →+ F.obj A := AddMonoidHom.mk' (fun z => (T.zero Q F z).1 A y) (by
    intro z w
    simp [map_add (f := _)])
  show E (∑ i, a i • T.pull (u i) F 0 x) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hE : ∀ i, E (a i • T.pull (u i) F 0 x) = a i • (T.zero P F x).1 A ((u i).app A y) := by
    intro i
    rw [map_zsmul]
    congr 1
    exact T.zero_pull (u i) F x A y
  simp only [hE]
  exact sum_sec_eq_zero Pa F hF a u h _ (T.zero P F x).2 A y

private theorem locSum_shift (T : Theory C) {Q P : C ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ)
    (u : I → (Q ⟶ P)) (S : ShortComplex (Coef C)) (hS : S.ShortExact) (j : ℕ)
    (hsub : Subsingleton (T.H P S.X₂ (j + 1)))
    (ih : ∀ w : T.H P S.X₃ j, ∑ i, a i • T.pull (u i) S.X₃ j w = 0)
    (x : T.H P S.X₁ (j + 1)) : ∑ i, a i • T.pull (u i) S.X₁ (j + 1) x = 0 := by
  obtain ⟨w, rfl⟩ := (T.ex₁ P S hS j x).1 (hsub.elim _ _)
  have hδ : ∑ i, a i • T.δ Q S hS j (T.pull (u i) S.X₃ j w) =
      T.δ Q S hS j (∑ i, a i • T.pull (u i) S.X₃ j w) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_zsmul]
  simp only [T.pull_δ]
  rw [hδ, ih w, map_zero]

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.locSum :
    UpperTheory.Ru.crystallineComparison.LocSum := by
  intro C _ Pa T F hF Q P I _ a u h j x
  induction j generalizing F with
  | zero => exact locSum_zero Pa T F hF a u h x
  | succ j ih =>
    obtain ⟨K, ι, hm, hK, hKa⟩ := emb C Pa F hF
    let S : ShortComplex (Coef C) := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel ι, mono_f := hm, epi_g := inferInstanceAs (Epi (cokernel.π ι)) }
    have h3 : Pa.Add S.X₃ := quotAdd C Pa S hS hF hKa
    exact locSum_shift T a u S hS j (T.inj P K hK j) (fun w => ih S.X₃ h3 w) x
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumTransport
section
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

private lemma sec_nat {P : C ⥤ Type} {K : Coef C} (c : Sec P K) {A B : C} (φ : A ⟶ B)
    (y : P.obj A) : (K.map φ).hom (c.1 A y) = c.1 B (P.map φ y) :=
  c.2 φ y

private lemma sum_transport {Q : C ⥤ Type} {K : Coef C} (c : Sec Q K) {I : Type} [Fintype I]
    (g : I → (Q ⟶ Q)) {A B : C} (φ : A ⟶ B) (w : Q.obj A) :
    (K.map φ).hom (∑ i, c.1 A ((g i).app A w)) =
      ((Finset.univ.val.map fun i => (g i).app B (Q.map φ w)).map (c.1 B)).sum := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Multiset.map_map]
  change _ = ∑ i, c.1 B ((g i).app B (Q.map φ w))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sec_nat c φ, ← NatTrans.naturality_apply (g i) φ]

private lemma avg_indep (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) {A : C}
    {w w' : Q.obj A} (hw : p.app A w = p.app A w') :
    ∑ i, c.1 A ((g i).app A w) = ∑ i, c.1 A ((g i).app A w') := by
  obtain ⟨S, hS, hm⟩ := h.2.2 A w w' hw
  apply (hK A S hS).1
  funext s
  change (K.map (S.f s)).hom _ = (K.map (S.f s)).hom _
  rw [sum_transport, sum_transport, hm s]

private def lift (Pa : Parts C) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (A : C) (y : P.obj A) : Q.obj A :=
  Classical.choose ((show ∀ A, Function.Surjective (p.app A) from h.2.1) A y)

private lemma lift_spec (Pa : Parts C) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I]
    {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (A : C) (y : P.obj A) :
    p.app A (lift Pa h A y) = y :=
  Classical.choose_spec ((show ∀ A, Function.Surjective (p.app A) from h.2.1) A y)

private def avg (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) : Sec P K :=
  ⟨fun A y => ∑ i, c.1 A ((g i).app A (lift Pa h A y)), by
    intro A B φ y
    have hw : p.app B (Q.map φ (lift Pa h A y)) = p.app B (lift Pa h B (P.map φ y)) := by
      rw [lift_spec, NatTrans.naturality_apply p φ, lift_spec]
    change (K.map φ).hom (∑ i, c.1 A ((g i).app A (lift Pa h A y))) =
      ∑ i, c.1 B ((g i).app B (lift Pa h B (P.map φ y)))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← avg_indep Pa hK h c hw, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sec_nat c φ, ← NatTrans.naturality_apply (g i) φ]⟩

private lemma avg_apply (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (c : Sec Q K) (A : C)
    (y : P.obj A) :
    (avg Pa hK h c).1 A y = ∑ i, c.1 A ((g i).app A (lift Pa h A y)) := rfl

private lemma avg_pull (Pa : Parts C) {K : Coef C} (hK : Pa.Add K) {Q P : C ⥤ Type} {p : Q ⟶ P}
    {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g) (s : Sec P K) (c : Sec Q K)
    (hc : ∀ (A : C) (q : Q.obj A), c.1 A q = s.1 A (p.app A q)) :
    avg Pa hK h c = Fintype.card I • s := by
  apply Subtype.ext
  funext A y
  have hg : ∀ (i : I) (w : Q.obj A), p.app A ((g i).app A w) = p.app A w := fun i w => by
    have hgi : g i ≫ p = p := (show ∀ i, g i ≫ p = p from h.1) i
    have : (g i ≫ p).app A w = p.app A w := by rw [hgi]
    exact this
  rw [avg_apply]
  simp only [hc, hg, lift_spec]
  simp

private lemma avg_map (Pa : Parts C) {K L : Coef C} (hK : Pa.Add K) (hL : Pa.Add L)
    {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I] {g : I → (Q ⟶ Q)} (h : Pa.LocTrans p g)
    (α : K ⟶ L) (c : Sec Q K) (c' : Sec Q L)
    (hc : ∀ (A : C) (q : Q.obj A), c'.1 A q = (α.app A).hom (c.1 A q)) (A : C) (y : P.obj A) :
    (avg Pa hL h c').1 A y = (α.app A).hom ((avg Pa hK h c).1 A y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [avg_apply, avg_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => hc _ _

private lemma zero_case (Pa : Parts C) (T : Theory C) {K L : Coef C} (hK : Pa.Add K)
    (hL : Pa.Add L) {Q P : C ⥤ Type} {p : Q ⟶ P} {I : Type} [Fintype I] {g : I → (Q ⟶ Q)}
    (h : Pa.LocTrans p g) (π : K ⟶ L) (x' : T.H P L 0) (k : T.H Q K 0)
    (hk : T.map Q π 0 k = T.pull p L 0 x') :
    Fintype.card I • x' ∈ Set.range (T.map P π 0) := by
  refine ⟨(T.zero P K).symm (avg Pa hK h (T.zero Q K k)), ?_⟩
  apply (T.zero P L).injective
  apply Subtype.ext
  funext A y
  have e1 : avg Pa hL h (T.zero Q L (T.pull p L 0 x')) = Fintype.card I • T.zero P L x' :=
    avg_pull Pa hL h _ _ fun A q => T.zero_pull p L x' A q
  have e2 := avg_map Pa hK hL h π (T.zero Q K k) (T.zero Q L (T.map Q π 0 k))
    (fun A q => T.zero_map Q π k A q) A y
  rw [T.zero_map, map_nsmul, ← e1, ← hk, e2, AddEquiv.apply_symm_apply]

private lemma step (Pa : Parts C) (T : Theory C) {Q P : C ⥤ Type} (p : Q ⟶ P) (n : ℕ)
    (S : ShortComplex (Coef C)) (hS : S.ShortExact) (hK : Injective S.X₂) (j : ℕ)
    (hr : ∀ (x' : T.H P S.X₃ j) (k : T.H Q S.X₂ j), T.map Q S.g j k = T.pull p S.X₃ j x' →
      n • x' ∈ Set.range (T.map P S.g j))
    (x : T.H P S.X₁ (j + 1)) (hx : T.pull p S.X₁ (j + 1) x = 0) : n • x = 0 := by
  have h0 : T.map P S.f (j + 1) x = 0 := (T.inj P S.X₂ hK j).elim _ _
  obtain ⟨x', rfl⟩ := (T.ex₁ P S hS j x).1 h0
  have hpull : T.δ Q S hS j (T.pull p S.X₃ j x') = 0 := by
    rw [← T.pull_δ]
    exact hx
  obtain ⟨k, hk⟩ := (T.ex₃ Q S hS j _).1 hpull
  obtain ⟨k', hk'⟩ := hr x' k hk
  rw [← map_nsmul, ← hk']
  exact (T.ex₃ P S hS j _).2 ⟨k', rfl⟩

end UpperTheory.Ru.crystallineComparison

open CategoryTheory CategoryTheory.Limits UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.locAvg :
    UpperTheory.Ru.crystallineComparison.LocAvg := by
  intro C _ Pa T F hF Q P p I _ g h j
  induction j generalizing F with
  | zero =>
    intro x hx
    have hx0 : x = 0 := by
      apply (T.zero P F).injective
      rw [map_zero]
      apply Subtype.ext
      funext A y
      obtain ⟨w, rfl⟩ := h.2.1 A y
      rw [← T.zero_pull p F x A w, hx, map_zero]
      rfl
    rw [hx0, smul_zero]
  | succ j ih =>
    intro x hx
    obtain ⟨K, ι, hm, hi, hK⟩ := emb C Pa F hF
    have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
      { exact := ShortComplex.exact_cokernel ι, mono_f := hm, epi_g := inferInstance }
    have hL : Pa.Add (cokernel ι) := quotAdd C Pa _ hS hF hK
    refine step Pa T p _ _ hS hi j ?_ x hx
    intro x' k hk
    cases j with
    | zero =>
      exact zero_case Pa T hK hL h _ x' k hk
    | succ j =>
      have hk0 : k = 0 := (T.inj Q K hi j).elim _ _
      rw [hk0, map_zero] at hk
      exact ⟨0, by rw [map_zero, ih _ hL x' hk.symm]⟩
end
end

