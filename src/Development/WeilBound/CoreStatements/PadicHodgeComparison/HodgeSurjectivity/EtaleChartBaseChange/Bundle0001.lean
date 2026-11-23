module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.CLBAlg
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto.CLB

theorem chart_etale_of_univ {R A S B : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    (f : R →+* A) (g : R →+* S) (φ : A →+* B) (h : S →+* B) (hf : f.Etale) (hsq : φ.comp f = h.comp g)
    (hU : ∀ (T : Type) [CommRing T] (α : A →+* T) (β : S →+* T), α.comp f = β.comp g →
      ∃ γ : B →+* T, γ.comp φ = α ∧ γ.comp h = β)
    (hE : ∀ (T : Type) [CommRing T] (γ γ' : B →+* T), γ.comp φ = γ'.comp φ → γ.comp h = γ'.comp h → γ = γ') :
    h.Etale := by
  letI : Algebra R A := f.toAlgebra
  letI : Algebra R S := g.toAlgebra
  letI : Algebra R B := (φ.comp f).toAlgebra
  haveI : Algebra.Etale R A := RingHom.etale_algebraMap.1 hf
  haveI : Algebra.Etale S (TensorProduct R S A) := Algebra.Etale.baseChange R A S
  let hA : S →ₐ[R] B := { h with commutes' := fun r => (RingHom.congr_fun hsq r).symm }
  let φA : A →ₐ[R] B := { φ with commutes' := fun r => rfl }
  let e : TensorProduct R S A →ₐ[R] B := Algebra.TensorProduct.lift hA φA (fun _ _ => Commute.all _ _)
  have he1 : e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom = h := by
    ext s; simp [e, hA]
  have he2 : e.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom = φ := by
    ext a; simp [e, φA]
  obtain ⟨γ, hγ1, hγ2⟩ := hU (TensorProduct R S A) (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := A)).toRingHom
    Algebra.TensorProduct.includeLeftRingHom (by
      ext r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.includeLeftRingHom_apply]
      have h1 : f r = r • (1 : A) := Algebra.algebraMap_eq_smul_one r
      have h2 : g r = r • (1 : S) := Algebra.algebraMap_eq_smul_one r
      rw [h1, h2, TensorProduct.smul_tmul])
  have hinv1 : ∀ b, e (γ b) = b := by
    intro b
    have := hE B (e.toRingHom.comp γ) (RingHom.id B)
      (by rw [RingHom.comp_assoc, hγ1, he2]; rfl) (by rw [RingHom.comp_assoc, hγ2, he1]; rfl)
    exact RingHom.congr_fun this b
  have hinv2 : ∀ z, γ (e z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
      rw [Algebra.TensorProduct.lift_tmul, map_mul]
      have e1 := RingHom.congr_fun hγ2 s
      have e2 := RingHom.congr_fun hγ1 a
      simp only [RingHom.comp_apply] at e1 e2
      change γ (h s) * γ (φ a) = _
      rw [e1, e2]
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hb : Function.Bijective e := Function.bijective_iff_has_inverse.2 ⟨γ, hinv2, hinv1⟩
  rw [← he1]
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.etale_algebraMap.2 inferInstance)
    (RingHom.Etale.of_bijective (f := e.toRingHom) hb)

def chartMapKXT {K : Type} [CommRing K] {n d : ℕ} (k : Fin d) :
    MvPolynomial (Fin n ⊕ Fin d) K →+* MvPolynomial (Fin n ⊕ Fin d) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Sum.elim (fun i => MvPolynomial.X (Sum.inl i))
    (fun j => if j = k then MvPolynomial.X (Sum.inr k) else MvPolynomial.X (Sum.inr k) * MvPolynomial.X (Sum.inr j)))

theorem chart_etale {K A B : Type} [CommRing K] [CommRing A] [CommRing B] {n d : ℕ} (s : K →+* A) (x : Fin n → A)
    (t : Fin d → A) (het : (MvPolynomial.eval₂Hom s (Sum.elim x t) : MvPolynomial (Fin n ⊕ Fin d) K →+* A).Etale)
    (φ : A →+* B) (u : Fin d → B) (k : Fin d) (hs : Function.Surjective (MvPolynomial.eval₂Hom φ u))
    (hr : RingHom.ker (MvPolynomial.eval₂Hom φ u) = Ideal.span (insert (MvPolynomial.X k - 1)
      (Set.range fun j => MvPolynomial.C (t j) - MvPolynomial.C (t k) * MvPolynomial.X j))) :
    (MvPolynomial.eval₂Hom (φ.comp s) (Sum.elim (φ ∘ x) (fun j => if j = k then φ (t k) else u j)) :
      MvPolynomial (Fin n ⊕ Fin d) K →+* B).Etale := by
  have hk1 : u k = 1 := by
    have hm : MvPolynomial.X k - 1 ∈ RingHom.ker (MvPolynomial.eval₂Hom φ u) := by
      rw [hr]; exact Ideal.subset_span (Set.mem_insert _ _)
    have := (RingHom.mem_ker).1 hm
    simpa [sub_eq_zero] using this
  have htj : ∀ j, φ (t j) = φ (t k) * u j := by
    intro j
    have hm : MvPolynomial.C (t j) - MvPolynomial.C (t k) * MvPolynomial.X j ∈ RingHom.ker (MvPolynomial.eval₂Hom φ u) := by
      rw [hr]; exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)
    have := (RingHom.mem_ker).1 hm
    simpa [sub_eq_zero] using this
  refine chart_etale_of_univ (MvPolynomial.eval₂Hom s (Sum.elim x t)) (chartMapKXT (K := K) (n := n) k) φ _ het ?_ ?_ ?_
  · refine MvPolynomial.ringHom_ext (fun r => by simp [chartMapKXT]) (fun v => ?_)
    rcases v with i | j
    · simp [chartMapKXT]
    · by_cases hj : j = k
      · subst hj; simp [chartMapKXT]
      · simp [chartMapKXT, hj, htj j]
  · intro T _ α β hαβ
    have hX : ∀ v, α (MvPolynomial.eval₂Hom s (Sum.elim x t) (MvPolynomial.X v)) =
        β (chartMapKXT (K := K) (n := n) k (MvPolynomial.X v)) := fun v => RingHom.congr_fun hαβ _
    have hC : ∀ c, α (s c) = β (MvPolynomial.C c) := by
      intro c
      have := RingHom.congr_fun hαβ (MvPolynomial.C c)
      simpa [chartMapKXT] using this
    have hXk : α (t k) = β (MvPolynomial.X (Sum.inr k)) := by
      have := hX (Sum.inr k); simpa [chartMapKXT] using this
    have hXj : ∀ j, j ≠ k → α (t j) = β (MvPolynomial.X (Sum.inr k)) * β (MvPolynomial.X (Sum.inr j)) := by
      intro j hj; have := hX (Sum.inr j); simpa [chartMapKXT, hj] using this
    have hXi : ∀ i, α (x i) = β (MvPolynomial.X (Sum.inl i)) := by
      intro i; have := hX (Sum.inl i); simpa [chartMapKXT] using this
    let γ0 : MvPolynomial (Fin d) A →+* T :=
      MvPolynomial.eval₂Hom α (fun j => if j = k then 1 else β (MvPolynomial.X (Sum.inr j)))
    have hle : RingHom.ker (MvPolynomial.eval₂Hom φ u) ≤ RingHom.ker γ0 := by
      rw [hr, Ideal.span_le]
      rintro p (rfl | ⟨j, rfl⟩)
      · simp [γ0]
      · by_cases hj : j = k
        · subst hj; simp [γ0]
        · simp [γ0, hj, hXj j hj, hXk]
    let γ := (RingHom.liftOfSurjective (MvPolynomial.eval₂Hom φ u) hs) ⟨γ0, hle⟩
    have hγ : ∀ p, γ (MvPolynomial.eval₂Hom φ u p) = γ0 p := fun p =>
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ p
    refine ⟨γ, ?_, ?_⟩
    · ext a
      have := hγ (MvPolynomial.C a)
      simpa [γ0] using this
    · refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
      · have := hγ (MvPolynomial.C (s c))
        simp only [MvPolynomial.eval₂Hom_C, γ0] at this
        simp [this, hC]
      · rcases v with i | j
        · have := hγ (MvPolynomial.C (x i))
          simp only [MvPolynomial.eval₂Hom_C, γ0] at this
          simp [this, hXi]
        · by_cases hj : j = k
          · subst hj
            have := hγ (MvPolynomial.C (t j))
            simp only [MvPolynomial.eval₂Hom_C, γ0] at this
            simp [this, hXk]
          · have := hγ (MvPolynomial.X j)
            simpa [γ0, hj] using this
  · intro T _ γ γ' h1 h2
    have hc : γ.comp (MvPolynomial.eval₂Hom φ u) = γ'.comp (MvPolynomial.eval₂Hom φ u) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
      · simpa using RingHom.congr_fun h1 a
      · by_cases hj : j = k
        · subst hj; simp [hk1]
        · have := RingHom.congr_fun h2 (MvPolynomial.X (Sum.inr j))
          simpa [hj] using this
    ext b
    obtain ⟨p, rfl⟩ := hs b
    exact RingHom.congr_fun hc p

end CrystallineSemistableComparison.Onto.CLB

end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.CLBKer
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace CrystallineSemistableComparison.Onto.CLB

theorem app_surj {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective (f.app U).hom :=
  f.app_surjective U hU

theorem fromSpec_appLE_top {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D)
    (e : (⊤ : (Spec Γ(Y, D)).Opens) ≤ hD.fromSpec ⁻¹ᵁ D) :
    hD.fromSpec.appLE D ⊤ e = (Scheme.ΓSpecIso Γ(Y, D)).inv := by
  unfold Scheme.Hom.appLE
  rw [hD.fromSpec_app_self]
  simp [← Functor.map_comp]

theorem SpecMap_appLE_top {R S : CommRingCat.{0}} (f : R ⟶ S) (e : (⊤ : (Spec S).Opens) ≤ Spec.map f ⁻¹ᵁ ⊤) :
    (Spec.map f).appLE ⊤ ⊤ e = (Scheme.ΓSpecIso R).hom ≫ f ≫ (Scheme.ΓSpecIso S).inv := by
  rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

theorem appLE_fromSpec_quot {Y : Scheme.{0}} {D : Y.Opens} (hD : IsAffineOpen D) (J : Ideal Γ(Y, D))
    (e : (⊤ : (Spec (CommRingCat.of (Γ(Y, D) ⧸ J))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec) ⁻¹ᵁ D) (x : Γ(Y, D)) :
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec).appLE D ⊤ e).hom x =
      (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).inv.hom (Ideal.Quotient.mk J x) := by
  rw [← Scheme.Hom.appLE_comp_appLE _ _ D ⊤ ⊤ (by simp [hD.fromSpec_preimage_self]) (by simp)]
  rw [fromSpec_appLE_top, SpecMap_appLE_top]
  change (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).inv.hom (Ideal.Quotient.mk J
    ((Scheme.ΓSpecIso Γ(Y, D)).hom.hom ((Scheme.ΓSpecIso Γ(Y, D)).inv.hom x))) = _
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

theorem ker_snd {W Z Y : Scheme.{0}} (i : W ⟶ Z) [IsClosedImmersion i] (π : Y ⟶ Z) (V : Z.Opens) (hV : IsAffineOpen V)
    (D : Y.Opens) (hD : IsAffineOpen D) (hDV : D ≤ π ⁻¹ᵁ V) :
    RingHom.ker ((pullback.snd i π).app D).hom = Ideal.map (π.appLE V D hDV).hom (RingHom.ker (i.app V).hom) := by
  apply le_antisymm
  · set I := RingHom.ker (i.app V).hom
    set J := Ideal.map (π.appLE V D hDV).hom I
    have hI' : IsAffineOpen (i ⁻¹ᵁ V) := hV.preimage i
    have hsurj := i.app_surjective V hV
    let e := RingHom.quotientKerEquivOfSurjective hsurj
    have hIJ : I ≤ J.comap (π.appLE V D hDV).hom := Ideal.le_comap_map
    let ψ : Γ(W, i ⁻¹ᵁ V) →+* Γ(Y, D) ⧸ J := (Ideal.quotientMap J (π.appLE V D hDV).hom hIJ).comp e.symm.toRingHom
    let a : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ Y := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hD.fromSpec
    let w : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ W := Spec.map (CommRingCat.ofHom ψ) ≫ hI'.fromSpec
    have hring : i.appLE V (i ⁻¹ᵁ V) le_rfl ≫ CommRingCat.ofHom ψ =
        π.appLE V D hDV ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      ext x
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      rw [← Scheme.Hom.app_eq_appLE]
      have : e.symm ((i.app V).hom x) = Ideal.Quotient.mk I x := by
        rw [RingEquiv.symm_apply_eq]; rfl
      change Ideal.quotientMap J (π.appLE V D hDV).hom hIJ (e.symm ((i.app V).hom x)) = _
      rw [this, Ideal.quotientMap_mk]
    have hw : w ≫ i = a ≫ π := by
      simp only [w, a, Category.assoc]
      rw [← IsAffineOpen.SpecMap_appLE_fromSpec i hV hI' le_rfl,
        ← IsAffineOpen.SpecMap_appLE_fromSpec π hV hD hDV, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]
    let c := pullback.lift w a hw
    intro x hx
    rw [RingHom.mem_ker] at hx
    have he : (⊤ : (Spec (CommRingCat.of (Γ(Y, D) ⧸ J))).Opens) ≤ a ⁻¹ᵁ D := by
      simp [a, hD.fromSpec_preimage_self]
    have h0 : (a.appLE D ⊤ he).hom x = 0 := by
      have hca : c ≫ pullback.snd i π = a := pullback.lift_snd _ _ _
      have key : ∀ (b : Spec (CommRingCat.of (Γ(Y, D) ⧸ J)) ⟶ Y) (hb : c ≫ pullback.snd i π = b) (e' : ⊤ ≤ b ⁻¹ᵁ D),
          (b.appLE D ⊤ e').hom x = 0 := by
        rintro b rfl e'
        rw [← Scheme.Hom.appLE_comp_appLE _ _ D ((pullback.snd i π) ⁻¹ᵁ D) ⊤ le_rfl (by simpa using e'),
          ← Scheme.Hom.app_eq_appLE]
        simp [hx]
      exact key a hca he
    rw [appLE_fromSpec_quot hD J he x] at h0
    have h1 : Ideal.Quotient.mk J x = 0 := by
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, D) ⧸ J))).hom.hom h0
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, map_zero] at h2
      exact h2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h1
  · rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [RingHom.mem_ker] at hg
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h1 : ∀ (f : pullback i π ⟶ Z) (hf : pullback.fst i π ≫ i = f) (e : (pullback.snd i π) ⁻¹ᵁ D ≤ f ⁻¹ᵁ V),
        (f.appLE V _ e).hom g = 0 := by
      rintro f rfl e
      rw [Scheme.Hom.comp_appLE]
      simp [hg]
    rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact h1 _ pullback.condition _

end CrystallineSemistableComparison.Onto.CLB

end
end

