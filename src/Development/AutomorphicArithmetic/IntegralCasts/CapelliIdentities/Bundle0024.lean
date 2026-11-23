module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FormallySmoothSectionStalk
section
private lemma UpperTheory.isLocalHom_of_square_zero {A B : Type*} [CommRing A] [CommRing B] (π : A →+* B)
    (hs : Function.Surjective π) (hk : ∀ x, π x = 0 → x * x = 0) : IsLocalHom π := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨c, hc⟩ := ha.exists_right_inv
  obtain ⟨b, rfl⟩ := hs c
  have h0 : π (a * b - 1) = 0 := by rw [map_sub, map_mul, hc, map_one, sub_self]
  have hn : IsNilpotent (a * b - 1) := ⟨2, by rw [pow_two]; exact hk _ h0⟩
  have hu : IsUnit (a * b) := by simpa using hn.isUnit_add_one
  exact isUnit_of_mul_isUnit_left hu

theorem UpperTheory.formally_smooth_section_stalk :
    open AlgebraicGeometry CategoryTheory in
        ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (s : X ⟶ Y), s ≫ f = 𝟙 X → ∀ p : X,
          ∃ (B : CommRingCat.{0}) (α : X.presheaf.stalk p ⟶ B) (σ : B ⟶ X.presheaf.stalk p) (ι : Spec B ⟶ Y),
            α.hom.FormallySmooth ∧ α.hom.EssFiniteType ∧ Mono ι ∧
              ι ≫ f = Spec.map α ≫ X.fromSpecStalk p ∧ Spec.map σ ≫ ι = X.fromSpecStalk p ≫ s ∧
              ∀ (R R' : CommRingCat.{0}) [IsLocalRing R] (π : R' ⟶ R) (φ : X.presheaf.stalk p ⟶ R) (v : Spec R' ⟶ Y),
                Function.Surjective π.hom → (∀ x, π.hom x = 0 → x * x = 0) →
                  Spec.map π ≫ v = Spec.map φ ≫ X.fromSpecStalk p ≫ s → ∃ g : B ⟶ R', v = Spec.map g ≫ ι := by
  open AlgebraicGeometry CategoryTheory in
  intro X Y f _ s hs p
  have hp : f (s p) = p := by
    rw [← Scheme.Hom.comp_apply, hs]; rfl
  have hi : Inseparable p (f (s p)) := Inseparable.of_eq hp.symm
  have hfs : (f.stalkMap (s p)).hom.FormallySmooth := by
    rw [← Scheme.Hom.mem_smoothLocus, f.smoothLocus_eq_top]; trivial
  have hft : (f.stalkMap (s p)).hom.EssFiniteType := LocallyOfFiniteType.stalkMap f (s p)
  refine ⟨Y.presheaf.stalk (s p), (X.presheaf.stalkCongr hi).hom ≫ f.stalkMap (s p),
    s.stalkMap p, Y.fromSpecStalk (s p), ?_, ?_, inferInstance, ?_, ?_, ?_⟩
  · exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso _ _).mpr hfs
  · exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso _ _).mpr hft
  · have h : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk p =
        X.fromSpecStalk (f (s p)) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.specializes'
    rw [Spec.map_comp, Category.assoc, h, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · exact Scheme.SpecMap_stalkMap_fromSpecStalk s
  · intro R R' _ π φ v hπ hk hv
    haveI : IsLocalHom π.hom := UpperTheory.isLocalHom_of_square_zero π.hom hπ hk
    haveI : IsLocalRing R' := π.hom.domain_isLocalRing
    have hsp : v (IsLocalRing.closedPoint R') ⤳ s p := by
      have h1 : v (IsLocalRing.closedPoint R') =
          s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R))) := by
        have h3 : v (Spec.map π (IsLocalRing.closedPoint R)) =
            s (X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R))) :=
          congrArg (fun k : Spec R ⟶ Y => k (IsLocalRing.closedPoint R)) hv
        exact (congrArg v (Spec_closedPoint (f := π)).symm).trans h3
      have h2 : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ⤳ p := by
        have : X.fromSpecStalk p (Spec.map φ (IsLocalRing.closedPoint R)) ∈
            Set.range (X.fromSpecStalk p) := ⟨_, rfl⟩
        rwa [Scheme.range_fromSpecStalk] at this
      rw [h1]
      exact h2.map s.continuous
    refine ⟨Y.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo v, ?_⟩
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FormallySmoothSurjectiveDerivation
section
open TensorProduct in
private theorem UpperTheory.universal_derivation_surjective {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [Algebra B A] [IsScalarTower A B A]
    [Algebra.FormallySmooth A B] [Algebra.EssFiniteType A B] :
    ∃ (n : ℕ) (d : Derivation A B (Fin n → A)), Function.Surjective d ∧
      ∀ (R : Type) [AddCommGroup R] [Module A R] [Module B R] [IsScalarTower B A R]
        (δ : Derivation A B R), ∃ c : Fin n → R, ∀ b, δ b = ∑ i, d b i • c i := by
  haveI : Module.Free A (A ⊗[B] Ω[B⁄A]) := Module.free_of_flat_of_isLocalRing
  let e := Module.finBasis A (A ⊗[B] Ω[B⁄A])
  let D0 : Derivation A B (A ⊗[B] Ω[B⁄A]) :=
    (TensorProduct.mk B A Ω[B⁄A] 1).compDer (KaehlerDifferential.D A B)
  have hD0 : ∀ b, D0 b = 1 ⊗ₜ KaehlerDifferential.D A B b := fun b => rfl
  have hsurj : Function.Surjective D0 := by
    have h1 : ∀ (w : Ω[B⁄A]) (a : A), a ⊗ₜ[B] w ∈ LinearMap.range D0.toLinearMap := by
      intro w
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D A B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        intro a
        have : a ⊗ₜ[B] KaehlerDifferential.D A B b = a • D0 b := by
          rw [hD0, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this]
        exact Submodule.smul_mem _ _ ⟨b, rfl⟩
      | zero => intro a; simp
      | add x y _ _ hx hy =>
        intro a
        rw [TensorProduct.tmul_add]
        exact add_mem (hx a) (hy a)
      | smul b x _ hx =>
        intro a
        rw [← TensorProduct.smul_tmul]
        exact hx _
    intro x
    change x ∈ LinearMap.range D0.toLinearMap
    induction x with
    | tmul a w => exact h1 w a
    | add x y hx hy => exact add_mem hx hy
  refine ⟨_, (e.equivFun.toLinearMap.restrictScalars B).compDer D0,
    e.equivFun.surjective.comp hsurj, ?_⟩
  intro R _ _ _ _ δ
  haveI : IsScalarTower A B R := ⟨fun a b r => by
    rw [← algebraMap_smul A (a • b) r, ← algebraMap_smul A b r, ← mul_smul]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one, smul_assoc, ← Algebra.algebraMap_eq_smul_one, smul_eq_mul]⟩
  let f : A ⊗[B] Ω[B⁄A] →ₗ[A] R := δ.liftKaehlerDifferential.liftBaseChange A
  refine ⟨fun i => f (e i), fun b => ?_⟩
  have h2 : δ b = f (D0 b) := by
    simp [f, hD0]
  rw [h2]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← e.sum_equivFun (D0 b), map_sum]
  simp only [map_smul]
  rfl

theorem UpperTheory.formally_smooth_surjective_derivation :
    ∀ {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] (α : A →+* B) (σ : B →+* A),
        σ.comp α = RingHom.id A → α.FormallySmooth → α.EssFiniteType →
          ∃ (n : ℕ) (d : B → Fin n → A), Function.Surjective d ∧
            ∀ (R : Type) [CommRing R] (φ : A →+* R),
              (∀ c : Fin n → R, ∃ g : B →+* DualNumber R,
                (∀ a, g (α a) = TrivSqZeroExt.inl (φ a)) ∧ (∀ b, (g b).fst = φ (σ b)) ∧
                  ∀ b, (g b).snd = ∑ i, φ (d b i) * c i) ∧
              ∀ g : B →+* DualNumber R, (∀ a, g (α a) = TrivSqZeroExt.inl (φ a)) → (∀ b, (g b).fst = φ (σ b)) →
                ∃ c : Fin n → R, ∀ b, (g b).snd = ∑ i, φ (d b i) * c i := by
  intro A B _ _ _ α σ hσ hfs hft
  have hσ' : ∀ a, σ (α a) = a := fun a => RingHom.congr_fun hσ a
  letI : Algebra A B := α.toAlgebra
  letI : Algebra B A := σ.toAlgebra
  haveI : IsScalarTower A B A := IsScalarTower.of_algebraMap_eq fun a => (hσ' a).symm
  haveI : Algebra.FormallySmooth A B := hfs
  haveI : Algebra.EssFiniteType A B := hft
  obtain ⟨n, d, hd, H⟩ := UpperTheory.universal_derivation_surjective (A := A) (B := B)
  have hmul : ∀ x y i, d (x * y) i = σ x * d y i + σ y * d x i := fun x y i => by
    rw [d.leibniz]; rfl
  have hα : ∀ a, d (α a) = 0 := fun a => d.map_algebraMap a
  refine ⟨n, d, hd, fun R _ φ => ⟨fun c => ?_, fun g hg1 hg2 => ?_⟩⟩
  · refine ⟨{ toFun := fun b => TrivSqZeroExt.inl (φ (σ b)) +
                TrivSqZeroExt.inr (∑ i, φ (d b i) * c i)
              map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
    · ext <;> simp
    · intro x y
      ext
      · simp
      · simp [hmul, -Derivation.leibniz, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm, mul_add, add_comm]
    · ext <;> simp
    · intro x y
      ext <;> simp [add_mul, Finset.sum_add_distrib]
    · intro a
      simp [hα, hσ']
    · intro b
      simp
    · intro b
      simp
  · letI : Algebra A R := φ.toAlgebra
    letI : Algebra B R := (φ.comp σ).toAlgebra
    haveI : IsScalarTower B A R := IsScalarTower.of_algebraMap_eq fun b => rfl
    let δ : Derivation A B R := Derivation.mk'
      { toFun := fun b => (g b).snd
        map_add' := fun x y => by simp
        map_smul' := fun a b => by
          change (g (α a * b)).snd = φ a * (g b).snd
          simp [hg1] }
      (fun x y => by
        change (g (x * y)).snd = φ (σ x) * (g y).snd + φ (σ y) * (g x).snd
        simp [hg2, mul_comm])
    exact H R δ
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FreeModuleQuotient
section
theorem UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot
    {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    (s : S →+* R) (I K : Ideal S) (hIK : I ≤ K) (c : ℕ)
    (e : M ≃+ (Fin c → S ⧸ I)) (he : ∀ (z : S) (x : M), e (s z • x) = z • e x) :
    ∃ e' : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K),
      ∀ (a : S) (x : M ⧸ (Ideal.map s K • ⊤ : Submodule R M)), e' (s a • x) = a • e' x := by
  classical
  let φ : M →+ (Fin c → S ⧸ K) :=
    { toFun := fun x i => Ideal.Quotient.factor hIK (e x i)
      map_zero' := by funext i; simp
      map_add' := by intro x y; funext i; simp }
  have hφ : ∀ x i, φ x i = Ideal.Quotient.factor hIK (e x i) := fun _ _ => rfl
  have hsm : ∀ (a : S) (x : M), φ (s a • x) = a • φ x := by
    intro a x
    funext i
    rw [Pi.smul_apply, hφ, hφ, he, Pi.smul_apply]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e x i)
    rw [← hy]
    rfl
  have hsurj : Function.Surjective φ := by
    intro y
    choose t ht using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨e.symm (fun i => Ideal.Quotient.mk I (t i)), ?_⟩
    funext i
    rw [hφ, e.apply_symm_apply, Ideal.Quotient.factor_mk, ht]
  have h1 : ∀ r ∈ Ideal.map s K, ∀ x : M, φ (r • x) = 0 := by
    intro r hr
    refine Submodule.span_induction (p := fun r _ => ∀ x : M, φ (r • x) = 0) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨k, hk, rfl⟩ x
      rw [hsm]
      funext i
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ x i)
      rw [Pi.smul_apply, ← hy]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (K.mul_mem_right y hk)
    · intro x; simp
    · intro a b _ _ ha hb x
      rw [add_smul, map_add (f := _), ha, hb, add_zero]
    · intro a b _ hb x
      rw [smul_eq_mul, mul_comm, mul_smul, hb]
  have hker : ∀ x : M, x ∈ (Ideal.map s K • ⊤ : Submodule R M) ↔ φ x = 0 := by
    intro x
    constructor
    · intro hx
      refine Submodule.smul_induction_on (p := fun x => φ x = 0) hx ?_ ?_
      · intro r hr n _; exact h1 r hr n
      · intro a b ha hb; rw [map_add (f := _), ha, hb, add_zero]
    · intro hx
      choose t ht using fun i => Ideal.Quotient.mk_surjective (e x i)
      have htK : ∀ i, t i ∈ K := by
        intro i
        have := congrFun hx i
        rw [hφ, ← ht, Ideal.Quotient.factor_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.1 this
      have hxe : x = ∑ i, s (t i) • e.symm (Pi.single i 1) := by
        apply e.injective
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [he, e.apply_symm_apply]
        rw [← Finset.univ_sum_single (e x)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Pi.single_smul, ← ht, ← Algebra.algebraMap_eq_smul_one]
        rfl
      rw [hxe]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (Ideal.mem_map_of_mem s (htK i)) Submodule.mem_top
  let ψ : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) →+ (Fin c → S ⧸ K) :=
    QuotientAddGroup.lift (Ideal.map s K • ⊤ : Submodule R M).toAddSubgroup φ
      (fun x hx => (hker x).1 hx)
  have hψ : ∀ x : M, ψ (Submodule.Quotient.mk x) = φ x := fun _ => rfl
  have hbij : Function.Bijective ψ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hψ] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((hker y).2 hx)
    · intro y
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨Submodule.Quotient.mk x, hψ x⟩
  refine ⟨AddEquiv.ofBijective ψ hbij, fun a x => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul]
  exact hsm a y
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FreeRatios
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G.{u_1, u_2} :
    (F : Type u_1) → (Ω : Type u_2) → [inst : Field F] → [inst_1 : Field Ω] → [Algebra F Ω] → Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] ↦ Gal(Ω/F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec.{u_1, u_2} :
    {F : Type u_1} →
      {Ω : Type u_2} →
        [inst : Field F] →
          [inst_1 : Field Ω] → [inst_2 : Algebra F Ω] → ValuationSubring Ω → Subgroup (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω) :=
    fun {F : Type u_1} {Ω : Type u_2} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) ↦
      ValuationSubring.decompositionSubgroup F A

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 : Algebra F Ω] → (l : ℕ) → [inst_3 : Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* ℤ_[l]ˣ :=
    fun (F : Type u_1) (Ω : Type u_2) [Field F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact (Nat.Prime l)] ↦
      (cyclotomicCharacter Ω l).comp (MulSemiringAction.toRingAut (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω) Ω)

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeRatios :
    {κ ι : Type} → [inst : Field κ] → (ι → κˣ) → Prop :=
    fun {κ ι : Type} [Field κ] (α : ι → κˣ) ↦ ∀ (i j : ι), i ≠ j → ∀ (m : ℕ), (0 : ℕ) < m → α i ^ m ≠ α j ^ m

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat :
    {H k : Type} → [inst : Group H] → [inst_1 : CommRing k] → {n : ℕ} → (H →* GL (Fin n) k) → H →* Matrix (Fin n) (Fin n) k :=
    fun {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) ↦
      (Units.coeHom (Matrix (Fin n) (Fin n) k)).comp r

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt :
    (l : ℕ) →
      [inst : Fact (Nat.Prime l)] →
        {F Ω : Type} →
          [inst_1 : Field F] →
            [inst_2 : Field Ω] →
              [inst_3 : Algebra F Ω] → {n : ℕ} → (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* GL (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)) → Prop :=
    fun (l : ℕ) [Fact (Nat.Prime l)] {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
        (r : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω →* GL (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)) ↦
      ∀ (A : ValuationSubring Ω),
        (A.valuation : Ω → A.ValueGroup) (↑l : Ω) < (1 : A.ValueGroup) →
          ∃ g ∈ UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec A,
            (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ F Ω l : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω → ℤ_[l]ˣ) g = (1 : ℤ_[l]ˣ) ∧
              ∃ (α : Fin n → (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)ˣ),
                UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeRatios α ∧
                  ((UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat r : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G F Ω → Matrix (Fin n) (Fin n) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))
                        g).charpoly =
                    ∏ i : Fin n,
                      (Polynomial.X -
                        (Polynomial.C : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l → Polynomial (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))
                          (↑(α i) : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l))

noncomputable def UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb :
    (k E Ω : Type) →
      [inst : Field k] →
        [inst_1 : Field E] →
          [inst_2 : Field Ω] →
            [inst_3 : Algebra k Ω] →
              [inst_4 : Algebra E Ω] →
                [inst_5 : Algebra k E] → [IsScalarTower k E Ω] → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G E Ω →* UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G k Ω :=
    fun (k E Ω : Type) [Field k] [Field E] [Field Ω] [Algebra k Ω] [Algebra E Ω] [Algebra k E] [IsScalarTower k E Ω] ↦
      AlgEquiv.restrictScalarsHom k

private theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.charpoly_pow_two {k : Type} [Field k] (M : Matrix (Fin 2) (Fin 2) k) (a b : k)
    (h : M.charpoly = (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b)) (m : ℕ) :
    (M ^ m).charpoly = (Polynomial.X - Polynomial.C (a ^ m)) * (Polynomial.X - Polynomial.C (b ^ m)) := by
  have ht : M.trace = a + b := by
    have h0 := congrArg (fun p => Polynomial.eval 0 p) h
    have h1 := congrArg (fun p => Polynomial.eval 1 p) h
    rw [Matrix.charpoly_fin_two] at h0 h1
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at h0 h1
    linear_combination h0 - h1
  have hd : M.det = a * b := by
    have h1 := congrArg (fun p => Polynomial.eval 0 p) h
    rw [Matrix.charpoly_fin_two] at h1
    simpa using h1
  have hsq : M ^ 2 = (a + b) • M - (a * b) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    rw [← ht, ← hd, Matrix.trace_fin_two, Matrix.det_fin_two, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have htr : ∀ n : ℕ, (M ^ n).trace = a ^ n + b ^ n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [one_add_one_eq_two]
    | one => simpa using ht
    | more n h0 h1 =>
      rw [pow_add M n 2, hsq, mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_one, ← pow_succ,
        Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, h0, h1, smul_eq_mul, smul_eq_mul]
      ring
  rw [Matrix.charpoly_fin_two, htr, Matrix.det_pow, hd, mul_pow, Polynomial.C_add, Polynomial.C_mul]
  ring

private theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.exists_pow_fix {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (L : Type)
    [Field L] [NumberField L] [Algebra L Ω] (g : Gal(Ω/ℚ)) :
    ∃ m : ℕ, 0 < m ∧ ∃ g' : Gal(Ω/L), AlgEquiv.restrictScalarsHom ℚ g' = g ^ m := by
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ L Ω).fieldRange
  haveI : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ L Ω)).toLinearEquiv.finiteDimensional
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hi : K.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi g
  rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
  refine ⟨m, hm, AlgEquiv.ofRingEquiv (f := (g ^ m).toRingEquiv) (fun x => hmem _ ⟨x, rfl⟩), ?_⟩
  ext x
  rfl

theorem UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.freeRes :
    ∀ {Ω : Type} [inst : Field Ω] [inst_1 : CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [inst_3 : Fact (Nat.Prime l)] (L : Type)
      [inst_4 : Field L] [inst_5 : NumberField L] [inst_6 : Algebra L Ω] [IsAlgClosure L Ω]
      (W : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.G ℚ Ω →* GL (Fin (2 : ℕ)) (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Qbar l)),
      UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt l W → UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.FreeAt l (W.comp (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb ℚ L Ω)) := by
  intro Ω _ _ _ l _ L _ _ _ _ W hW A hA
  obtain ⟨g, hgD, hgc, α, hα, hch⟩ := hW A hA
  obtain ⟨m, hm, g', hg'⟩ := UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.exists_pow_fix L g
  refine ⟨g', ?_, ?_, fun i => α i ^ m, ?_, ?_⟩
  · have h1 : g ^ m ∈ UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.Dec A := Subgroup.pow_mem _ hgD m
    rw [← hg'] at h1
    exact h1
  · have h1 : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.cycZ ℚ Ω l (g ^ m) = 1 := by rw [map_pow, hgc, one_pow]
    rw [← hg'] at h1
    exact h1
  · intro i j hij n hn
    have h1 := hα i j hij (m * n) (Nat.mul_pos hm hn)
    simpa only [pow_mul] using h1
  · have h1 : UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat (W.comp (UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.galEmb ℚ L Ω)) g' = UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.mat W g ^ m := by
      rw [← map_pow, ← hg']
      rfl
    rw [Fin.prod_univ_two] at hch
    rw [h1, Fin.prod_univ_two, UpperTheory.Reformulated.B.FreeAtCompGaloisEmbedding.charpoly_pow_two _ _ _ hch m]
    simp only [Units.val_pow_eq_pow_val]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FrobeniusElement
section
noncomputable def UpperTheory.Reformulated.B.FrobeniusElement.frb :
    {l : ℕ} → [Fact (Nat.Prime l)] → {B₀ : Type} → [inst : CommRing B₀] → (↑l : B₀) = (0 : B₀) → B₀ →+* B₀ :=
  fun {l} [hl : Fact (Nat.Prime l)] {B₀} [CommRing B₀] h =>
    { toFun := fun x => x ^ l
      map_one' := one_pow l
      map_mul' := fun x y => mul_pow x y l
      map_zero' := zero_pow hl.out.ne_zero
      map_add' := fun x y => by
        obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out x y
        rw [hr, h]
        ring }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GaloisBoundFirst
section
open Filter Topology in
theorem UpperTheory.Reformulated.B.GaloisBoundFirst.main :
    ∀ (B : ℂ → ℂ),
      Differentiable ℂ B →
        (∃ (z : ℂ), B z ≠ (0 : ℂ)) →
          ∀ (a : ℂ), ∃ (k : ℕ) (v : ℂ → ℂ), Differentiable ℂ v ∧ v a ≠ (0 : ℂ) ∧ ∀ (z : ℂ), B z = (z - a) ^ k * v z := by
  rintro B hB ⟨z0, hz0⟩ a
  have han : AnalyticOnNhd ℂ B Set.univ := hB.differentiableOn.analyticOnNhd isOpen_univ
  have hnot : ¬ ∀ᶠ z in 𝓝 a, B z = 0 := fun h => hz0
    (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
      (Set.mem_univ z0))
  obtain ⟨k, g, hg, hga, hev⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff (han a (Set.mem_univ a))).2 hnot
  have hev' : ∀ᶠ z in 𝓝 a, z ≠ a → B z / (z - a) ^ k = g z := by
    filter_upwards [hev] with z hz hne
    have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hne)
    rw [hz, smul_eq_mul]
    field_simp
  let v : ℂ → ℂ := fun z => if z = a then g a else B z / (z - a) ^ k
  have hva : v a = g a := by simp [v]
  have hvne : ∀ z, z ≠ a → v z = B z / (z - a) ^ k := fun z hz => by simp [v, hz]
  refine ⟨k, v, ?_, by rwa [hva], ?_⟩
  · intro z
    by_cases hz : z = a
    · subst hz
      have : v =ᶠ[𝓝 z] g := by
        filter_upwards [hev'] with w hw
        by_cases hwz : w = z
        · rw [hwz, hva]
        · rw [hvne w hwz, hw hwz]
      exact (hg.differentiableAt.congr_of_eventuallyEq this)
    · have hd : DifferentiableAt ℂ (fun w => B w / (w - a) ^ k) z :=
        (hB z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow k)
          (pow_ne_zero _ (sub_ne_zero.2 hz))
      have : v =ᶠ[𝓝 z] fun w => B w / (w - a) ^ k := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        exact hvne w hw
      exact hd.congr_of_eventuallyEq this
  · intro z
    by_cases hz : z = a
    · subst hz
      have hB0 : B z = (z - z) ^ k * g z := by
        simpa [smul_eq_mul] using hev.self_of_nhds
      rw [hva]; exact hB0
    · rw [hvne z hz]
      have h0 : (z - a) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hz)
      field_simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRest
section
theorem UpperTheory.Reformulated.B.DYha2.main :
    ∀ {X Y : Type} [inst : AddCommGroup X] [inst_1 : _root_.Module ℂ X] [inst_2 : AddCommGroup Y]
      [inst_3 : _root_.Module ℂ Y] {x : X} {y : Y}, x ≠ (0 : X) → y ≠ (0 : Y) → x ⊗ₜ[ℂ] y ≠ (0 : TensorProduct ℂ X Y) := by
  intro X Y _ _ _ _ x y hx hy h
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero ℂ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_ne_zero ℂ hy
  have key := congrArg (TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ f g)) h
  simp only [TensorProduct.lift.tmul, map_zero, LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at key
  exact (mul_ne_zero hf hg) key
end

