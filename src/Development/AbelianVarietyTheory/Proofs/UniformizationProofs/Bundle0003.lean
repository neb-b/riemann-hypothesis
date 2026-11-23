module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UT.ExactTerm

theorem exists_ringHom_lift (F : Type) [Field F] [IsAlgClosed F] {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsIntegrallyClosed O] [Algebra O F] [IsFractionRing O F] {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (φ : A →+* ResidueField O)
    (hφ : φ.comp (algebraMap O A) = residue O) :
    ∃ ψ : A →+* O, ψ.comp (algebraMap O A) = RingHom.id O ∧ (residue O).comp ψ = φ := by
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have : (RingHom.ker φ).LiesOver (maximalIdeal O) := ⟨by
    show maximalIdeal O = Ideal.comap (algebraMap O A) (RingHom.ker φ)
    rw [RingHom.comap_ker, hφ, ker_residue]⟩
  obtain ⟨P, hPQ, hP, hPlo⟩ := (RingHom.ker φ).exists_ideal_le_liesOver_of_le
    (p := (⊥ : Ideal O)) (q := maximalIdeal O) bot_le
  have hjinj : Function.Injective (algebraMap O P.ResidueField) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : algebraMap O A y ∈ P := by
      rw [← Ideal.algebraMap_residueField_eq_zero, ← IsScalarTower.algebraMap_apply]
      exact hy
    have h2 : y ∈ P.under O := h1
    rw [← hPlo.over] at h2
    simpa using h2
  let : Algebra F P.ResidueField := (IsFractionRing.lift (K := F) hjinj).toAlgebra
  have : IsScalarTower O F P.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun y => (IsFractionRing.lift_algebraMap hjinj y).symm
  have hrange : ∀ a : A, ∃ y : O, algebraMap O P.ResidueField y = algebraMap A P.ResidueField a := by
    intro a
    have hO : IsIntegral O (algebraMap A P.ResidueField a) :=
      (Algebra.IsIntegral.isIntegral a).algebraMap
    have hF : IsIntegral F (algebraMap A P.ResidueField a) := hO.tower_top
    obtain ⟨r, hr⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := F)
      (K := integralClosure F P.ResidueField)).2 ⟨_, hF⟩
    have hr' : algebraMap F P.ResidueField r = algebraMap A P.ResidueField a := congrArg Subtype.val hr
    have hrO : IsIntegral O r := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom O F P.ResidueField)
        (algebraMap F P.ResidueField).injective]
      simpa [hr'] using hO
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hrO
    exact ⟨y, by rw [IsScalarTower.algebraMap_apply O F P.ResidueField, hy, hr']⟩
  let e : O ≃+* (algebraMap O P.ResidueField).range :=
    RingEquiv.ofBijective (algebraMap O P.ResidueField).rangeRestrict
      ⟨fun a b h => hjinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let π' : A →+* (algebraMap O P.ResidueField).range :=
    (algebraMap A P.ResidueField).codRestrict _ fun a => by
      obtain ⟨y, hy⟩ := hrange a
      exact ⟨y, hy⟩
  have key : ∀ a, algebraMap O P.ResidueField (e.symm (π' a)) = algebraMap A P.ResidueField a :=
    fun a => congrArg Subtype.val (e.apply_symm_apply (π' a))
  refine ⟨e.symm.toRingHom.comp π', ?_, ?_⟩
  · ext y
    apply hjinj
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.id_apply]
    rw [key]
    exact (IsScalarTower.algebraMap_apply O A P.ResidueField y).symm
  · ext a
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have hmem : algebraMap O A (e.symm (π' a)) - a ∈ RingHom.ker φ := by
      apply hPQ
      rw [← Ideal.algebraMap_residueField_eq_zero, map_sub, ← IsScalarTower.algebraMap_apply, key,
        sub_self]
    have h1 : φ (algebraMap O A (e.symm (π' a))) = φ a := by
      rw [← sub_eq_zero, ← map_sub]
      exact (RingHom.mem_ker).mp hmem
    rw [← h1, ← RingHom.comp_apply φ (algebraMap O A), hφ]

theorem exists_section_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of O)) [IsFinite f] [Flat f] (p : Spec (CommRingCat.of (ResidueField O)) ⟶ H)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (residue O))) :
    ∃ q : Spec (CommRingCat.of O) ⟶ H, q ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ q = p := by
  have : IsAffine H := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = H.isoSpec.inv ≫ f := ⟨_, Spec.map_preimage _⟩
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hflat : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    exact MorphismProperty.comp_mem @Flat _ _ (inferInstance : Flat H.isoSpec.inv) ‹Flat f›
  obtain ⟨χ, hχ⟩ : ∃ χ, Spec.map χ = p ≫ H.isoSpec.hom := ⟨_, Spec.map_preimage _⟩
  let _ := φ.hom.toAlgebra
  have : Module.Finite O Γ(H, ⊤) := hfin
  have : Module.Flat O Γ(H, ⊤) := hflat
  have hcomp : χ.hom.comp (algebraMap O Γ(H, ⊤)) = residue O := by
    have h1 : Spec.map (φ ≫ χ) = Spec.map (CommRingCat.ofHom (residue O)) := by
      rw [Spec.map_comp, hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_ringHom_lift F χ.hom hcomp
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ H.isoSpec.inv, ?_, ?_⟩
  · have h2 : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
      exact CommRingCat.hom_ext hψ1
    rw [Category.assoc, ← hφ, ← Spec.map_comp, h2, Spec.map_id]
  · have h3 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (residue O) = χ := by
      exact CommRingCat.hom_ext hψ2
    rw [← Category.assoc, ← Spec.map_comp, h3, hχ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

theorem exists_torsion_lift {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {S : Scheme.{0}}
    (G : Over S) [GrpObj G] (n : ℕ) [IsFinite ((𝟙 G) ^ n : G ⟶ G).left] [Flat ((𝟙 G) ^ n : G ⟶ G).left]
    (t : Spec (CommRingCat.of O) ⟶ S)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G) (hx : x ^ n = 1) :
    ∃ y : Over.mk t ⟶ G, y ^ n = 1 ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ y.left = x.left := by
  have hpow : ∀ {Y : Over S} (z : Y ⟶ G), z ^ n = z ≫ (𝟙 G) ^ n := fun z => by
    rw [MonObj.comp_pow, Category.comp_id]
  have hxm : x.left ≫ ((𝟙 G) ^ n : G ⟶ G).left =
      Spec.map (CommRingCat.ofHom (residue O)) ≫ t ≫ η[G].left := by
    have h1 : (x ≫ (𝟙 G) ^ n).left = (1 : Over.mk (Spec.map (CommRingCat.ofHom (residue O)) ≫ t) ⟶ G).left := by
      rw [← hpow, hx]
    rw [Over.comp_left, CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left] at h1
    rw [h1]
    exact Category.assoc _ _ _
  obtain ⟨q, hq1, hq2⟩ := exists_section_lift O
    (pullback.snd ((𝟙 G) ^ n : G ⟶ G).left (t ≫ η[G].left))
    (pullback.lift x.left (Spec.map (CommRingCat.ofHom (residue O))) hxm) (pullback.lift_snd _ _ _)
  have hw : ((𝟙 G) ^ n : G ⟶ G).left ≫ G.hom = G.hom := Over.w _
  have he : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]
  refine ⟨Over.homMk (q ≫ pullback.fst _ _) ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hw, pullback.condition_assoc, Category.assoc, he, Category.comp_id,
      ← Category.assoc, hq1]
    exact Category.id_comp t
  · rw [hpow, CategoryTheory.Hom.one_def]
    ext
    change (q ≫ pullback.fst _ _) ≫ ((𝟙 G) ^ n : G ⟶ G).left = t ≫ η[G].left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq1]
    exact Category.id_comp _
  · change Spec.map (CommRingCat.ofHom (residue O)) ≫ (q ≫ pullback.fst _ _) = x.left
    rw [← Category.assoc, hq2, pullback.lift_fst]

end GlobalTheory.UT.ExactTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LeOfPowLePolyMulPow
section
namespace GlobalTheory.UU

theorem le_of_pow_le_poly_mul_pow (A B K a g : ℕ)
    (H : ∀ k, A ^ k ≤ K * B ^ k * (1 + k * a) ^ g) : A ≤ B := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · have := H 1
    simp [hB] at this
    omega
  by_contra hAB
  push Not at hAB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr : (1 : ℝ) < (A : ℝ) / B := by
    rw [one_lt_div hBr]; exact_mod_cast hAB
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt g hr).const_mul
    ((K : ℝ) * (1 + a) ^ g)
  rw [mul_zero] at ht
  have h1 : ∀ᶠ k : ℕ in Filter.atTop,
      (1 : ℝ) ≤ ((K : ℝ) * (1 + a) ^ g) * ((k : ℝ) ^ g / ((A : ℝ) / B) ^ k) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk' : A ^ k ≤ K * B ^ k * ((1 + a) * k) ^ g := by
      refine (H k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      nlinarith
    have hk2 : (A : ℝ) ^ k ≤ K * (B : ℝ) ^ k * ((1 + a) * k) ^ g := by exact_mod_cast hk'
    have hA : (0 : ℝ) < A := by exact_mod_cast (hB.trans hAB)
    rw [div_pow, ← mul_div_assoc, div_div_eq_mul_div, one_le_div (by positivity)]
    refine hk2.trans (le_of_eq ?_)
    rw [mul_pow]; ring
  have := ge_of_tendsto ht h1
  linarith

theorem degree_eq_pow_of_growth :
    ∀ (h : ℕ → ℕ) (g c C a d q : ℕ), 1 ≤ c → 1 ≤ q → (∀ t t', t ≤ t' → h t ≤ h t') → (∀ t, 1 ≤ t → t ^ g ≤ c * h t ∧ h t ≤ C * t ^ g) → (∀ t, d * h t ≤ h (q * (t + a)) ∧ h (q * t) ≤ d * h (t + a)) → d = q ^ g := by
  intro h g c C a d q hc hq hm hg hd
  have h1 : 1 ≤ h 1 := by
    have := (hg 1 le_rfl).1
    rcases Nat.eq_zero_or_pos (h 1) with h0 | h0
    · simp [h0] at this
    · exact h0
  have up : ∀ k t, h (q ^ k * t) ≤ d ^ k * h (t + k * a) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have e1 : q ^ (k + 1) * t = q ^ k * (q * t) := by ring
      rw [e1]
      refine (ih _).trans ?_
      rw [pow_succ, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      have e2 : t + (k + 1) * a = t + k * a + a := by ring
      rw [e2]
      refine le_trans (hm _ _ ?_) (hd (t + k * a)).2
      rw [mul_add]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hq) _
  have lo : ∀ k, d ^ k ≤ h (q ^ k * (1 + k * a)) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [pow_succ, mul_comm]
      refine (Nat.mul_le_mul_left d ih).trans ((hd _).1.trans (hm _ _ ?_))
      have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
      have e : q ^ (k + 1) * (1 + (k + 1) * a) = q * (q ^ k * (1 + k * a) + q ^ k * a) := by ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hp) _)
  apply le_antisymm
  · apply le_of_pow_le_poly_mul_pow d (q ^ g) C a g
    intro k
    have hp : 1 ≤ q ^ k * (1 + k * a) := Nat.mul_pos (Nat.pow_pos hq) (by omega)
    refine (lo k).trans ((hg _ hp).2.trans (le_of_eq ?_))
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k g]; ring
  · apply le_of_pow_le_poly_mul_pow (q ^ g) d (c * C) a g
    intro k
    have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    have a1 := (hg _ hp).1
    have a2 := up k 1
    rw [mul_one] at a2
    have a3 := (hg (1 + k * a) (by omega)).2
    calc (q ^ g) ^ k = (q ^ k) ^ g := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ c * h (q ^ k) := a1
      _ ≤ c * (d ^ k * (C * (1 + k * a) ^ g)) :=
        Nat.mul_le_mul_left _ (a2.trans (Nat.mul_le_mul_left _ a3))
      _ = _ := by ring

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ShortestVectorStrictOfMul
section
namespace GlobalTheory

theorem shortest_vector_strict_of_mul :
    ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (B : X →+ X →+ ℤ), (∀ a b, Q (a + b) = Q a + Q b + B a b) → (∀ a, 2 * Q a = B a a) → (∀ a, a ≠ 0 → 1 ≤ Q a) → ∀ (n r : ℕ), 1 ≤ n → 2 ≤ r → ∀ z : X, (∀ m, Q z ≤ Q (z + n • m)) → ∀ m : X, (n * r) • m ≠ 0 → Q z < Q (z + (n * r) • m) := by
  intro X _ Q B hadd hdiag hpos n r _ hr z hmin m hm
  have hnr : (n * r) • m = r • (n • m) := by rw [mul_comm, mul_smul]
  rw [hnr] at hm ⊢
  have h1 := hmin m
  generalize n • m = a at hm h1
  have ha : a ≠ 0 := by
    rintro rfl
    exact hm (smul_zero _)
  have hQa := hpos a ha
  have h2 : 2 * Q (r • a) = (r : ℤ) * ((r : ℤ) * (2 * Q a)) := by
    rw [hdiag, hdiag]
    simp only [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]
  have h3 : B z (r • a) = (r : ℤ) * B z a := by
    simp only [map_nsmul, nsmul_eq_mul]
  rw [hadd] at h1 ⊢
  rw [h3]
  have hr' : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have h4 : 0 ≤ (r : ℤ) * (Q a + B z a) := mul_nonneg (by omega) (by omega)
  have h5 : 0 < ((r : ℤ) * (r - 1)) * Q a :=
    mul_pos (mul_pos (by omega) (by omega)) (by omega)
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TensorComponentNeZeroIff
section
namespace GlobalTheory

theorem tensor_component_ne_zero_iff (F : Type) [Field F] (X C : Type) [Finite C] (cl : X → C)
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (c : C) (s : E), ∃ s' : E, ∀ a,
      (cl a = c → ex a s' = ex a s) ∧ (cl a ≠ c → ex a s' = 0))
    (hinj : ∀ a, ex a ≠ 0 → ∀ s, (∀ b, cl b ≠ cl a → ex b s = 0) → ex a s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ a b, cl a ≠ cl b → TensorProduct.map (ex a) (ex b) w = 0)
    (a b : X) (hab : cl a = cl b) :
    TensorProduct.map (ex a) (ex b) w ≠ 0 ↔ ex a ≠ 0 ∧ ex b ≠ 0 := by
  classical
  have := Fintype.ofFinite C
  choose p hp using hcut
  have hext : ∀ s t : E, (∀ x, ex x s = ex x t) → s = t := fun s t h =>
    sub_eq_zero.mp (hsep _ fun x => by rw [map_sub, h x, sub_self])
  let π : C → E →ₗ[F] E := fun c =>
    { toFun := p c
      map_add' := fun s t => hext _ _ fun x => by
        by_cases hx : cl x = c
        · rw [map_add (f := _), (hp c _ x).1 hx, (hp c _ x).1 hx, (hp c _ x).1 hx, map_add (f := _)]
        · rw [map_add (f := _), (hp c _ x).2 hx, (hp c _ x).2 hx, (hp c _ x).2 hx, add_zero]
      map_smul' := fun r s => hext _ _ fun x => by
        by_cases hx : cl x = c
        · rw [RingHom.id_apply, map_smul, (hp c _ x).1 hx, (hp c _ x).1 hx, map_smul]
        · rw [RingHom.id_apply, map_smul, (hp c _ x).2 hx, (hp c _ x).2 hx, smul_zero] }
  have h1 : ∀ c s x, cl x = c → ex x (π c s) = ex x s := fun c s x h => (hp c s x).1 h
  have h0 : ∀ c s x, cl x ≠ c → ex x (π c s) = 0 := fun c s x h => (hp c s x).2 h
  have hsum : ∑ c, π c = LinearMap.id := by
    refine LinearMap.ext fun s => hext _ _ fun x => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single (cl x)]
    · exact h1 _ s x rfl
    · intro c _ hc
      exact h0 c s x (Ne.symm hc)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfac : ∀ x, ex x ≠ 0 → ∃ r : W x →ₗ[F] E, r ∘ₗ ex x = π (cl x) := by
    intro x hx
    have hk : LinearMap.ker (ex x ∘ₗ (LinearMap.range (π (cl x))).subtype) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨_, s, rfl⟩ hs
      exact Subtype.ext (hinj x hx _ (fun y hy => h0 _ s y hy) hs)
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
    refine ⟨(LinearMap.range (π (cl x))).subtype ∘ₗ g, LinearMap.ext fun s => ?_⟩
    have h2 := congrArg Subtype.val
      (LinearMap.congr_fun hg ⟨π (cl x) s, LinearMap.mem_range_self _ s⟩)
    rw [LinearMap.comp_apply, ← h1 (cl x) s x rfl]
    exact h2
  have hpass : ∀ x y, ex x ≠ 0 → ex y ≠ 0 → TensorProduct.map (ex x) (ex y) w = 0 →
      TensorProduct.map (π (cl x)) (π (cl y)) w = 0 := by
    intro x y hx hy h
    obtain ⟨r, hr⟩ := hfac x hx
    obtain ⟨t, ht⟩ := hfac y hy
    rw [← hr, ← ht, TensorProduct.map_comp, LinearMap.comp_apply, h, map_zero]
  constructor
  · intro h
    constructor
    · intro ha
      apply h
      rw [ha, TensorProduct.map_zero_left, LinearMap.zero_apply]
    · intro hb
      apply h
      rw [hb, TensorProduct.map_zero_right, LinearMap.zero_apply]
  · rintro ⟨ha, hb⟩ h
    have hall : ∀ c, TensorProduct.map (π (cl a)) (π c) w = 0 := by
      intro c
      by_cases hc : cl b = c
      · rw [← hc]
        exact hpass a b ha hb h
      by_cases hy : ∃ y, cl y = c ∧ ex y ≠ 0
      · obtain ⟨y, rfl, hy⟩ := hy
        exact hpass a y ha hy (hoff a y (hab ▸ hc))
      · have hz : π c = 0 := by
          refine LinearMap.ext fun s => hsep _ fun y => ?_
          by_cases hyc : cl y = c
          · have : ex y = 0 := by
              by_contra hne
              exact hy ⟨y, hyc, hne⟩
            rw [this, LinearMap.zero_apply]
          · exact h0 c s y hyc
        rw [hz, TensorProduct.map_zero_right, LinearMap.zero_apply]
    have hz : π (cl a) = 0 := by
      apply hfull
      have e : TensorProduct.map (π (cl a)) (∑ c, π c) =
          ∑ c, TensorProduct.map (π (cl a)) (π c) :=
        map_sum (TensorProduct.mapBilinear (RingHom.id F) E E E E (π (cl a))) π Finset.univ
      rw [← hsum, e, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun c _ => hall c
    apply ha
    refine LinearMap.ext fun s => ?_
    rw [← h1 (cl a) s a rfl, hz, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end GlobalTheory
end

