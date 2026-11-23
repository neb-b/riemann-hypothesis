module

public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.NilSurjOfSqZero
public import ReciprocityTheory.DualLattices.Bundle0015

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.MemSupOfRestrictToSubgroupMemSq
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem exists_basis_map_restrictToSubgroup (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ β : Matrix K K C, IsUnit β.det ∧
      AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j) := by
  obtain ⟨B, hB, hAB⟩ := AA.lat
  apply exists_matrix_span_eq hv
  · rw [hAB]
    exact (Submodule.fg_span (Set.finite_range _)).map _
  · rw [eq_top_iff]
    rintro φ -
    let F : N → C := fun x => if h : x ∈ K then φ ⟨x, h⟩ else 0
    have hBB : B *ᵥ (B⁻¹ *ᵥ F) = F := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hB, Matrix.one_mulVec]
    have hF : F = ∑ j, (B⁻¹ *ᵥ F) j • (fun x => B x j) := by
      calc F = B *ᵥ (B⁻¹ *ᵥ F) := hBB.symm
        _ = _ := by
          funext x
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hsm : ∀ (c : C) (g : N → C), resK (R := R) K (c • g) = c • resK (R := R) K g := by
      intro c g; funext k; simp [resK]
    have hφ : φ = resK (R := R) K F := by
      funext k; simp [resK, F]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, hF, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hsm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨fun x => B x j, ?_, rfl⟩
    rw [hAB]
    exact Submodule.subset_span ⟨j, rfl⟩

theorem exists_coset_basis (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∃ f : K → N → C, (∀ j, f j ∈ AA.carrier) ∧ ∀ g ∈ AA.carrier,
      ∃! b : K → N → C, (∀ j, b j ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ K)) ∧
        g = ∑ j, b j * f j := by
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  refine ⟨f, hf, fun g hg => ?_⟩
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  refine ⟨b, ⟨fun j => mem_map_comap_pullbackQuotient AA K (hbA j) (hbinv j), hgb⟩, ?_⟩
  rintro b' ⟨hb', hgb'⟩
  funext j x
  have hc := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood x (fun j => b' j x - b j x) (fun k => by
    have e1 := congrFun hgb (x + k)
    have e2 := congrFun hgb' (x + k)
    simp only [Finset.sum_apply, Pi.mul_apply] at e1 e2
    have h1 : ∀ j, b' j x - b j x = b' j (x + k) - b j (x + k) := fun j => by
      rw [apply_add_of_mem_map_pullbackQuotient K _ (hb' j) x k, hbinv j x k]
    simp only [h1, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp (congrFun hc j)

theorem mem_of_restrictToSubgroup_eq_zero (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ AA.carrier, resK (R := R) K g = 0 →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) *
        AA.carrier := by
  intro g hg hres
  obtain ⟨β, hβ, hAK⟩ := exists_basis_map_restrictToSubgroup hv AA K
  obtain ⟨f, hf, hgood⟩ := exists_family_valuation_det_eq_one hv AA K β hβ hAK
  obtain ⟨b, hbA, hbinv, hgb⟩ := exists_coset_invariant_coefficients hv AA K β hβ hAK f hf hgood hg
  have h0 : (fun j => b j 0) = 0 := eq_zero_of_sum_mul_coset_eq_zero (v := v) K β hβ f hgood 0 _ (fun k => by
    have e : g (k : N) = 0 := by simpa [resK] using congrFun hres k
    calc ∑ j, b j 0 * f j (0 + k) = ∑ j, b j (0 + k) * f j (0 + k) :=
          Finset.sum_congr rfl fun j _ => by rw [hbinv j 0 k]
      _ = g (0 + k) := by rw [hgb]; simp [Finset.sum_apply]
      _ = 0 := by rw [zero_add]; exact e)
  rw [hgb]
  exact Submodule.sum_mem _ fun j _ => Submodule.mul_mem_mul
    (mem_map_augmentationIdeal_comap_pullbackQuotient AA K (hbA j) (hbinv j) (by simpa using congrFun h0 j)) (hf j)

private theorem mem_augIdeal_iff {X : Type} [AddCommGroup X] (M : Submodule R (X → C)) (f : X → C) :
    f ∈ augIdeal M ↔ f ∈ M ∧ f 0 = 0 := by
  simp [augIdeal]

theorem mem_sup_of_restrictToSubgroup_mem_sq (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
    [DecidablePred (· ∈ K)] :
    ∀ g ∈ augIdeal AA.carrier, resK (R := R) K g ∈
        augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) →
      g ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
  intro g hgI hres
  have hIA : ∀ a, a ∈ augIdeal AA.carrier ↔ a ∈ AA.carrier ∧ a 0 = 0 := mem_augIdeal_iff _
  have hII : augIdeal AA.carrier * augIdeal AA.carrier ≤ AA.carrier :=
    Submodule.mul_le.mpr fun a ha b hb => AA.mul_mem a b ((hIA a).1 ha).1 ((hIA b).1 hb).1
  have hle : augIdeal (AA.carrier.map (resK (R := R) K)) * augIdeal (AA.carrier.map (resK (R := R) K)) ≤
      (augIdeal AA.carrier * augIdeal AA.carrier).map (resK (R := R) K) := by
    refine Submodule.mul_le.mpr fun p hp q hq => ?_
    obtain ⟨⟨a, ha, rfl⟩, hp0⟩ := (mem_augIdeal_iff _ _).1 hp
    obtain ⟨⟨b, hb, rfl⟩, hq0⟩ := (mem_augIdeal_iff _ _).1 hq
    refine ⟨a * b, Submodule.mul_mem_mul ((hIA a).2 ⟨ha, ?_⟩) ((hIA b).2 ⟨hb, ?_⟩), ?_⟩
    · simpa [resK] using hp0
    · simpa [resK] using hq0
    · funext k; simp [resK]
  obtain ⟨q, hq, hqg⟩ := hle hres
  have hgq : g - q ∈ AA.carrier := AA.carrier.sub_mem ((hIA g).1 hgI).1 (hII hq)
  have hker := mem_of_restrictToSubgroup_eq_zero hv AA K (g - q) hgq (by rw [map_sub, hqg, sub_self])
  have hmul : (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) * AA.carrier ≤
      (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) ⊔
        augIdeal AA.carrier * augIdeal AA.carrier := by
    refine Submodule.mul_le.mpr fun e he a ha => ?_
    obtain ⟨e', he', rfl⟩ := he
    obtain ⟨he'A, he'0⟩ := (mem_augIdeal_iff _ _).1 he'
    obtain ⟨r, hr⟩ := hopfOrder_exists_algebraMap_eq_of_mem AA ha 0
    have heI : pullQ (R := R) K e' ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨he'A, by simpa [pullQ] using he'0⟩
    have haI : a - r • (1 : N → C) ∈ augIdeal AA.carrier :=
      (hIA _).2 ⟨AA.carrier.sub_mem ha (AA.carrier.smul_mem r AA.one_mem),
        by simp [Algebra.smul_def, hr]⟩
    have hsplit : pullQ (R := R) K e' * a =
        pullQ (R := R) K e' * (a - r • (1 : N → C)) + r • pullQ (R := R) K e' := by
      rw [mul_sub, mul_smul_comm, mul_one, sub_add_cancel]
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.mul_mem_mul heI haI))
      (Submodule.mem_sup_left (Submodule.smul_mem _ r ⟨e', he', rfl⟩))
  have hg : g = (g - q) + q := by abel
  rw [hg]
  exact Submodule.add_mem _ (hmul hker) (Submodule.mem_sup_right hq)

end ReciprocityTheory.PGsh.L2
end
end

-- bundled from ReciprocityTheory.DualLattices.SmKerSurj
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

section

variable {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hsurj : Function.Surjective π.1)

def ell (r : (R : Type u)) : (R' : Type u) := Function.surjInv hsurj r * ξ

end

section

variable {R' R : LAlg R₀} {π : LHom R' R} {ξ : (R' : Type u)}
  (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)

include hker in
lemma π_ξ : π.1 ξ = 0 := by
  have h : ξ ∈ RingHom.ker π.1 := by
    rw [hker]
    exact Ideal.mem_span_singleton_self ξ
  exact (RingHom.mem_ker).1 h

include hker hsq in
lemma ell_spec (a : (R' : Type u)) : ell π ξ hsurj (π.1 a) = a * ξ := by
  have h1 : π.1 (Function.surjInv hsurj (π.1 a)) = π.1 a := Function.surjInv_eq hsurj _
  have h2 : Function.surjInv hsurj (π.1 a) - a ∈ Ideal.span {ξ} := by
    rw [← hker, RingHom.mem_ker, map_sub, h1, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h2
  show Function.surjInv hsurj (π.1 a) * ξ = a * ξ
  have e : Function.surjInv hsurj (π.1 a) = a + c * ξ := by
    rw [hc]
    ring
  rw [e, add_mul, mul_assoc, hsq, mul_zero, add_zero]

include hker in
lemma ell_π (r : (R : Type u)) : π.1 (ell π ξ hsurj r) = 0 := by
  show π.1 (Function.surjInv hsurj r * ξ) = 0
  rw [map_mul, π_ξ hker, mul_zero]

include hker hsq in
lemma ell_add (r r' : (R : Type u)) :
    ell π ξ hsurj (r + r') = ell π ξ hsurj r + ell π ξ hsurj r' := by
  obtain ⟨a, rfl⟩ := hsurj r
  obtain ⟨a', rfl⟩ := hsurj r'
  rw [← map_add (f := _), ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, add_mul]

include hker hsq in
lemma ell_mul (a : (R' : Type u)) (r : (R : Type u)) :
    ell π ξ hsurj (π.1 a * r) = a * ell π ξ hsurj r := by
  obtain ⟨b, rfl⟩ := hsurj r
  rw [← map_mul, ell_spec hsurj hker hsq, ell_spec hsurj hker hsq, mul_assoc]

include hker hsq in
lemma ell_zero : ell π ξ hsurj 0 = 0 := by
  have h := ell_spec hsurj hker hsq 0
  rw [map_zero, zero_mul] at h
  exact h

include hker hsq in
lemma ell_mul_ell (r r' : (R : Type u)) : ell π ξ hsurj r * ell π ξ hsurj r' = 0 := by
  obtain ⟨a, rfl⟩ := hsurj r
  obtain ⟨b, rfl⟩ := hsurj r'
  rw [ell_spec hsurj hker hsq, ell_spec hsurj hker hsq]
  calc a * ξ * (b * ξ) = a * b * (ξ * ξ) := by ring
    _ = 0 := by rw [hsq, mul_zero]

end

section

variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R) (ξ : (R' : Type u))
  (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)

def smAlg : (FP π Dp.π : Type u) →ₐ[R₀] (R' : Type u) where
  toFun x := x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)
  map_one' := by
    show (1 : (R' : Type u)) + ell π ξ hsurj (Dp.κ 1) = 1
    rw [Dp.κ_one, ell_zero hsurj hker hsq, add_zero]
  map_mul' x y := by
    show x.1.1 * y.1.1 + ell π ξ hsurj (Dp.κ (x.1.2 * y.1.2)) =
      (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) * (y.1.1 + ell π ξ hsurj (Dp.κ y.1.2))
    rw [Dp.κ_mul, ← FP.mem π Dp.π x, ← FP.mem π Dp.π y, ell_add hsurj hker hsq,
      ell_mul hsurj hker hsq, ell_mul hsurj hker hsq]
    linear_combination (-1 : (R' : Type u)) *
      ell_mul_ell hsurj hker hsq (Dp.κ x.1.2) (Dp.κ y.1.2)
  map_zero' := by
    show (0 : (R' : Type u)) + ell π ξ hsurj (Dp.κ 0) = 0
    rw [Dp.κ_zero, ell_zero hsurj hker hsq, add_zero]
  map_add' x y := by
    show (x.1.1 + y.1.1) + ell π ξ hsurj (Dp.κ (x.1.2 + y.1.2)) =
      (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) + (y.1.1 + ell π ξ hsurj (Dp.κ y.1.2))
    rw [Dp.κ_add, ell_add hsurj hker hsq]; ring
  commutes' c := by
    show algebraMap R₀ (R' : Type u) c + ell π ξ hsurj (Dp.κ (algebraMap R₀ (Dp.D : Type u) c)) =
      algebraMap R₀ (R' : Type u) c
    rw [Dp.κ_algebraMap, ell_zero hsurj hker hsq, add_zero]

def sm : LHom (FP π Dp.π) R' :=
  ⟨smAlg π Dp ξ hsurj hker hsq, ⟨fun x hx => fp_isUnit π Dp.π x (π.2.map_nonunit _ (by
    convert hx.map π.1 using 1
    show _ = π.1 (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2))
    rw [map_add (f := _), ell_π hsurj hker, add_zero]; rfl))⟩⟩

lemma π_comp_sm : π.comp (sm π Dp ξ hsurj hker hsq) = π.comp (FP.p₁ π Dp.π) := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  show π.1 (x.1.1 + ell π ξ hsurj (Dp.κ x.1.2)) = π.1 x.1.1
  rw [map_add (f := _), ell_π hsurj hker, add_zero]

end

section

variable {R' R : LAlg R₀} (π : LHom R' R) (Dp : DualPair R)

def ι₁ : LHom R' (FP π Dp.π) :=
  FP.lift π Dp.π (LHom.id R') (Dp.σ.comp π) (fun t => (Dp.sect (π.1 t)).symm)

lemma p₁_comp_ι₁ : (FP.p₁ π Dp.π).comp (ι₁ π Dp) = LHom.id R' := Subtype.ext (AlgHom.ext fun _ => rfl)

lemma p₂_comp_ι₁ : (FP.p₂ π Dp.π).comp (ι₁ π Dp) = Dp.σ.comp π := Subtype.ext (AlgHom.ext fun _ => rfl)

lemma sm_comp_ι₁ {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
    (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0) :
    (sm π Dp ξ hsurj hker hsq).comp (ι₁ π Dp) = LHom.id R' := by
  apply Subtype.ext
  apply AlgHom.ext
  intro t
  show t + ell π ξ hsurj (Dp.κ (Dp.σ.1 (π.1 t))) = t
  rw [Dp.κ_σ, ell_zero hsurj hker hsq, add_zero]

lemma p₁_sqZero : (FP.p₁ π Dp.π).SqZero := by
  refine ⟨fun a => ⟨(ι₁ π Dp).1 a, rfl⟩, ?_⟩
  rw [sq, ← le_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  rw [RingHom.mem_ker] at hx hy
  have hx0 : x.1.1 = 0 := hx
  have hy0 : y.1.1 = 0 := hy
  have hx2 : x.1.2 ∈ Ideal.span {Dp.η} := by
    rw [← Dp.ker_eq, RingHom.mem_ker, ← FP.mem π Dp.π x, hx0, map_zero]
  have hy2 : y.1.2 ∈ Ideal.span {Dp.η} := by
    rw [← Dp.ker_eq, RingHom.mem_ker, ← FP.mem π Dp.π y, hy0, map_zero]
  rw [Ideal.mem_bot]
  apply Subtype.ext
  apply Prod.ext
  · show x.1.1 * y.1.1 = 0
    rw [hx0, zero_mul]
  · show x.1.2 * y.1.2 = 0
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hx2
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 hy2
    rw [← hc, ← hc']
    calc c * Dp.η * (c' * Dp.η) = c * c' * (Dp.η * Dp.η) := by ring
      _ = 0 := by rw [Dp.η_sq, mul_zero]

lemma p₂_ker : ∀ a ∈ (FP.p₁ π Dp.π).ker, (FP.p₂ π Dp.π).1.toLinearMap a ∈ Dp.π.ker := by
  intro a ha
  have ha0 : a.1.1 = 0 := ha
  show Dp.π.1 a.1.2 = 0
  rw [← FP.mem π Dp.π a, ha0, map_zero]

variable {ξ : (R' : Type u)} (hsurj : Function.Surjective π.1)
  (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0)

lemma sm_ker : ∀ a ∈ (FP.p₁ π Dp.π).ker, (sm π Dp ξ hsurj hker hsq).1.toLinearMap a ∈ π.ker := by
  intro a ha
  have ha0 : a.1.1 = 0 := ha
  show π.1 (a.1.1 + ell π ξ hsurj (Dp.κ a.1.2)) = 0
  rw [map_add (f := _), ell_π hsurj hker, ha0, map_zero, add_zero]

lemma sm_ker_surj :
    Function.Surjective ((sm π Dp ξ hsurj hker hsq).1.toLinearMap.restrict
      (sm_ker π Dp hsurj hker hsq)) := by
  rintro ⟨b, hb⟩
  have hb' : b ∈ RingHom.ker π.1 := hb
  have hbξ : b ∈ Ideal.span {ξ} := by
    rw [← hker]
    exact hb'
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hbξ
  have hmem : ((0 : (R' : Type u)), Dp.σ.1 (π.1 c) * Dp.η) ∈ fpSub π Dp.π := by
    rw [mem_fpSub]
    show π.1 0 = Dp.π.1 (Dp.σ.1 (π.1 c) * Dp.η)
    rw [map_zero, map_mul, Dp.π_η, mul_zero]
  have hk : (⟨_, hmem⟩ : (FP π Dp.π : Type u)) ∈ (FP.p₁ π Dp.π).ker := by
    show (0 : (R' : Type u)) = 0
    rfl
  refine ⟨⟨⟨_, hmem⟩, hk⟩, ?_⟩
  apply Subtype.ext
  show (0 : (R' : Type u)) + ell π ξ hsurj (Dp.κ (Dp.σ.1 (π.1 c) * Dp.η)) = c * ξ
  rw [Dp.κ_ση, ell_spec hsurj hker hsq, zero_add]

end

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.StThmA
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

def ξmul {R' R : LAlg R₀} (π : LHom R' R) (ξ : (R' : Type u)) (hξ : ξ ∈ π.ker) :
    (R' : Type u) →ₗ[R₀] π.ker where
  toFun r := ⟨ξ * r, by
    rw [Submodule.restrictScalars_mem] at hξ ⊢
    exact Ideal.mul_mem_right r _ hξ⟩
  map_add' a b := by ext; simp [mul_add]
  map_smul' c r := by ext; simp

namespace BX

variable (B : BX R₀)

def ev {R' : LAlg R₀} (h : B.gg →ₗ[R₀] R') (v : B.gg ⊗[R₀] (R' : Type u)) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h LinearMap.id v)

end BX

end ReciprocityTheory.PGsh
end
end

