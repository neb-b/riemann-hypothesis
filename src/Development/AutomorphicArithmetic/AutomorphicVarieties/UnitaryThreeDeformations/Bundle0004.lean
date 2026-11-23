module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtGrSub
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem ltgs_inv_mem {M : Type} [Group M] [Finite M] (S : Submonoid M) {x : M} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hk : 0 < orderOf x := orderOf_pos x
  have e : x⁻¹ = x ^ (orderOf x - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hk, pow_orderOf_eq_one]
  rw [e]
  exact S.pow_mem hx _

theorem UpperTheory.V.UnitaryThreeInertia.lt_grSub :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R] (ℬ : ℤ → Submodule O R) [SetLike.GradedMonoid ℬ],
      ∃ S : Subgroup (GG (m := 3) (R := R)), ∀ x, x ∈ S ↔ GrMat ℬ x.mat := by
  intro O R _ _ _ _ ℬ _
  classical
  have hwt : ∀ a c b : Fin 3, wt a c + wt c b = wt a b := by
    intro a c b; simp only [wt]; ring
  have hwrev : ∀ a b : Fin 3, wt b.rev a.rev = wt a b := by
    intro a b; fin_cases a <;> fin_cases b <;> rfl
  have hone : GrMat ℬ (1 : Matrix (Fin 3) (Fin 3) R) := by
    intro a b
    by_cases h : a = b
    · subst h
      rw [Matrix.one_apply_eq]
      have h0 : wt a a = 0 := by simp [wt]
      rw [h0]
      exact SetLike.GradedOne.one_mem
    · rw [Matrix.one_apply_ne h]
      exact Submodule.zero_mem _
  have hmul : ∀ X Y : Matrix (Fin 3) (Fin 3) R, GrMat ℬ X → GrMat ℬ Y → GrMat ℬ (X * Y) := by
    intro X Y hX hY a b
    rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [← hwt a c b]
    exact SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  let T : Submonoid (GL (Fin 3) R) :=
    { carrier := {g | GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R)}
      mul_mem' := fun {g h} hg hh => by
        show GrMat ℬ ((g * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        rw [Units.val_mul]
        exact hmul _ _ hg hh
      one_mem' := by
        show GrMat ℬ ((1 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
        rw [Units.val_one]
        exact hone }
  have hinv : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) :=
    fun g hg => ltgs_inv_mem T (x := g) hg
  have hJ : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * M * Jmat R 3) a b = M a.rev b.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat] <;> rfl
  have htheta : ∀ g : GL (Fin 3) R, GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro g hg a b
    rw [theta_val, hJ, Matrix.transpose_apply, ← hwrev a b]
    exact hinv g hg b.rev a.rev
  have hact : ∀ (s : ℤˣ) (g : GL (Fin 3) R), GrMat ℬ (g : Matrix (Fin 3) (Fin 3) R) →
      GrMat ℬ ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro s g hg
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [sgnAct_one]; exact hg
    · rw [sgnAct_neg_one]; exact htheta g hg
  haveI : Finite (GG (m := 3) (R := R)) :=
    Finite.of_injective (fun x : GG (m := 3) (R := R) => (x.left, x.right))
    (fun x y h => SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let S0 : Submonoid (GG (m := 3) (R := R)) :=
    { carrier := {x | GrMat ℬ x.mat}
      mul_mem' := fun {x y} hx hy => by
        show GrMat ℬ ((x * y).left : Matrix (Fin 3) (Fin 3) R)
        rw [SemidirectProduct.mul_left, Units.val_mul]
        exact hmul _ _ hx (hact _ _ hy)
      one_mem' := by
        show GrMat ℬ ((1 : GG (m := 3) (R := R)).left : Matrix (Fin 3) (Fin 3) R)
        rw [SemidirectProduct.one_left, Units.val_one]
        exact hone }
  exact ⟨{ S0 with inv_mem' := fun {x} hx => ltgs_inv_mem S0 hx }, fun x => Iff.rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtRedConj
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem entIn_sub_iff {C : Type} [CommRing C] (I : Ideal C) (X Y : Matrix (Fin 3) (Fin 3) C) :
    EntIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext a b
    simp only [Matrix.map_apply]
    exact Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using h a b)
  · intro h a b
    have hab := congrFun (congrFun h a) b
    simp only [Matrix.map_apply] at hab
    simpa [Matrix.sub_apply] using Ideal.Quotient.eq.mp hab

private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  unfold CongOne
  rw [entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro e
    exact Units.ext e
  · intro e
    exact congrArg Units.val e

private theorem map_conjBy {C D : Type} [CommRing C] [Group D] (I : Ideal C) (h : GL (Fin 3) C)
    (hh : CongOne I h) (r : D →* GG (m := 3) (R := C)) (g : D) :
    GG.map (Ideal.Quotient.mk I) (conjBy h r g) = GG.map (Ideal.Quotient.mk I) (r g) := by
  have e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1 := by
    unfold GG.map
    rw [SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e,
    one_mul, inv_one, mul_one]

private theorem mats_conjBy {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) (g : D) :
    mats (conjBy h r) g =
      (h : Matrix (Fin 3) (Fin 3) C) * mats r g *
        ((sgnAct 3 C (r g).right h⁻¹ : GL (Fin 3) C) : Matrix (Fin 3) (Fin 3) C) := by
  simp [mats, GG.mat, conjBy, GG.ofGL, SemidirectProduct.mul_left, Units.val_mul]

theorem UpperTheory.V.UnitaryThreeInertia.lt_red_conj :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R]
      [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (Ψ : D →* Oˣ)
      (r : D →* GG (m := 3) (R := R)) (h : GL (Fin 3) R),
      InHat h → Red η Ψ r → InHat h⁻¹ ∧ Red η Ψ (conjBy h r) ∧ (IsLocallyConstant η → IsLocallyConstant (mats r) → IsLocallyConstant (mats (conjBy h r))) := by
  intro O R D _ _ _ _ _ _ _ η Ψ r h hh hr
  have hinv : InHat h⁻¹ := by
    show CongOne (maximalIdeal R) h⁻¹
    rw [congOne_iff, map_inv, (congOne_iff _ h).mp hh, inv_one]
  have hright : ∀ g, (conjBy h r g).right = (r g).right := by
    intro g
    simp [conjBy, GG.ofGL]
  refine ⟨hinv, ⟨fun g => (hright g).trans (hr.mult g), fun g => ?_⟩, fun hη hm => ?_⟩
  · rw [entIn_sub_iff]
    have h0 := (entIn_sub_iff _ _ _).mp (hr.red g)
    rw [← h0, ← GG.map_mat, ← GG.map_mat, map_conjBy _ h hh]
  · have hfun : mats (conjBy h r) = fun g =>
        (h : Matrix (Fin 3) (Fin 3) R) * mats r g *
          ((sgnAct 3 R (η g) h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
      funext g
      rw [mats_conjBy, hr.mult g]
    rw [hfun]
    exact IsLocallyConstant.comp₂ hm hη fun M s =>
      (h : Matrix (Fin 3) (Fin 3) R) * M * ((sgnAct 3 R s h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtUpper
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

private theorem lu_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

private theorem lu_up {R : Type} [CommRing R] (U k T : Matrix (Fin 3) (Fin 3) R) (e : U * k = k * T)
    (hU : ∀ a b, wt a b < 0 → U a b = 0) (hT : ∀ a b, wt a b < 0 → T a b = 0)
    (hu : ∀ a b, a ≠ b → IsUnit (U a a - T b b)) :
    ∀ a b, wt a b < 0 → k a b = 0 := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have t10 := hT 1 0 (by decide)
  have t20 := hT 2 0 (by decide)
  have t21 := hT 2 1 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, t10, t20, t21] at e10 e20 e21
  have k20 : k 2 0 = 0 := (hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)
  have k10 : k 1 0 = 0 := (hu 1 0 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e10; linear_combination e10)
  have k21 : k 2 1 = 0 := (hu 2 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e21; linear_combination e21)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

private theorem lu_J {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

end UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_upper :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D]
      (η : D →* ℤˣ) (Ψ : D →* Oˣ) (r : D →* GG (m := 3) (R := R)) (x : D),
      Red η Ψ r → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → Upper η r → ∀ g a b, wt a b < 0 → (r g).mat a b = 0 := by
  intro O R D _ _ _ _ _ _ η Ψ r x hr hx hΨ hU g
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hU g hg
  have hX : ∀ x a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O)) := by
    intro x a
    have := (residue_eq_zero_iff _).2 (hr.red x a a)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
  obtain ⟨y, hy⟩ : ∃ y, y = g⁻¹ * x⁻¹ * g := ⟨_, rfl⟩
  have hηy : η y = 1 := by simp [hy, hx]
  have hΨy : Ψ y = (Ψ x)⁻¹ := by simp [hy]
  have rx : (r x).right = 1 := (hr.mult x).trans hx
  have ry : (r y).right = 1 := (hr.mult y).trans hηy
  have rg : (r g).right = -1 := (hr.mult g).trans hg
  have e0 : r x * r g = r g * (r y)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hy]; congr 1; group
  have e1 : (r x).left * (r g).left = (r g).left * theta ((r y).left⁻¹) := by
    have := congrArg SemidirectProduct.left e0
    simpa [rx, ry, rg] using this
  have e2 : (r x).mat * (r g).mat = (r g).mat * (Jmat R 3 * (r y).matᵀ * Jmat R 3) := by
    have := congrArg Units.val e1
    rwa [Units.val_mul, Units.val_mul, theta_val, inv_inv] at this
  refine lu_up _ _ _ e2 (hU x hx) (fun a b hab => ?_) (fun a b hab => ?_)
  · rw [lu_J]
    refine hU y hηy _ _ ?_
    have : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
    rwa [this]
  · have w : wt1 b.rev = -wt1 b := by fin_cases b <;> rfl
    rw [lu_J, ← residue_ne_zero_iff_isUnit, map_sub, hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit, hΨy, w, _root_.inv_zpow', neg_neg]
    exact (lu_unit (Ψ x) hΨ a b hab).map _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtZhat
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.V.UnitaryThreeInertia.lt_zhat :
    ∀ {D E E' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group E] [Finite E] [Group E'] (I : Subgroup D) (φ : D),
      (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ →
      (∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧ d φ = Multiplicative.ofAdd 1) →
      ∀ (q : E →* E') (w' : D →* E') (e : E), IsLocallyConstant w' → (∀ s ∈ I, w' s = 1) → q e = w' φ →
      ∃ w : D →* E, IsLocallyConstant w ∧ (∀ s ∈ I, w s = 1) ∧ q.comp w = w' ∧ ∀ g, w g ∈ Subgroup.zpowers e := by
  intro D E E' _ _ _ _ _ _ I φ hcl hd q w' e hw' hw'I hqe
  obtain ⟨d, hdc, hdI, hdφ⟩ := hd (orderOf e) (orderOf_pos e)
  haveI : NeZero (orderOf e) := ⟨(orderOf_pos e).ne'⟩
  let w : D →* E :=
    { toFun := fun g => e ^ (Multiplicative.toAdd (d g)).val
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [map_mul, toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add] }
  have hwapp : ∀ g, w g = e ^ (Multiplicative.toAdd (d g)).val := fun g => rfl
  have hwc : IsLocallyConstant w := hdc.comp fun x => e ^ (Multiplicative.toAdd x).val
  have hφ : w φ = e := by
    rw [hwapp, hdφ, toAdd_ofAdd, ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  have hwI : ∀ s ∈ I, w s = 1 := by
    intro s hs
    rw [hwapp, hdI s hs]
    simp
  refine ⟨w, hwc, hwI, ?_, fun g => by rw [hwapp]; exact Subgroup.npow_mem_zpowers e _⟩
  have hf : IsLocallyConstant fun x => (q (w x))⁻¹ * w' x :=
    IsLocallyConstant.comp₂ (hwc.comp q) hw' fun a b => a⁻¹ * b
  have hclosed : IsClosed ((q.comp w).eqLocus w' : Set D) := by
    have e1 : ((q.comp w).eqLocus w' : Set D) = (fun x => (q (w x))⁻¹ * w' x) ⁻¹' {1} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, inv_mul_eq_one]
      exact Iff.rfl
    rw [e1]
    exact (hf.isClopen_fiber 1).isClosed
  have hle : I ⊔ Subgroup.zpowers φ ≤ (q.comp w).eqLocus w' := by
    refine sup_le (fun s hs => ?_) (Subgroup.zpowers_le.2 ?_)
    · show q (w s) = w' s
      rw [hwI s hs, map_one, hw'I s hs]
    · show q (w φ) = w' φ
      rw [hφ, hqe]
  have htop : ⊤ ≤ (q.comp w).eqLocus w' := by
    rw [← hcl]
    exact Subgroup.topologicalClosure_minimal _ hle hclosed
  ext g
  exact htop (Subgroup.mem_top g)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem map_diagonal_rep_matrix_eq {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (g : D) :
    (GG.map (algebraMap O R) (r0 η Ψ g)).mat = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g) := by
  rw [GG.map_mat]
  show ((tor O (Ψ g)).val).map (algebraMap O R) = _
  rw [tor_val, Matrix.diagonal_map (map_zero _)]
  rfl

private theorem conjBy_inv_one {R D : Type} [CommRing R] [Group D] (r : D →* @UpperTheory.V.U3.GG 3 R _) :
    conjBy (1 : GL (Fin 3) R)⁻¹ r = r := by
  ext1 g
  simp [conjBy]

private theorem diagIn_one {O R D : Type} [CommRing O] [CommRing R] [Algebra O R] [Group D]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* @UpperTheory.V.U3.GG 3 R _)
    (hr : ∀ g, (r g).mat = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g)) : DiagIn η Ψ I r 1 := by
  have hne : ∀ a b : Fin 3, wt a b ≠ 0 → a ≠ b := by
    intro a b h hab
    subst hab
    simp [wt] at h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro g _ a b hab
    rw [conjBy_inv_one, hr]
    exact Matrix.diagonal_apply_ne _ (hne a b hab.ne)
  · intro s _ _ a
    rw [conjBy_inv_one, hr, Matrix.diagonal_apply_eq]
  · intro g _ a b hab
    rw [conjBy_inv_one, hr]
    exact Matrix.diagonal_apply_ne _ (hne a b hab.ne')

theorem UpperTheory.V.UnitaryThreeInertia.isPt_rz :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] [IsLocalHom (algebraMap O R)], F.IsPt g₁ (F.rz R) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hok g₁ R _ _ _ _
  have hmat : ∀ g, (F.rz R g).mat = diagonal fun a => algebraMap O R (psi F.Ψ a g) :=
    fun g => map_diagonal_rep_matrix_eq F.η F.Ψ g
  have hinhat : InHat (1 : GL (Fin 3) R) := by
    intro a b
    simp
  have hloc : ∀ v, ∀ s, ((F.rz R).comp (F.loc v) s).mat =
      diagonal fun a => algebraMap O R (psi (F.Ψv v) a s) := fun v s => hmat _
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro g
    rfl
  · intro g a b
    have e : (F.rz R g).mat = (r0 F.η F.Ψ g).mat.map (algebraMap O R) := GG.map_mat _ _
    rw [e, sub_self, Matrix.zero_apply]
    exact zero_mem _
  · intro v
    refine ⟨fun _ => ⟨1, hinhat, (diagIn_one _ _ _ _ (hloc v)).toTriIn⟩,
      fun _ => ⟨1, hinhat, diagIn_one _ _ _ _ (hloc v)⟩, fun hv s hs => ?_⟩
    have h1 : F.Ψ (F.loc v s) = 1 := hok.teich v hv s hs
    have h2 : F.η (F.loc v s) = 1 := hs.1.2
    show GG.map (algebraMap O R) (r0 F.η F.Ψ (F.loc v s)) = 1
    have e : r0 F.η F.Ψ (F.loc v s) = 1 := by
      apply SemidirectProduct.ext
      · rw [unitaryThreeReflection_left, h1, map_one]
        rfl
      · exact h2
    rw [e, map_one]
  · have hc : ∀ a, psi F.Ψ a F.c = 1 := by
      intro a
      simp [psi, hok.Ψc]
    refine ⟨?_, ?_, ?_⟩
    · rw [hmat]
      simp [hc, Matrix.diagonal_one]
    · simp [zmat, hmat]
    · simp [zmat, hmat]
  · intro n
    have hle : Ideal.map (algebraMap O R) (maximalIdeal O ^ n) ≤ maximalIdeal R ^ n := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono
        (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_nonunit (algebraMap O R) x hx)) n
    have key : ∀ g g', Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g : O) =
        Ideal.Quotient.mk (maximalIdeal O ^ n) (F.Ψ g' : O) → ∀ a,
        Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap O R (psi F.Ψ a g)) =
        Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap O R (psi F.Ψ a g')) := by
      intro g g' h a
      let q : O →* O ⧸ maximalIdeal O ^ n := (Ideal.Quotient.mk (maximalIdeal O ^ n) : O →* O ⧸ maximalIdeal O ^ n)
      have hu : Units.map q (F.Ψ g) = Units.map q (F.Ψ g') := Units.ext h
      have h2 : ((Units.map q (F.Ψ g ^ wt1 a) : (O ⧸ maximalIdeal O ^ n)ˣ) : O ⧸ maximalIdeal O ^ n) =
          ((Units.map q (F.Ψ g' ^ wt1 a) : (O ⧸ maximalIdeal O ^ n)ˣ) : O ⧸ maximalIdeal O ^ n) := by
        rw [map_zpow (Units.map q) (F.Ψ g) (wt1 a), map_zpow (Units.map q) (F.Ψ g') (wt1 a), hu]
      have h3 : Ideal.Quotient.mk (maximalIdeal O ^ n) (psi F.Ψ a g) =
          Ideal.Quotient.mk (maximalIdeal O ^ n) (psi F.Ψ a g') := h2
      rw [Ideal.Quotient.eq] at h3 ⊢
      rw [← map_sub]
      exact hle (Ideal.mem_map_of_mem _ h3)
    have hf := hok.Ψ_cont n
    rw [IsLocallyConstant.iff_exists_open] at hf ⊢
    intro x
    obtain ⟨U, hU, hxU, hUx⟩ := hf x
    refine ⟨U, hU, hxU, fun x' hx' => ?_⟩
    simp only [hmat]
    rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    exact key x' x (hUx x' hx') a
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MemSatSqIffConstantCoeffAndLinearCoeffEqZero
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private lemma order_of_mem_sq {O σ : Type} [CommRing O] (I : Ideal (MvPowerSeries σ O))
    (hI : ∀ f ∈ I, constantCoeff f = 0) : ∀ f ∈ I ^ 2, ((2 : ℕ) : ℕ∞) ≤ f.order := by
  intro x hx
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
  · refine le_trans ?_ le_order_mul
    have h := add_le_add (one_le_order_iff_constCoeff_eq_zero.2 (hI a ha))
      (one_le_order_iff_constCoeff_eq_zero.2 (hI b hb))
    rwa [one_add_one_eq_two] at h
  · intro f g hf hg
    exact le_trans (le_min hf hg) min_order_le_add

private lemma mem_sq_of_coeff {O σ : Type} [CommRing O] [Fintype σ] (I : Ideal (MvPowerSeries σ O))
    (hI : ∀ i, (X i : MvPowerSeries σ O) ∈ I) (f : MvPowerSeries σ O)
    (hf : ∀ m : σ →₀ ℕ, m.degree < 2 → coeff m f = 0) : f ∈ I ^ 2 := by
  classical
  have key : ∃ μ : Finset (σ →₀ ℕ), (μ : Set _) ⊆ {m : σ →₀ ℕ | 2 ≤ m.degree} ∧
      ∀ f : MvPowerSeries σ O, (∀ m, m ∉ {m : σ →₀ ℕ | 2 ≤ m.degree} → coeff m f = 0) →
      ∃ b : (σ →₀ ℕ) → MvPowerSeries σ O, (∀ m, b m ∈ wtPart O (fun _ : σ => (0 : ℤ)) 0) ∧
        f = ∑ m ∈ μ, b m * monomial m 1 :=
    part_span O (MvPowerSeries σ O) ℤ (WPres.free O fun _ : σ => (0 : ℤ))
      {m : σ →₀ ℕ | 2 ≤ m.degree} 0 (fun (m : σ →₀ ℕ) _ => by
        show Finsupp.weight (fun _ : σ => (0 : ℤ)) m = 0
        simp [Finsupp.weight_apply, Finsupp.sum])
  obtain ⟨μ, hμ, hs⟩ := key
  obtain ⟨b, -, hb⟩ := hs f (fun m hm => hf m (not_le.1 hm))
  rw [hb]
  refine Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _ ?_
  have hm2 : 2 ≤ m.degree := hμ hm
  refine Ideal.pow_le_pow_right hm2 ?_
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hI i) _

private lemma low_degree {σ : Type} (m : σ →₀ ℕ) (hm : m.degree < 2) : m = 0 ∨ ∃ i, m = Finsupp.single i 1 := by
  rcases (show m.degree = 0 ∨ m.degree = 1 by omega) with h | h
  · exact Or.inl ((Finsupp.degree_eq_zero_iff m).1 h)
  · have : m ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]; exact h
    obtain ⟨i, hi⟩ := this
    exact Or.inr ⟨i, hi.symm⟩

theorem UpperTheory.mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ) (f : FA O wt),
        f ∈ satSq (x0 O wt) ↔ constantCoeff (ser f) = 0 ∧ ∀ i, coeff (Finsupp.single i 1) (ser f) = 0 := by
  intro O _ _ σ _ wt f
  classical
  have hk := (ker_pow O (MvPowerSeries σ O) ℤ (WPres.free O wt) (freeOrigin O wt) 2).1
  have ho : ∀ g : MvPowerSeries σ O, (WPres.free O wt).origin (freeOrigin O wt) g = constantCoeff g :=
    fun g => (WPres.free O wt).origin_π (freeOrigin O wt) g
  have hiff : ∀ g : FA O wt, g ∈ RingHom.ker (x0 O wt) ^ 2 ↔
      ser g ∈ RingHom.ker ((WPres.free O wt).origin (freeOrigin O wt)) ^ 2 := fun g => by
    show g ∈ RingHom.ker ((WPres.free O wt).originA (freeOrigin O wt)) ^ 2 ↔ _
    rw [← hk]
    rfl
  constructor
  · rintro ⟨c, hc, hf⟩
    have h2 := order_of_mem_sq _ (fun g hg => by rw [← ho]; exact hg) _ ((hiff _).1 hf)
    have h3 : ∀ m : σ →₀ ℕ, m.degree < 2 → coeff m (ser f) = 0 := fun m hm => by
      have h4 : coeff m (c • ser f) = 0 :=
        coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hm) h2)
      rw [map_smul, smul_eq_mul] at h4
      exact (mul_eq_zero.1 h4).resolve_left hc
    exact ⟨h3 0 (by simp), fun i => h3 _ (by simp)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul, hiff]
    refine mem_sq_of_coeff _ (fun i => ?_) _ (fun m hm => ?_)
    · rw [RingHom.mem_ker, ho]; simp
    · rcases low_degree m hm with rfl | ⟨i, rfl⟩
      · exact h0
      · exact h1 i
end

