module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0061

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonGr
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
open LaurentPolynomial

private theorem exists_coact {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] :
    ∃ φ : R →+* R[T;T⁻¹], ∀ (j : ℤ) (x : R), x ∈ 𝒜 j ↔ φ x = C x * T j := by
  let t : Multiplicative ℤ →* (R[T;T⁻¹])ˣ := (AddMonoidAlgebra.of R ℤ).toHomUnits
  let φ : R →ₐ[O] R[T;T⁻¹] := act 𝒜 t (IsScalarTower.toAlgHom O R R[T;T⁻¹])
  have h1 : ∀ j x, x ∈ 𝒜 j → φ x = C x * T j := fun j x hx => by
    rw [mul_comm]
    exact act_of_mem 𝒜 t _ hx
  have h2 : ∀ x j, (φ x).coeff j = (DirectSum.decompose 𝒜 x j : R) := by
    intro x j
    induction x using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous i m =>
      rw [h1 i m m.2, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
      by_cases hij : i = j
      · subst hij
        rw [DirectSum.decompose_of_mem_same 𝒜 m.2, Finsupp.single_eq_same]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 m.2 hij, Finsupp.single_eq_of_ne' hij]
    | add a b ha hb => simp [ha, hb]
  refine ⟨φ, fun j x => ⟨h1 j x, fun hx => ?_⟩⟩
  have h3 := h2 x j
  have hx' : φ x = C x * T j := hx
  rw [hx', ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h3
  rw [h3]
  exact Subtype.property _

private theorem eig_unique {S n : Type} [CommRing S] [Fintype n] [DecidableEq n]
    (X h g h' : Matrix n n S) (l l' : n → S) (hg : h * g = 1) (gh : g * h = 1)
    (e : X * h = h * diagonal l) (e' : X * h' = h' * diagonal l')
    (o : ∀ a, h a a = 1) (o' : ∀ a, h' a a = 1) (u : ∀ a b, a ≠ b → IsUnit (l a - l' b)) : h' = h := by
  have e1 : g * X = diagonal l * g := by
    calc g * X = g * (X * h) * g := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, Matrix.mul_one]
      _ = _ := by rw [e, ← Matrix.mul_assoc, gh, Matrix.one_mul]
  have e2 : diagonal l * (g * h') = (g * h') * diagonal l' := by
    rw [← Matrix.mul_assoc, ← e1, Matrix.mul_assoc, e', Matrix.mul_assoc]
  have e3 : (g * h').IsDiag := by
    intro a b hab
    have := congrFun (congrFun e2 a) b
    rw [diagonal_mul, mul_diagonal] at this
    exact (u a b hab).mul_right_eq_zero.1 (by rw [sub_mul, this]; ring)
  have e4 : h' = h * diagonal (diag (g * h')) := by
    rw [e3.diagonal_diag, ← Matrix.mul_assoc, hg, Matrix.one_mul]
  have e5 : diag (g * h') = fun _ => 1 := by
    funext a
    have := congrFun (congrFun e4 a) a
    rw [mul_diagonal, o, o', one_mul] at this
    exact this.symm
  rw [e4, e5, diagonal_one, Matrix.mul_one]

end

open LaurentPolynomial in
theorem UpperTheory.V.UnitaryThreeInertia.canon_graded :
    ∀ {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Finite R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → GrMat 𝒜 X → Canon X h → GrMat 𝒜 h.val ∧ GrMat 𝒜 (h⁻¹).val := by
  intro O R _ _ _ _ _ _ 𝒜 _ X h hu hX hc
  obtain ⟨φ, hφ⟩ := exists_coact 𝒜
  have hnil : ∀ x ∈ maximalIdeal R, IsNilpotent x := by
    intro x hx
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact this
  set l : Fin 3 → R := diag ((h⁻¹).val * X * h.val) with hl
  have e : X * h.val = h.val * diagonal l := by
    rw [hl, hc.diag.diagonal_diag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hlX : ∀ a, IsNilpotent (l a - X a a) := by
    intro a
    apply hnil
    have e1 : X * (h.val - 1) = h.val * diagonal l - X := by rw [Matrix.mul_sub, e, Matrix.mul_one]
    have e2 := congrFun (congrFun e1 a) a
    rw [Matrix.sub_apply, mul_diagonal, hc.one, one_mul] at e2
    rw [← e2, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hc.hat c a)
  let D : Matrix (Fin 3) (Fin 3) R[T;T⁻¹] := diagonal fun a => T (wt1 a)
  let D' : Matrix (Fin 3) (Fin 3) R[T;T⁻¹] := diagonal fun a => T (-wt1 a)
  have DD : D * D' = 1 := by
    simp only [D, D', diagonal_mul_diagonal, ← T_add, add_neg_cancel, T_zero, diagonal_one]
  have DD' : D' * D = 1 := by
    simp only [D, D', diagonal_mul_diagonal, ← T_add, neg_add_cancel, T_zero, diagonal_one]
  have ent : ∀ (M : Matrix (Fin 3) (Fin 3) R[T;T⁻¹]) a b, (D * M * D') a b = M a b * T (wt a b) := by
    intro M a b
    simp only [D, D', mul_diagonal, diagonal_mul, wt, T_sub]
    ring
  have key : ∀ M : Matrix (Fin 3) (Fin 3) R, GrMat 𝒜 M ↔ M.map φ = D * M.map C * D' := by
    intro M
    constructor
    · intro hM
      ext1 a b
      rw [ent]
      exact (hφ _ _).1 (hM a b)
    · intro hM a b
      have := congrFun (congrFun hM a) b
      rw [ent] at this
      exact (hφ _ _).2 this
  have inv1 : ∀ f : R →+* R[T;T⁻¹], h.val.map f * (h⁻¹).val.map f = 1 := fun f => by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one f (map_zero f) (map_one f)]
  have inv2 : ∀ f : R →+* R[T;T⁻¹], (h⁻¹).val.map f * h.val.map f = 1 := fun f => by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one f (map_zero f) (map_one f)]
  have emap : ∀ f : R →+* R[T;T⁻¹], X.map f * h.val.map f = h.val.map f * diagonal fun a => f (l a) := fun f => by
    rw [← Matrix.map_mul, e, Matrix.map_mul, diagonal_map (map_zero f)]
  have can : ∀ M N : Matrix (Fin 3) (Fin 3) R[T;T⁻¹], (D * M * D') * (D * N * D') = D * (M * N) * D' := by
    intro M N
    calc _ = D * M * (D' * D) * N * D' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [DD', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have main : D * h.val.map C * D' = h.val.map φ := by
    refine eig_unique (X.map φ) (h.val.map φ) ((h⁻¹).val.map φ) _ (fun a => φ (l a)) (fun a => C (l a))
      (inv1 φ) (inv2 φ) (emap φ) ?_ (fun a => by simp [hc.one]) (fun a => by rw [ent]; simp [hc.one, wt]) ?_
    · rw [(key X).1 hX, can, emap C]
      have hcomm : (diagonal fun a => C (l a)) * D' = D' * diagonal fun a => C (l a) := by
        simp only [D', diagonal_mul_diagonal, mul_comm]
      simp only [Matrix.mul_assoc]
      rw [hcomm]
    · intro a b hab
      have hXa : φ (X a a) = C (X a a) := by
        have := (hφ _ _).1 (hX a a)
        simpa [wt] using this
      have h1 : IsNilpotent (φ (l a - X a a) - C (l b - X b b)) :=
        (Commute.all _ _).isNilpotent_sub ((hlX a).map φ) ((hlX b).map C)
      have h2 := h1.isUnit_add_right_of_commute ((hu a b hab).map C) (Commute.all _ _)
      convert h2 using 1
      simp only [map_sub, hXa]
      ring
  refine ⟨(key _).2 main.symm, (key _).2 ?_⟩
  have h3 : h.val.map φ * (D * (h⁻¹).val.map C * D') = 1 := by
    rw [← main, can, inv1, Matrix.mul_one, DD]
  calc (h⁻¹).val.map φ = (h⁻¹).val.map φ * (h.val.map φ * (D * (h⁻¹).val.map C * D')) := by
        rw [h3, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, inv2, Matrix.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonMap
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem tor_conj_apply {R : Type} [CommRing R] (t : Rˣ) (Y : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    ((tor R t).val * Y * (tor R t⁻¹).val) a b =
      ((t ^ wt1 a : Rˣ) : R) * Y a b * ((t⁻¹ ^ wt1 b : Rˣ) : R) := by
  rw [tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem tor_mul_inv {R : Type} [CommRing R] (t : Rˣ) :
    (tor R t⁻¹).val * (tor R t).val = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

private theorem tor_mul_inv' {R : Type} [CommRing R] (t : Rˣ) :
    (tor R t).val * (tor R t⁻¹).val = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem UpperTheory.V.UnitaryThreeInertia.canon_map :
    (∀ {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R), Canon X h → Canon (X.map φ) (GeneralLinearGroup.map φ h)) ∧
    ∀ {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R) (t : Rˣ), Canon X h → Canon ((tor R t).val * X * (tor R t⁻¹).val) (tor R t * h * tor R t⁻¹) := by
  refine ⟨fun {R R'} _ _ _ _ φ _ X h H => ⟨fun a b => ?_, fun a => ?_, ?_⟩,
    fun {R} _ _ X h t H => ⟨fun a b => ?_, fun a => ?_, ?_⟩⟩
  · have e : ((GeneralLinearGroup.map φ h : GL (Fin 3) R').val - 1) a b = φ ((h.val - 1) a b) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · rw [map_one]; rfl
      · rw [map_zero]; rfl
    rw [e]
    exact map_nonunit φ _ (H.hat a b)
  · show φ (h.val a a) = 1
    rw [H.one, map_one]
  · have e : ((GeneralLinearGroup.map φ h)⁻¹ : GL (Fin 3) R').val * X.map φ * (GeneralLinearGroup.map φ h).val =
        ((h⁻¹ : GL (Fin 3) R).val * X * h.val).map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, ← map_inv]; rfl
    rw [e]
    exact H.diag.map (map_zero φ)
  · have e : (tor R t * h * tor R t⁻¹).val - 1 = (tor R t).val * (h.val - 1) * (tor R t⁻¹).val := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, tor_mul_inv', Units.val_mul, Units.val_mul]
    rw [e, tor_conj_apply]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (H.hat a b))
  · rw [Units.val_mul, Units.val_mul, tor_conj_apply, H.one, mul_one, ← Units.val_mul, ← mul_zpow,
      mul_inv_cancel, _root_.one_zpow, Units.val_one]
  · have e : ((tor R t * h * tor R t⁻¹)⁻¹ : GL (Fin 3) R).val * ((tor R t).val * X * (tor R t⁻¹).val) *
        (tor R t * h * tor R t⁻¹).val = (tor R t).val * ((h⁻¹ : GL (Fin 3) R).val * X * h.val) * (tor R t⁻¹).val := by
      have hc : ∀ Y : Matrix (Fin 3) (Fin 3) R, (tor R t⁻¹).val * ((tor R t).val * Y) = Y := fun Y => by
        rw [← Matrix.mul_assoc, tor_mul_inv, Matrix.one_mul]
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, ← map_inv, ← map_inv, inv_inv]
      simp only [Units.val_mul, Matrix.mul_assoc, hc]
    rw [e]
    intro a b hab
    rw [tor_conj_apply, H.diag hab, mul_zero, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonUniq
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem canon_eig {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (h : GL (Fin 3) R) (hc : Canon X h) :
    ∃ d : Fin 3 → R, ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h = diagonal d ∧
      ∀ a, d a - X a a ∈ maximalIdeal R := by
  let φ := residue R
  have h0 : φ.mapMatrix (h.val - 1) = 0 := by
    ext a b
    exact (residue_eq_zero_iff _).2 (hc.hat a b)
  have hh : φ.mapMatrix h.val = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0
  have hhi : φ.mapMatrix h⁻¹.val = 1 := by
    have e : φ.mapMatrix h⁻¹.val * φ.mapMatrix h.val = 1 := by
      rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
    rwa [hh, mul_one] at e
  refine ⟨fun a => (h⁻¹.val * X * h.val) a a, hc.diag.diagonal_diag.symm, ?_⟩
  intro a
  rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  have e : φ.mapMatrix (h⁻¹.val * X * h.val) = φ.mapMatrix X := by
    rw [map_mul, map_mul, hh, hhi, one_mul, mul_one]
  exact congrFun (congrFun e a) a

theorem UpperTheory.V.UnitaryThreeInertia.canon_unique :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] (X : Matrix (Fin 3) (Fin 3) R) (h h' : GL (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → Canon X h → Canon X h' → h = h' := by
  intro R _ _ X h h' hX hc hc'
  obtain ⟨d, hd, hdX⟩ := canon_eig X h hc
  obtain ⟨d', hd', hd'X⟩ := canon_eig X h' hc'
  let g : GL (Fin 3) R := h⁻¹ * h'
  have key : diagonal d * g.val = g.val * diagonal d' := by
    rw [← hd, ← hd']
    simp only [g, Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  have hg : ∀ a b, a ≠ b → g.val a b = 0 := by
    intro a b hab
    have e := congrFun (congrFun key a) b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    have hu : IsUnit (d a - d' b) := by
      by_contra hn
      have hm : d a - d' b ∈ maximalIdeal R := hn
      have hm2 : X a a - X b b ∈ maximalIdeal R := by
        have e2 : X a a - X b b = (d a - d' b) - (d a - X a a) + (d' b - X b b) := by ring
        rw [e2]
        exact add_mem (sub_mem hm (hdX a)) (hd'X b)
      exact hm2 (hX a b hab)
    have e3 : g.val a b * (d a - d' b) = 0 := by
      rw [mul_sub, mul_comm (g.val a b) (d a), e, sub_self]
    exact hu.mul_left_eq_zero.1 e3
  have hh' : h'.val = h.val * g.val := by
    simp only [g, Units.val_mul, Units.mul_inv_cancel_left]
  have g1 : g.val = 1 := by
    ext a b
    by_cases hab : a = b
    · subst hab
      rw [Matrix.one_apply_eq]
      have e := congrFun (congrFun hh' a) a
      rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hg c a hc, mul_zero])
        (by simp), hc'.one a, hc.one a, one_mul] at e
      exact e.symm
    · rw [Matrix.one_apply_ne hab, hg a b hab]
  have g1' : g = 1 := Units.ext g1
  exact inv_mul_eq_one.1 g1'
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CardDualResidueFieldEqCardOfMaximalIdealSmulEqZe
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

theorem UpperTheory.card_dual_residueField_eq_card_of_maximalIdeal_smul_eq_zero :
    ∀ {O N : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [AddCommGroup N] [Module O N] [Finite N], (∀ a ∈ maximalIdeal O, ∀ x : N, a • x = 0) → Nat.card (N →ₗ[O] ResidueField O) = Nat.card N := by
  intro O N _ _ _ _ _ _ h
  classical
  have hM : Module.IsTorsionBySet O N (maximalIdeal O) := fun x a => h a a.2 x
  letI : Module (ResidueField O) N := hM.module
  haveI : IsScalarTower O (ResidueField O) N := hM.isScalarTower
  have e := LinearMap.extendScalarsOfSurjectiveEquiv (R := O) (S := ResidueField O) (M := N)
    (N := ResidueField O) IsLocalRing.residue_surjective
  rw [Nat.card_congr e.toEquiv]
  let b := Module.Free.chooseBasis (ResidueField O) N
  exact (Nat.card_congr b.toDualEquiv.toEquiv).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CondConj
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem entIn_sub_iff {C : Type} [CommRing C] (I : Ideal C) (X Y : Matrix (Fin 3) (Fin 3) C) :
    EntIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext a b
    exact Ideal.Quotient.eq.2 (h a b)
  · intro h a b
    exact Ideal.Quotient.eq.1 (congrFun (congrFun h a) b)

private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  unfold CongOne
  rw [entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro e
    exact Units.ext e
  · intro e
    exact congrArg Units.val e

private theorem conjBy_app {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

private theorem conjBy_comp {C D E : Type} [CommRing C] [Group D] [Group E] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C))
    (f : E →* D) : (conjBy h r).comp f = conjBy h (r.comp f) := rfl

private theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) :
    conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r := by
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy_app, map_inv, map_mul]
  group

private theorem map_conjBy {C D : Type} [CommRing C] [Group D] (I : Ideal C) (h : GL (Fin 3) C)
    (hh : CongOne I h) (r : D →* GG (m := 3) (R := C)) (g : D) :
    GG.map (Ideal.Quotient.mk I) (conjBy h r g) = GG.map (Ideal.Quotient.mk I) (r g) := by
  have e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1 := by
    unfold GG.map
    rw [SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e,
    one_mul, inv_one, mul_one]

theorem UpperTheory.V.UnitaryThreeInertia.cond_conj :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] (h : GL (Fin 3) R), InHat h →
      (∀ v (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (conjBy h r)) ∧
        ∀ r : Γ →* GG (m := 3) (R := R), F.Cond r → F.Cond (conjBy h r) := by
  intro O _ _ G Γ ι _ _ F R _ _ _ h hh
  have hmul : ∀ h' : GL (Fin 3) R, InHat h' → InHat (h * h') := fun h' hh' => by
    refine (congOne_iff _ _).2 ?_
    rw [map_mul, (congOne_iff _ _).1 hh, (congOne_iff _ _).1 hh', mul_one]
  have hloc : ∀ v (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (conjBy h r) := by
    intro v r ⟨ht, hd, hu⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e s hs => ?_⟩
    · obtain ⟨h', h1, h2, h3⟩ := ht e
      refine ⟨h * h', hmul h' h1, ?_, ?_⟩
      · rw [conjBy_conjBy]; exact h2
      · rw [conjBy_conjBy]; exact h3
    · obtain ⟨h', h1, ⟨h2, h3⟩, h4⟩ := hd e
      refine ⟨h * h', hmul h' h1, ⟨?_, ?_⟩, ?_⟩
      · rw [conjBy_conjBy]; exact h2
      · rw [conjBy_conjBy]; exact h3
      · rw [conjBy_conjBy]; exact h4
    · rw [conjBy_app, hu e s hs, mul_one, mul_inv_cancel]
  refine ⟨hloc, fun r hr => ⟨⟨fun g => ?_, fun g => ?_⟩, fun v => ?_⟩⟩
  · have e := congrArg SemidirectProduct.right (map_conjBy _ h hh r g)
    rw [GG.map_right, GG.map_right] at e
    exact e.trans (hr.mult g)
  · have e := congrArg GG.mat (map_conjBy _ h hh r g)
    rw [GG.map_mat, GG.map_mat] at e
    rw [entIn_sub_iff, e, ← entIn_sub_iff]
    exact hr.red g
  · rw [conjBy_comp]
    exact hloc v _ (hr.loc v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsSmallExtensionFactorizationOfFunctional
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem isCO_of_surj {O : Type} [CommRing O] [IsLocalRing O] {R S : Type} [CommRing R] [Algebra O R]
    [IsCO O R] [Finite R] [CommRing S] [Algebra O S] [Nontrivial S] (f : R →ₐ[O] S)
    (hf : Function.Surjective f) :
    ∃ _ : IsCO O S, ∀ x : R, f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
  haveI : IsLocalRing S := IsLocalRing.of_surjective' (f : R →+* S) hf
  haveI : Finite S := Finite.of_surjective f hf
  haveI hl : IsLocalHom (f : R →+* S) := IsLocalHom.of_surjective (f : R →+* S) hf
  have hm : ∀ x : R, f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := fun x =>
    ⟨fun h hu => h (hu.map f), fun h hu => h (hl.map_nonunit x hu)⟩
  haveI : IsArtinianRing S := inferInstance
  refine ⟨{ complete := inferInstance, isLocalHom := ⟨fun a ha => ?_⟩, res_surj := fun y => ?_ }, hm⟩
  · rw [← f.commutes] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap O R) a (hl.map_nonunit _ ha)
  · obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨a, ?_⟩
    rw [← f.commutes, ← map_sub]
    exact (hm _).2 ha

theorem UpperTheory.exists_small_extension_factorization_of_functional :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R'), maximalIdeal R * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal R → ∀ φ : RingHom.ker p →ₗ[O] ResidueField O, φ ≠ 0 →
     ∃ (R'' : Type) (_ : CommRing R'') (_ : Algebra O R'') (_ : IsCO O R'') (p₁ : R →ₐ[O] R'') (q : R'' →ₐ[O] R') (ε : ResidueField O →ₗ[O] R''), Function.Surjective p₁ ∧ q.comp p₁ = p ∧ ¬ Function.Injective q ∧ (∀ x : RingHom.ker p, p₁ x = ε (φ x)) ∧ (∀ y, q (ε y) = 0) ∧ (∀ y, ε y ∈ maximalIdeal R'') ∧ ∀ x ∈ maximalIdeal R'', ∀ y, x * ε y = 0 := by
  intro O _ _ R R' _ _ _ _ _ _ p hmul hle φ hφ
  have hz : ∀ m ∈ maximalIdeal R, ∀ x ∈ RingHom.ker p, m * x = 0 := fun m hm x hx => by
    have := Ideal.mul_mem_mul hm hx
    rwa [hmul, Ideal.mem_bot] at this
  let J : Ideal R :=
    { carrier := {x | ∃ h : x ∈ RingHom.ker p, φ ⟨x, h⟩ = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, ?_⟩
        have : (⟨a + b, add_mem ha hb⟩ : RingHom.ker p) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, map_add (f := _), ha', hb', add_zero]
      zero_mem' := ⟨zero_mem _, map_zero φ⟩
      smul_mem' := by
        rintro r x ⟨hx, hx'⟩
        refine ⟨Ideal.mul_mem_left _ r hx, ?_⟩
        obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) r
        have : (⟨r • x, Ideal.mul_mem_left _ r hx⟩ : RingHom.ker p) = a • ⟨x, hx⟩ := by
          apply Subtype.ext
          have h := hz _ ha x hx
          rw [sub_mul, sub_eq_zero] at h
          show r * x = a • x
          rw [h, Algebra.smul_def]
        rw [this, map_smul, hx', smul_zero] }
  have hJ : ∀ x : RingHom.ker p, (x : R) ∈ J ↔ φ x = 0 := fun x =>
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩
  have hJp : ∀ x ∈ J, p x = 0 := fun x ⟨h, _⟩ => h
  obtain ⟨x0, hx0⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨a, ha⟩ := residue_surjective (y * (φ x0)⁻¹)
    refine ⟨a • x0, ?_⟩
    rw [map_smul, Algebra.smul_def, ResidueField.algebraMap_eq, ha, inv_mul_cancel_right₀ hx0]
  have hJtop : J ≠ ⊤ := fun h => hx0 ((hJ x0).1 (h ▸ Submodule.mem_top))
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have hp1 : Function.Surjective (Ideal.Quotient.mkₐ O J) := Ideal.Quotient.mkₐ_surjective O J
  obtain ⟨inst, hm⟩ := isCO_of_surj (Ideal.Quotient.mkₐ O J) hp1
  let ψ : RingHom.ker p →ₗ[O] R ⧸ J :=
    (Ideal.Quotient.mkₐ O J).toLinearMap ∘ₗ ((RingHom.ker p).subtype.restrictScalars O)
  have hψ : ∀ x : RingHom.ker p, ψ x = Ideal.Quotient.mkₐ O J x := fun _ => rfl
  have hker : LinearMap.ker φ ≤ LinearMap.ker ψ := fun x hx =>
    Ideal.Quotient.eq_zero_iff_mem.2 ((hJ x).2 hx)
  let ε : ResidueField O →ₗ[O] R ⧸ J :=
    (LinearMap.ker φ).liftQ ψ hker ∘ₗ (φ.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hε : ∀ x : RingHom.ker p, ε (φ x) = Ideal.Quotient.mkₐ O J x := fun x => by
    have : (φ.quotKerEquivOfSurjective hsurj).symm (φ x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker φ).liftQ ψ hker ((φ.quotKerEquivOfSurjective hsurj).symm (φ x)) = _
    rw [this, Submodule.liftQ_apply, hψ]
  have hq : ∀ x : R, Ideal.Quotient.liftₐ J p hJp (Ideal.Quotient.mkₐ O J x) = p x := fun _ => rfl
  refine ⟨R ⧸ J, inferInstance, inferInstance, inst, Ideal.Quotient.mkₐ O J, Ideal.Quotient.liftₐ J p hJp, ε,
    hp1, AlgHom.ext hq, fun hinj => ?_, fun x => (hε x).symm, fun y => ?_, fun y => ?_, fun x hx y => ?_⟩
  · have h : Ideal.Quotient.mkₐ O J (x0 : R) = 0 := hinj (by rw [hq, map_zero]; exact x0.2)
    exact hx0 ((hJ x0).1 (Ideal.Quotient.eq_zero_iff_mem.1 h))
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [hε, hq]; exact x.2
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [hε]; exact (hm _).2 (hle x.2)
  · obtain ⟨z, rfl⟩ := hsurj y
    obtain ⟨w, rfl⟩ := hp1 x
    rw [hε, ← map_mul, hz w ((hm w).1 hx) _ z.2, map_zero]
end

