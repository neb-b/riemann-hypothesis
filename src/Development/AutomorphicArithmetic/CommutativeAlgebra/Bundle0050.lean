module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointsNonemptyUnitaryGaussian
public import Development.AutomorphicArithmetic.RealSpanData.RealData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSumBaseChangeOfCommuteBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

theorem UpperTheory.exists_sum_baseChange_of_commute_baseChange :
    ∀ (κ V V' R : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup V'] [Module ℚ V'] [FiniteDimensional ℚ V] [FiniteDimensional ℚ V'] [CommRing R] [Algebra ℚ R] (a : κ → Module.End ℚ V) (a' : κ → Module.End ℚ V') (T : (R ⊗[ℚ] V') →ₗ[R] (R ⊗[ℚ] V)), (∀ i, T ∘ₗ (a' i).baseChange R = (a i).baseChange R ∘ₗ T) → ∃ (k : ℕ) (r : Fin k → R) (h : Fin k → V' →ₗ[ℚ] V), (∀ l i, h l ∘ₗ a' i = a i ∘ₗ h l) ∧ T = ∑ l, r l • (h l).baseChange R := by
  intro κ V V' R _ _ _ _ _ _ _ _ a a' T hT
  classical
  set bV' := Module.finBasis ℚ V'
  set bV := Module.finBasis ℚ V
  set B := Algebra.TensorProduct.basis R bV
  let M : Fin (Module.finrank ℚ V') × Fin (Module.finrank ℚ V) → R :=
    fun p => B.repr (T (1 ⊗ₜ bV' p.1)) p.2
  let S : Submodule ℚ R := Submodule.span ℚ (Set.range M)
  haveI : FiniteDimensional ℚ S := FiniteDimensional.span_of_finite ℚ (Set.finite_range M)
  let bS := Module.finBasis ℚ S
  let r : Fin (Module.finrank ℚ S) → R := fun l => (bS l : R)
  have hr : LinearIndependent ℚ r := bS.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  let c : Fin (Module.finrank ℚ S) → Fin (Module.finrank ℚ V') × Fin (Module.finrank ℚ V) → ℚ :=
    fun l p => bS.repr ⟨M p, Submodule.subset_span ⟨p, rfl⟩⟩ l
  have hM : ∀ p, M p = ∑ l, c l p • r l := by
    intro p
    have e := congrArg Subtype.val (bS.sum_repr ⟨M p, Submodule.subset_span ⟨p, rfl⟩⟩)
    rw [Submodule.coe_sum] at e
    exact e.symm
  let h : Fin (Module.finrank ℚ S) → V' →ₗ[ℚ] V :=
    fun l => bV'.constr ℚ (fun j => ∑ i, c l (j, i) • bV i)
  have key : ∀ w : Fin (Module.finrank ℚ S) → V, ∑ l, r l ⊗ₜ[ℚ] w l = 0 → ∀ l, w l = 0 := by
    intro w hw l
    apply bV.ext_elem
    intro i
    have h1 := congrArg (fun x => B.repr x i) hw
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply', B,
      Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    have h2 : ∑ l, bV.repr (w l) i • r l = 0 := by
      rw [← h1]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have h3 := Fintype.linearIndependent_iff.1 hr (fun l => bV.repr (w l) i) h2 l
    simpa using h3
  have hT1 : ∀ x : V', T (1 ⊗ₜ x) = ∑ l, r l ⊗ₜ[ℚ] h l x := by
    have e : (T.restrictScalars ℚ).comp (TensorProduct.mk ℚ R V' 1) =
        ∑ l, (TensorProduct.mk ℚ R V (r l)).comp (h l) := by
      refine bV'.ext fun j => ?_
      have hs : T (1 ⊗ₜ bV' j) = ∑ i, M (j, i) ⊗ₜ[ℚ] bV i := by
        conv_lhs => rw [← B.sum_repr (T (1 ⊗ₜ bV' j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Algebra.TensorProduct.basis_repr_symm_apply' bV _ i
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
        LinearMap.sum_apply, h, Module.Basis.constr_basis]
      rw [hs]
      simp only [hM, TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
      exact Finset.sum_comm
    intro x
    have e2 := LinearMap.congr_fun e x
    simpa using e2
  refine ⟨Module.finrank ℚ S, r, h, ?_, ?_⟩
  · intro l i
    have hw : ∀ v : V', ∑ l, r l ⊗ₜ[ℚ] (h l (a' i v) - a i (h l v)) = 0 := by
      intro v
      have e := LinearMap.congr_fun (hT i) (1 ⊗ₜ v)
      simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at e
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hT1, hT1, map_sum] at e
      simp only [LinearMap.baseChange_tmul] at e
      simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib, e, sub_self]
    ext v
    have h4 := key _ (hw v) l
    simpa [sub_eq_zero] using h4
  · ext m
    simp only [TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearMap.restrictScalars_apply]
    rw [hT1]
    simp [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.baseChange_tmul,
      TensorProduct.smul_tmul']
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUnitaryUnitHermitianFormOfCmLattice
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem exists_den {Λ : Type} [AddCommGroup Λ] (t : ℚ ⊗[ℤ] Λ) :
    ∃ (n : ℤ) (z : Λ), n ≠ 0 ∧ n • t = (1 : ℚ) ⊗ₜ[ℤ] z := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q z =>
    refine ⟨(q.den : ℤ), q.num • z, by exact_mod_cast q.den_nz, ?_⟩
    have h : ((q.den : ℤ)) • q = q.num • (1 : ℚ) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, Int.cast_natCast, _root_.mul_one]
      exact Rat.den_mul_eq_num q
    rw [TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨n, z, hn, h⟩ := ha
    obtain ⟨m, w, hm, h'⟩ := hb
    refine ⟨n * m, m • z + n • w, mul_ne_zero hn hm, ?_⟩
    rw [smul_add, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← h, ← h',
      smul_smul, smul_smul, mul_comm m n]

private theorem sep_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) (a : ℚ ⊗[ℤ] Λ) (h : ∀ w, B.baseChange ℚ a w = 0) : a = 0 := by
  obtain ⟨n, z, hn, e⟩ := exists_den a
  have hz : z = 0 := by
    apply hB
    intro w
    have h2 : B.baseChange ℚ ((1 : ℚ) ⊗ₜ[ℤ] z) ((1 : ℚ) ⊗ₜ[ℤ] w) = 0 := by
      rw [← e, map_zsmul, LinearMap.smul_apply, h, smul_zero]
    simpa [LinearMap.BilinForm.baseChange_tmul] using h2
  rw [hz, TensorProduct.tmul_zero] at e
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  rw [← Int.cast_smul_eq_zsmul ℚ] at e
  exact (smul_eq_zero.1 e).resolve_left hn'

private theorem adj_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (f g : Λ →ₗ[ℤ] Λ)
    (h : ∀ x y, B (f x) y = B x (g y)) (u w : ℚ ⊗[ℤ] Λ) :
    B.baseChange ℚ (f.baseChange ℚ u) w = B.baseChange ℚ u (g.baseChange ℚ w) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul r y => simp [LinearMap.BilinForm.baseChange_tmul, h]

private theorem anti_bc {Λ : Type} [AddCommGroup Λ] (B : LinearMap.BilinForm ℤ Λ) (h : ∀ x, B x x = 0)
    (u w : ℚ ⊗[ℤ] Λ) : B.baseChange ℚ u w = - B.baseChange ℚ w u := by
  have anti : ∀ x y, B x y = - B y x := fun x y => by
    have := h (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, h, zero_add, add_zero] at this
    linarith
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
  | tmul q x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]; ring
    | tmul r y =>
      simp only [LinearMap.BilinForm.baseChange_tmul]
      rw [anti x y]
      rw [mul_comm q r, neg_smul]

private theorem exists_rep {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (E F : LinearMap.BilinForm ℚ V) (hE : ∀ a, (∀ w, E a w = 0) → a = 0) :
    ∃ b : Module.End ℚ V, ∀ u w, F u w = 2 * E (b u) w := by
  have inj : Function.Injective (E : V →ₗ[ℚ] Module.Dual ℚ V) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact hE a fun w => by rw [ha]; rfl
  let Φ : V ≃ₗ[ℚ] Module.Dual ℚ V :=
    LinearMap.linearEquivOfInjective (E : V →ₗ[ℚ] Module.Dual ℚ V) inj (Subspace.dual_finrank_eq).symm
  refine ⟨(1 / 2 : ℚ) • (Φ.symm.toLinearMap ∘ₗ (F : V →ₗ[ℚ] Module.Dual ℚ V)), fun u w => ?_⟩
  have h : E (Φ.symm (F u)) = F u := Φ.apply_symm_apply (F u)
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul, h, smul_eq_mul]
  ring

theorem UpperTheory.exists_unitary_unit_hermitian_form_of_cm_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (Y : PLat D.O D.inv) (j : (ℚ ⊗[ℤ] Y.La) ≃ₗ[ℚ] VQ D), (∀ (c : D.O) (u : ℚ ⊗[ℤ] Y.La), j ((DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ u) = actQ D c (j u)) → ∃ β : G.Cˣ, sh G β = β ∧ ∀ u w : ℚ ⊗[ℤ] Y.La, Y.EF.baseChange ℚ u w = 2 * D.EF.baseChange ℚ (L.rep ((β⁻¹ : G.Cˣ) : G.C) (j u)) (j w) := by
  intro p _ D G L Y j hj
  haveI := D.finLa
  set E := D.EF.baseChange ℚ with hEdef
  have sepE : ∀ a, (∀ w, E a w = 0) → a = 0 := fun a h =>
    sep_bc D.EF (fun x hx => D.nondeg (by rw [map_zero]; ext y; simpa using hx y)) a h
  have sepY : ∀ a, (∀ w, Y.EF.baseChange ℚ a w = 0) → a = 0 := fun a h => sep_bc Y.EF Y.nondeg a h
  have eqE : ∀ a a', (∀ w, E a w = E a' w) → a = a' := fun a a' h => by
    rw [← sub_eq_zero]
    exact sepE _ fun w => by rw [map_sub, LinearMap.sub_apply, h, sub_self]
  let F : LinearMap.BilinForm ℚ (VQ D) :=
    ((Y.EF.baseChange ℚ).compl₁₂ j.symm.toLinearMap j.symm.toLinearMap)
  have hF : ∀ u w, F u w = Y.EF.baseChange ℚ (j.symm u) (j.symm w) := fun u w => rfl
  obtain ⟨b, hb⟩ := exists_rep E F sepE
  have hinj : Function.Injective b := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro u hu
    have : j.symm u = 0 := sepY _ fun w => by
      have h := hb u (j w)
      rw [hu, map_zero, LinearMap.zero_apply, MulZeroClass.mul_zero, hF, j.symm_apply_apply] at h
      exact h
    simpa using this
  have comm : ∀ c : D.O, b * actQ D c = actQ D c * b := by
    intro c
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    have hc : j.symm (actQ D c u) = (DistribSMul.toLinearMap ℤ Y.La c).baseChange ℚ (j.symm u) := by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have hc' : ∀ w, j.symm (actQ D (D.inv c) w) = (DistribSMul.toLinearMap ℤ Y.La (D.inv c)).baseChange ℚ (j.symm w) := fun w => by
      rw [LinearEquiv.symm_apply_eq, hj, j.apply_symm_apply]
    have h1 : F (actQ D c u) w = F u (actQ D (D.inv c) w) := by
      rw [hF, hF, hc, hc']
      exact adj_bc Y.EF _ _ (fun x y => Y.adj c x y) _ _
    have h2 : E (actQ D c (b u)) w = E (b u) (actQ D (D.inv c) w) :=
      adj_bc D.EF _ _ (fun x y => D.adj c x y) _ _
    have h3 := hb (actQ D c u) w
    have h4 := hb u (actQ D (D.inv c) w)
    simp only [Module.End.mul_apply]
    rw [h2]
    linarith
  have hsym : ∀ u w, E (b u) w = E u (b w) := by
    intro u w
    have h1 := hb u w
    have h2 := hb w u
    have h3 : F u w = - F w u := by
      rw [hF, hF]
      exact anti_bc Y.EF Y.alt _ _
    have h4 : E (b w) u = - E u (b w) := anti_bc D.EF D.alt _ _
    linarith
  obtain ⟨b₀, hb₀⟩ : ∃ x : G.C, L.rep x = b := (L.rep_range b).2 comm
  let e : VQ D ≃ₗ[ℚ] VQ D := LinearEquiv.ofInjectiveEndo b hinj
  have he : ∀ u, b (e.symm u) = u := fun u => e.apply_symm_apply u
  have he' : ∀ u, e.symm (b u) = u := fun u => e.symm_apply_apply u
  have comm' : ∀ c : D.O, (e.symm.toLinearMap : Module.End ℚ (VQ D)) * actQ D c = actQ D c * e.symm.toLinearMap := by
    intro c
    refine LinearMap.ext fun u => hinj ?_
    have h := LinearMap.congr_fun (comm c) (e.symm u)
    simp only [Module.End.mul_apply, LinearEquiv.coe_coe, he] at h ⊢
    exact h.symm
  obtain ⟨b₁, hb₁⟩ : ∃ x : G.C, L.rep x = e.symm.toLinearMap :=
    (L.rep_range e.symm.toLinearMap).2 comm'
  have h01 : b₀ * b₁ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he u
  have h10 : b₁ * b₀ = 1 := by
    apply L.rep_inj
    rw [map_mul, map_one, hb₀, hb₁]
    exact LinearMap.ext fun u => he' u
  have hadj : ∀ x v w, E (L.rep x v) w = E v (L.rep (sh G x) w) := L.adj
  have shsh : sh G (sh G b₀) = b₀ := G.star_star b₀
  have shmul : ∀ x y, sh G (x * y) = sh G y * sh G x := fun x y => by
    unfold sh
    rw [map_mul, MulOpposite.unop_mul]
  have shone : sh G 1 = 1 := by
    unfold sh
    rw [map_one, MulOpposite.unop_one]
  have hs : sh G b₀ = b₀ := by
    apply L.rep_inj
    refine LinearMap.ext fun u => eqE _ _ fun w => ?_
    rw [hadj, shsh, hb₀, hsym]
  have hs1 : sh G b₁ = b₁ := by
    have h : sh G b₁ * b₀ = 1 := by
      have h' := shmul b₀ b₁
      rw [h01, shone, hs] at h'
      exact h'.symm
    calc sh G b₁ = sh G b₁ * (b₀ * b₁) := by rw [h01, _root_.mul_one]
      _ = (sh G b₁ * b₀) * b₁ := (_root_.mul_assoc _ _ _).symm
      _ = b₁ := by rw [h, _root_.one_mul]
  refine ⟨⟨b₁, b₀, h10, h01⟩, hs1, fun u w => ?_⟩
  have h := hb (j u) (j w)
  rw [hF, j.symm_apply_apply, j.symm_apply_apply] at h
  rw [h]
  show _ = 2 * E (L.rep b₀ (j u)) (j w)
  rw [hb₀]
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HermitianCongruentAndPositiveEigenvectorOfSignat
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKCx GlobalTheory.PELU
attribute [local instance] Over.cartesianMonoidalCategory
open UpperTheory.ComplexUniformization

private theorem form_re_eq {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (H *ᵥ x)).re = ∑ i, hH.eigenvalues i *
      Complex.normSq ((star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hspec : H = U * diagonal (RCLike.ofReal ∘ hH.eigenvalues) * star U := by
    have h0 := hH.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at h0
  have hsy : star (star U *ᵥ x) = star x ᵥ* U := by
    rw [star_mulVec, ← star_eq_conjTranspose, star_star]
  have hL : star x ⬝ᵥ (H *ᵥ x) =
      star (star U *ᵥ x) ⬝ᵥ (diagonal (RCLike.ofReal ∘ hH.eigenvalues) *ᵥ (star U *ᵥ x)) := by
    rw [hsy, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, ← hspec]
  rw [hL, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mulVec_diagonal]
  simp only [Function.comp_apply, Pi.star_apply, RCLike.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  simp [Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem finrank_le_of_coord {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (p : Fin n → Prop)
    [Fintype {i // p i}] (W : Submodule ℂ (Fin n → ℂ)) (h : ∀ x ∈ W, (∀ i, p i → (U *ᵥ x) i = 0) → x = 0) :
    Module.finrank ℂ W ≤ Fintype.card {i // p i} := by
  let f : W →ₗ[ℂ] ({i // p i} → ℂ) :=
    { toFun := fun x i => (U *ᵥ (x : Fin n → ℂ)) i.1
      map_add' := fun x y => by
        ext i
        simp [mulVec_add]
      map_smul' := fun c x => by
        ext i
        simp [mulVec_smul] }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply Subtype.ext
    apply h x x.2
    intro i hi
    exact congrFun hx ⟨i, hi⟩
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi] at h1

private theorem sig_eq_finrank {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (A B : Submodule ℂ (Fin n → ℂ)) (hAB : Module.finrank ℂ A + Module.finrank ℂ B = n)
    (hA : ∀ x ∈ A, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re)
    (hB : ∀ x ∈ B, x ≠ 0 → (star x ⬝ᵥ (H *ᵥ x)).re < 0) :
    sigPosH hH = Module.finrank ℂ A := by
  set U : Matrix (Fin n) (Fin n) ℂ := star (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hA' : Module.finrank ℂ A ≤ Fintype.card {i // 0 < hH.eigenvalues i} := by
    apply finrank_le_of_coord U (fun i => 0 < hH.eigenvalues i) A
    intro x hx hz
    by_contra hne
    have h1 := hA x hx hne
    rw [form_re_eq hH x] at h1
    have h2 : ∑ i, hH.eigenvalues i * Complex.normSq ((U *ᵥ x) i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      by_cases hi : 0 < hH.eigenvalues i
      · rw [hz i hi]
        simp
      · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hi) (Complex.normSq_nonneg _)
    linarith
  have hB' : Module.finrank ℂ B ≤ Fintype.card {i // ¬ 0 < hH.eigenvalues i} := by
    apply finrank_le_of_coord U (fun i => ¬ 0 < hH.eigenvalues i) B
    intro x hx hz
    by_contra hne
    have h1 := hB x hx hne
    rw [form_re_eq hH x] at h1
    have h2 : 0 ≤ ∑ i, hH.eigenvalues i * Complex.normSq ((U *ᵥ x) i) := by
      apply Finset.sum_nonneg
      intro i _
      by_cases hi : 0 < hH.eigenvalues i
      · exact mul_nonneg hi.le (Complex.normSq_nonneg _)
      · rw [hz i hi]
        simp
    linarith
  have hc : Fintype.card {i // ¬ 0 < hH.eigenvalues i} =
      n - Fintype.card {i // 0 < hH.eigenvalues i} := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
  have hle : Fintype.card {i // 0 < hH.eigenvalues i} ≤ n := by
    simpa using Fintype.card_subtype_le (fun i => 0 < hH.eigenvalues i)
  have hs : sigPosH hH = Fintype.card {i // 0 < hH.eigenvalues i} := by
    unfold sigPosH
    exact Fintype.card_congr' rfl
  rw [hs]
  omega

theorem UpperTheory.hermitian_congruent_and_positive_eigenvector_of_signature :
    ∀ (n δ : ℕ) (H K J : Matrix (Fin n) (Fin n) ℂ) (e : ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian), (e = Complex.I ∨ e = -Complex.I) → J * J = -1 → ((-e) • (H * J)).PosDef → Matrix.trace J = e * (2 * (δ : ℂ) - (n : ℂ)) → K.det ≠ 0 → sigPosH hK = δ → (∃ Z : GL (Fin n) ℂ, H = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * K * (Z : Matrix (Fin n) (Fin n) ℂ)) ∧ (0 < δ → ∃ z : Fin n → ℂ, J *ᵥ z = e • z ∧ 0 < (star z ⬝ᵥ (H *ᵥ z)).re) := by
  intro n δ H K J e hH hK he hJJ hM htr hKdet hKsig
  have he2 : e * e = -1 := by
    rcases he with rfl | rfl <;> simp
  set E : Matrix (Fin n) (Fin n) ℂ := e • J with hEdef
  have hEE : E * E = 1 := by
    rw [hEdef, smul_mul_smul_comm, he2, hJJ, neg_smul, smul_neg, one_smul, neg_neg]
  have hJE : J = (-e) • E := by
    rw [hEdef, smul_smul, neg_mul, he2, neg_neg, one_smul]
  set P : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (1 - E) with hPdef
  have h2 : (1 - E) * (1 - E) = (2 : ℂ) • (1 - E) := by
    rw [sub_mul, mul_sub, mul_sub, _root_.one_mul, _root_.mul_one, _root_.one_mul, hEE, two_smul]
    abel
  have hPP : P * P = P := by
    rw [hPdef, smul_mul_smul_comm, h2, smul_smul]
    norm_num
  have hEP : E * P = -P := by
    rw [hPdef, Matrix.mul_smul, mul_sub, _root_.mul_one, hEE, ← smul_neg, neg_sub]
  set f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.toLin' P with hfdef
  have hidem : IsIdempotentElem f := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hPP]
  have hJrange : ∀ x ∈ LinearMap.range f, J *ᵥ x = e • x := by
    rintro x ⟨y, rfl⟩
    rw [hfdef, Matrix.toLin'_apply, hJE, smul_mulVec, mulVec_mulVec, hEP, neg_mulVec,
      smul_neg, ← neg_smul, neg_neg]
  have hJker : ∀ x ∈ LinearMap.ker f, J *ᵥ x = (-e) • x := by
    intro x hx
    rw [LinearMap.mem_ker, hfdef, Matrix.toLin'_apply, hPdef, smul_mulVec, sub_mulVec,
      one_mulVec, smul_eq_zero] at hx
    have hx' : x = E *ᵥ x := by
      rcases hx with h | h
      · norm_num at h
      · exact (sub_eq_zero.1 h)
    rw [hJE, smul_mulVec, ← hx']
  have hform : ∀ x c, J *ᵥ x = c • x → ((-e) • (H * J)) *ᵥ x = ((-e) * c) • (H *ᵥ x) := by
    intro x c hx
    rw [smul_mulVec, ← mulVec_mulVec, hx, mulVec_smul, smul_smul]
  have hApos : ∀ x ∈ LinearMap.range f, x ≠ 0 → 0 < (star x ⬝ᵥ (H *ᵥ x)).re := by
    intro x hx hx0
    have h0 := hM.re_dotProduct_pos hx0
    rw [hform x e (hJrange x hx), neg_mul, he2, neg_neg, one_smul] at h0
    simpa using h0
  have hBneg : ∀ x ∈ LinearMap.ker f, x ≠ 0 → (star x ⬝ᵥ (H *ᵥ x)).re < 0 := by
    intro x hx hx0
    have h0 := hM.re_dotProduct_pos hx0
    rw [hform x (-e) (hJker x hx), neg_mul_neg, he2, neg_one_smul, dotProduct_neg] at h0
    have h1 : 0 < -(star x ⬝ᵥ (H *ᵥ x)).re := by simpa using h0
    linarith
  have hAB : Module.finrank ℂ (LinearMap.range f) + Module.finrank ℂ (LinearMap.ker f) = n := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
  have htrP : P.trace = (δ : ℂ) := by
    rw [hPdef, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one, hEdef, Matrix.trace_smul, htr,
      Fintype.card_fin, smul_eq_mul, smul_eq_mul]
    linear_combination (-(2 * (δ : ℂ) - (n : ℂ)) / 2) * he2
  have hrank : Module.finrank ℂ (LinearMap.range f) = δ := by
    have h0 := (LinearMap.IsIdempotentElem.isProj_range f hidem).trace
    rw [hfdef, Matrix.trace_toLin'_eq, htrP] at h0
    exact_mod_cast h0.symm
  have hsig : sigPosH hH = δ := by
    rw [sig_eq_finrank hH _ _ hAB hApos hBneg, hrank]
  have hHdet : H.det ≠ 0 := by
    intro h0
    have hd := hM.det_pos
    rw [Matrix.det_smul, Matrix.det_mul, h0, zero_mul, mul_zero] at hd
    exact lt_irrefl _ hd
  refine ⟨?_, ?_⟩
  · obtain ⟨Z, hZ⟩ := HermCongruence.congr_of_sigPosH_eq K H hK hH hKdet hHdet (by rw [hKsig, hsig])
    exact ⟨Z, hZ⟩
  · intro hδ
    have hpos : 0 < Module.finrank ℂ (LinearMap.range f) := hrank ▸ hδ
    obtain ⟨⟨z, hzA⟩, hz0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
    have hz0' : z ≠ 0 := fun h => hz0 (Subtype.ext h)
    exact ⟨z, hJrange z hzA, hApos z hzA hz0'⟩
end
end

