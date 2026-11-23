module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0024

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerSplitRankUpperBound
section
open GlobalTheory.RegSS

noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.SplitRankBound

theorem zpow_sum_eq {M : Type} [CommGroup M] (a : M) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, _root_.zpow_add, ih]

theorem two_zpow_eq_one {F : Type} [Field F] [CharZero F] {m : ℤ} (h : (2:F) ^ m = 1) : m = 0 := by
  have h2 : ((2:ℚ) ^ m : ℚ) = (2:ℚ) ^ (0:ℤ) := by
    rw [zpow_zero]
    apply (algebraMap ℚ F).injective
    rw [map_zpow₀, map_ofNat, h, map_one]
  exact (zpow_right_strictMono₀ one_lt_two).injective h2

set_option maxHeartbeats 1000000 in
theorem splitRankUpper (hL : SubtorusLaurent) (hM : CharacterMonomial) (hP : SeparatingPoints) :
    SplitRankUpper := by
  intro F E _ _ _ _ n _ _ σ J γ hR hPl hPC k K _ _ he s hA
  classical
  obtain ⟨A⟩ := hA
  haveI : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) := Module.Finite.of_basis hPl.2.1.some
  obtain ⟨ψ, hsep, hfield⟩ := hP F E σ hR.quad (plusAlg σ J (γ : Matrix n n E)) k K he
  have hinj := (hPC F).1
  have hcent := (hPC F).2.2
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective
    (toMat σ J (γ : Matrix n n E) F).toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hρT : ∀ x, ρ (toMat σ J (γ : Matrix n n E) F x) = x := fun x => LinearMap.congr_fun hρ x
  have hex : ∀ t : Fin s → Fˣ, ∃ u ∈ normOne σ J (γ : Matrix n n E) F,
      toMat σ J (γ : Matrix n n E) F (u : LPts σ J (γ : Matrix n n E) F) =
        ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) :=
    fun t => (hcent _).1 (A.mem F t)
  have hTu : ∀ t : Fin s → Fˣ, toMat σ J (γ : Matrix n n E) F
      (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))) =
        ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) := by
    intro t; obtain ⟨u, -, hu⟩ := hex t; rw [← hu, hρT]
  have hnorm : ∀ t : Fin s → Fˣ,
      ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) *
        lConj σ J (γ : Matrix n n E) F (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)))
          = 1 := by
    intro t; obtain ⟨u, hu, hu'⟩ := hex t; rw [← hu', hρT]; exact hu
  let uu : (Fin s → Fˣ) →* LPts σ J (γ : Matrix n n E) F :=
    { toFun := fun t => ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))
      map_one' := hinj (by rw [hTu, map_one, Units.val_one, map_one])
      map_mul' := fun a b => hinj (by
        rw [map_mul (toMat σ J (γ : Matrix n n E) F), hTu a, hTu b, ← Units.val_mul, ← map_mul, hTu]) }
  have huu : ∀ t, uu t = ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) := fun _ => rfl
  clear_value uu
  obtain ⟨S, C, hC⟩ := hL F E n σ J γ s A
  have hmono : ∀ i, ∃ a : Fin s → ℤ, ∀ t : Fin s → Fˣ,
      ψ i (uu t) = algebraMap F (AlgebraicClosure F) ((∏ j, t j ^ a j : Fˣ) : F) := by
    intro i
    refine hM F (AlgebraicClosure F) s ((ψ i : _ →+* AlgebraicClosure F).toMonoidHom.comp uu) S
      (fun a => ψ i (ρ (C a))) (fun t => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, RingHom.coe_coe, huu, hC t, map_sum, map_smul]
  choose a ha using hmono
  have hconj : ∀ i t, ψ i (uu t) * ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1 := by
    intro i t; rw [← map_mul, huu, hnorm, map_one]
  have hlc : tConj3 (plusAlg σ J (γ : Matrix n n E)) σ F = lConj σ J (γ : Matrix n n E) F := rfl
  have hsq : ∀ i, IsField (K i ⊗[F] E) → ∀ t : Fin s → Fˣ,
      ((∏ j, t j ^ a i j : Fˣ) : F) * ((∏ j, t j ^ a i j : Fˣ) : F) = 1 := by
    intro i hi t
    have h0 : ψ i (uu t - algebraMap F _ ((∏ j, t j ^ a i j : Fˣ) : F)) = 0 := by
      rw [map_sub, AlgHom.commutes, ha, sub_self]
    have h1 := hfield i hi _ h0
    rw [hlc, map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    have h2 := hconj i t
    rw [ha, h1, ← map_mul] at h2
    exact (algebraMap F (AlgebraicClosure F)).injective (h2.trans (map_one _).symm)
  let M : Matrix {i : Fin k // ¬ IsField (K i ⊗[F] E)} (Fin s) ℤ := Matrix.of fun i j => a i.1 j
  have hfinj : Function.Injective M.mulVecLin := by
    refine (injective_iff_map_eq_zero M.mulVecLin).2 fun w hw => ?_
    have hw' : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∑ j, a i.1 j * w j = 0 := by
      intro i
      have := congrFun hw i
      simpa [M, Matrix.mulVec, dotProduct] using this
    let u2 : Fˣ := Units.mk0 2 two_ne_zero
    let t : Fin s → Fˣ := fun j => u2 ^ w j
    have hprod : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = (2:F) ^ (∑ j, a i j * w j) := by
      intro i
      have : (∏ j, t j ^ a i j : Fˣ) = u2 ^ (∑ j, a i j * w j) := by
        rw [zpow_sum_eq]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [t]
        rw [← _root_.zpow_mul, mul_comm]
      rw [this, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    have hone : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = 1 := by
      intro i
      by_cases hi : IsField (K i ⊗[F] E)
      · have h := hsq i hi t
        rw [hprod, ← zpow_add₀ (two_ne_zero)] at h
        have h0 := two_zpow_eq_one h
        rw [hprod, show ∑ j, a i j * w j = 0 by omega, zpow_zero]
      · rw [hprod, hw' ⟨i, hi⟩, zpow_zero]
    have hψ1 : ∀ i, ψ i (uu t) = 1 := fun i => by rw [ha, hone, map_one]
    have hψc : ∀ i, ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1 := fun i => by
      have h := hconj i t; rwa [hψ1, one_mul] at h
    have hut : uu t = 1 := by
      have := hsep (uu t - 1) fun i => ⟨by rw [map_sub, hψ1, map_one, sub_self],
        by rw [hlc, map_sub, map_sub, hψc, map_one, map_one, sub_self]⟩
      rwa [sub_eq_zero] at this
    have hhom : A.hom F t = A.hom F 1 := by
      refine Units.ext ?_
      rw [(A.hom F).map_one, Units.val_one, ← hTu t, ← huu, hut,
        map_one]
    have ht1 : t = 1 := A.inj F hhom
    funext j
    have hj := congrFun ht1 j
    have hj' : ((u2 ^ w j : Fˣ) : F) = 1 := by
      have := congrArg Units.val hj
      simpa [t] using this
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hj'
    exact two_zpow_eq_one hj'
  have hle := LinearMap.finrank_le_finrank_of_injective hfinj
  rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at hle
  rw [Nat.card_eq_fintype_card]
  exact hle

end GlobalTheory.RegSS.SplitRankBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateFactorPointsSeparate
section
noncomputable section

open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem nonempty_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [Nontrivial A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m).toLinearMap (Ideal.Quotient.mkₐ_surjective F m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

theorem exists_eq_tmul_add_tmul {F E P : Type} [Field F] [CommRing E] [Algebra F E] [CommRing P]
    [Algebra F P] (b : Module.Basis (Fin 2) F E) (x : P ⊗[F] (E ⊗[F] F)) :
    ∃ p q : P, x = p ⊗ₜ (b 0 ⊗ₜ (1 : F)) + q ⊗ₜ (b 1 ⊗ₜ (1 : F)) := by
  induction x with
  | tmul p y =>
    obtain ⟨e, rfl⟩ := (TensorProduct.rid F E).symm.surjective y
    refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
    have hs := b.sum_repr e
    rw [Fin.sum_univ_two] at hs
    rw [TensorProduct.rid_symm_apply, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, hs]
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [TensorProduct.add_tmul]; abel⟩

theorem separatingPoints : SeparatingPoints := by
  intro F E _ _ _ _ σ hσ P _ _ _ k K _ _ ⟨e⟩
  haveI := quad_finite hσ
  haveI := quad_nontrivial hσ
  obtain ⟨b, d, hb0, hb1, hd, hbb⟩ := quad_exists_basis hσ
  let pr : ∀ i, P →ₐ[F] K i := fun i => (Pi.evalAlgHom F K i).comp e.toAlgHom
  have hpr : ∀ i p, pr i p = e p i := fun _ _ => rfl
  haveI : ∀ i, Module.Finite F (K i) := fun i =>
    Module.Finite.of_surjective (pr i).toLinearMap fun y => by
      obtain ⟨p, hp⟩ := e.surjective (Pi.single i y)
      exact ⟨p, by simp [hpr, hp]⟩
  let χ : ∀ i, K i ⊗[F] E →ₐ[F] AlgebraicClosure F := fun i =>
    (nonempty_algHom_algebraicClosure F (K i ⊗[F] E)).some
  let π : ∀ i, P ⊗[F] (E ⊗[F] F) →ₐ[F] K i ⊗[F] E := fun i =>
    Algebra.TensorProduct.map (pr i) (Algebra.TensorProduct.rid F F E).toAlgHom
  have hπ : ∀ i p (y : E), π i (p ⊗ₜ (y ⊗ₜ (1 : F))) = e p i ⊗ₜ y := fun i p y => by
    simp [π, hpr]
  have hc : ∀ (p : P) (y : E), tConj3 P σ F (p ⊗ₜ (y ⊗ₜ (1 : F))) = p ⊗ₜ (σ y ⊗ₜ (1 : F)) :=
    fun p y => by simp [tConj3]
  refine ⟨fun i => (χ i).comp (π i), fun x hx => ?_, fun i hi x hx => ?_⟩
  · obtain ⟨p, q, rfl⟩ := exists_eq_tmul_add_tmul b x
    have key : ∀ i, e p i = 0 ∧ e q i = 0 := fun i => by
      obtain ⟨h1, h2⟩ := hx i
      have hm : (e q i ⊗ₜ[F] b 1 : K i ⊗[F] E) = (e q i ⊗ₜ[F] 1) * (1 ⊗ₜ[F] b 1) := by simp
      simp only [AlgHom.comp_apply, map_add (f := _), hc, hπ, hb0, hb1, map_one, TensorProduct.tmul_neg,
        map_neg] at h1 h2
      rw [hm, map_mul] at h1 h2
      have hδ : χ i (1 ⊗ₜ[F] b 1) ≠ 0 := fun h0 => by
        have : χ i (1 ⊗ₜ[F] b 1) * χ i (1 ⊗ₜ[F] b 1) = algebraMap F _ d := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, hbb, mul_one,
            ← Algebra.TensorProduct.algebraMap_apply', AlgHom.commutes]
        rw [h0, zero_mul] at this
        exact hd ((map_eq_zero _).1 this.symm)
      have inj : ∀ y : K i, χ i (y ⊗ₜ[F] 1) = 0 → y = 0 := fun y hy =>
        (map_eq_zero ((χ i).comp Algebra.TensorProduct.includeLeft : K i →ₐ[F] _)).1 hy
      refine ⟨inj _ (by linear_combination (h1 + h2) / 2), inj _ ?_⟩
      exact (mul_eq_zero.1 (by linear_combination (h1 - h2) / 2)).resolve_right hδ
    have hp : p = 0 := e.injective (by rw [map_zero]; exact funext fun i => (key i).1)
    have hq : q = 0 := e.injective (by rw [map_zero]; exact funext fun i => (key i).2)
    simp [hp, hq]
  · have h0 : π i x = 0 := by
      by_contra h0
      obtain ⟨y, hy⟩ := hi.mul_inv_cancel h0
      have := congrArg (χ i) hy
      rw [map_mul, show χ i (π i x) = 0 from hx, zero_mul, map_one] at this
      exact zero_ne_one this
    have h1 : π i (tConj3 P σ F x) = tConj (K i) σ (π i x) := by
      obtain ⟨p, q, rfl⟩ := exists_eq_tmul_add_tmul b x
      simp only [map_add (f := _), hc, hπ, tConj, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [AlgHom.comp_apply, h1, h0, map_zero, map_zero]

end GlobalTheory.RegSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorGeneratedAlgebraStructure
section
noncomputable section

open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS.CycAlg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def lowPoly (c : n → A) : A[X] :=
  ∑ j, c j • (X : A[X]) ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)

theorem aeval_lowPoly_mulVec (M : Matrix n n A) (v c : n → A) :
    aeval M (lowPoly c) *ᵥ v = krylov M v *ᵥ c := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lowPoly, map_sum, map_smul, map_pow, aeval_X, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [krylov, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_lowPoly (M : Matrix n n A) (p : A[X]) :
    ∃ c : n → A, p %ₘ M.charpoly = lowPoly c := by
  nontriviality A
  have h : (p %ₘ M.charpoly).degree < Fintype.card n := by
    rw [← Matrix.charpoly_degree_eq_dim M]
    exact degree_modByMonic_lt p M.charpoly_monic
  refine ⟨fun j => (p %ₘ M.charpoly).coeff (Fintype.equivFin n j), ?_⟩
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq (p %ₘ M.charpoly),
    Polynomial.sum_fin _ (by simp) h |>.symm]
  rw [lowPoly, ← Equiv.sum_comp (Fintype.equivFin n)]
  simp [Polynomial.smul_eq_C_mul]

theorem charpoly_dvd {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) {p : A[X]}
    (hp : aeval M p *ᵥ v = 0) : M.charpoly ∣ p := by
  obtain ⟨c, hc⟩ := exists_lowPoly M p
  rw [Matrix.aeval_eq_aeval_mod_charpoly, hc, aeval_lowPoly_mulVec] at hp
  have h0 : c = 0 := by
    have := congrArg (fun w => (krylov M v)⁻¹ *ᵥ w) hp
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h] using this
  rw [← modByMonic_eq_zero_iff_dvd M.charpoly_monic, hc, h0]
  simp [lowPoly]

theorem exists_aeval {M : Matrix n n A} (l : genAlg M) :
    ∃ p : A[X], aeval M p = (l : Matrix n n A) := by
  exact (Algebra.adjoin_singleton_eq_range_aeval A M).le l.2

theorem coe_aeval_gen (M : Matrix n n A) (p : A[X]) :
    ((aeval (gen M) p : genAlg M) : Matrix n n A) = aeval M p :=
  (Polynomial.aeval_algHom_apply (genAlg M).val (gen M) p).symm

def actOn (M : Matrix n n A) (v : n → A) : genAlg M →ₗ[A] (n → A) where
  toFun l := (l : Matrix n n A) *ᵥ v
  map_add' a b := Matrix.add_mulVec _ _ _
  map_smul' c a := Matrix.smul_mulVec c (a : Matrix n n A) v

theorem actOn_bijective {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) :
    Function.Bijective (actOn M v) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun l hl => ?_, fun w => ?_⟩
  · obtain ⟨p, hp⟩ := exists_aeval l
    have hl' : aeval M p *ᵥ v = 0 := by rw [hp]; exact hl
    obtain ⟨q, rfl⟩ := charpoly_dvd h hl'
    refine Subtype.ext ?_
    rw [← hp, map_mul, Matrix.aeval_self_charpoly, zero_mul]; rfl
  · refine ⟨aeval (gen M) (lowPoly ((krylov M v)⁻¹ *ᵥ w)), ?_⟩
    change ((aeval (gen M) _ : genAlg M) : Matrix n n A) *ᵥ v = w
    rw [coe_aeval_gen, aeval_lowPoly_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h,
      Matrix.one_mulVec]

theorem aeval_gen_charpoly (M : Matrix n n A) : aeval (gen M) M.charpoly = 0 :=
  Subtype.ext (by rw [coe_aeval_gen, Matrix.aeval_self_charpoly]; rfl)

def toGen (M : Matrix n n A) : AdjoinRoot M.charpoly →ₐ[A] genAlg M :=
  AdjoinRoot.liftAlgHom M.charpoly (Algebra.ofId A _) (gen M) (aeval_gen_charpoly M)

theorem toGen_mk (M : Matrix n n A) (p : A[X]) :
    toGen M (AdjoinRoot.mk _ p) = aeval (gen M) p :=
  AdjoinRoot.liftAlgHom_mk _ _ _ _ p

theorem toGen_bijective {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) :
    Function.Bijective (toGen M) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun l => ?_⟩
  · obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [toGen_mk] at hx
    rw [AdjoinRoot.mk_eq_zero]
    refine charpoly_dvd h ?_
    rw [← coe_aeval_gen, hx]
    exact Matrix.zero_mulVec v
  · obtain ⟨p, hp⟩ := exists_aeval l
    exact ⟨AdjoinRoot.mk _ p, Subtype.ext (by rw [toGen_mk, coe_aeval_gen, hp])⟩

theorem cyclicAlgebra : GlobalTheory.RegSS.CyclicAlgebra := by
  intro A _ n _ _ M v h
  refine ⟨⟨AlgEquiv.ofBijective (toGen M) (toGen_bijective h), ?_⟩,
    ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective (actOn M v) (actOn_bijective h))⟩,
    actOn_bijective h⟩
  change toGen M (AdjoinRoot.mk _ X) = _
  rw [toGen_mk, aeval_X]

end GlobalTheory.RegSS.CycAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
section
open Matrix

namespace GlobalTheory.RegSS

private theorem aeval_mul_mulVec {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (f g : Polynomial K) (v : n → K) :
    Polynomial.aeval M (f * g) *ᵥ v = Polynomial.aeval M f *ᵥ (Polynomial.aeval M g *ᵥ v) := by
  rw [map_mul, Matrix.mulVec_mulVec]

private theorem det_aeval_eq_zero_of_irreducible_dvd_charpoly {K : Type} [Field K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) {q : Polynomial K} (hq : Irreducible q)
    (hd : q ∣ M.charpoly) : (Polynomial.aeval M q).det = 0 := by
  have : Fact (Irreducible q) := ⟨hq⟩
  obtain ⟨s, hs⟩ := hd
  have hα : Polynomial.aeval (AdjoinRoot.root q) q = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hroot : (q.map (algebraMap K (AdjoinRoot q))).IsRoot (AdjoinRoot.root q) := by
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, hα]
  obtain ⟨g, hg⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
  have hN : (Matrix.scalar n (AdjoinRoot.root q) - M.map (algebraMap K (AdjoinRoot q))).det = 0 := by
    rw [← Matrix.eval_charpoly, Matrix.charpoly_map, hs, Polynomial.map_mul, Polynomial.eval_mul,
      Polynomial.eval_map_algebraMap, hα, zero_mul]
  have hmap : Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q =
      (Polynomial.aeval M q).map (algebraMap K (AdjoinRoot q)) := by
    exact Polynomial.aeval_algHom_apply ((Algebra.ofId K (AdjoinRoot q)).mapMatrix (m := n)) M q
  have hfac : Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q =
      (M.map (algebraMap K (AdjoinRoot q)) - Matrix.scalar n (AdjoinRoot.root q)) *
        Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) g := by
    rw [← Polynomial.aeval_map_algebraMap (AdjoinRoot q), hg, map_mul, map_sub, Polynomial.aeval_X,
      Polynomial.aeval_C]
    congr 2
  have h2 : (Polynomial.aeval (M.map (algebraMap K (AdjoinRoot q))) q).det = 0 := by
    rw [hfac, Matrix.det_mul, ← neg_sub, Matrix.det_neg, hN, mul_zero, zero_mul]
  have h3 : algebraMap K (AdjoinRoot q) (Polynomial.aeval M q).det = 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← hmap, h2]
  exact (map_eq_zero_iff _ (algebraMap K (AdjoinRoot q)).injective).mp h3

private theorem exists_vec_annihilator_eq_of_dvd_charpoly {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hsq : Squarefree M.charpoly) (q : Polynomial K) :
    q ∣ M.charpoly → ∃ w : n → K, Polynomial.aeval M q *ᵥ w = 0 ∧
      ∀ f : Polynomial K, Polynomial.aeval M f *ᵥ w = 0 → q ∣ f := by
  refine UniqueFactorizationMonoid.induction_on_prime q ?_ ?_ ?_
  · intro h
    exact absurd (zero_dvd_iff.mp h) M.charpoly_monic.ne_zero
  · intro x hx _
    exact ⟨0, Matrix.mulVec_zero _, fun _ _ => hx.dvd⟩
  · intro r π _ hπ ih hd
    obtain ⟨wr, hwr0, hwr⟩ := ih (dvd_trans (dvd_mul_left r π) hd)
    obtain ⟨wp, hwpne, hwp0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
      (det_aeval_eq_zero_of_irreducible_dvd_charpoly M hπ.irreducible (dvd_trans (dvd_mul_right π r) hd))
    have hcop : IsCoprime π r := by
      rw [hπ.coprime_iff_not_dvd]
      rintro ⟨t, rfl⟩
      exact hπ.not_isUnit (hsq π (dvd_trans ⟨t, by ring⟩ hd))
    have hwp : ∀ f : Polynomial K, Polynomial.aeval M f *ᵥ wp = 0 → π ∣ f := by
      intro f hf
      by_contra hn
      obtain ⟨a, b, hab⟩ := hπ.coprime_iff_not_dvd.mpr hn
      apply hwpne
      have h0 : Polynomial.aeval M (a * π + b * f) *ᵥ wp = 0 := by
        rw [map_add (f := _), Matrix.add_mulVec, aeval_mul_mulVec, aeval_mul_mulVec, hwp0, hf,
          Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
      rwa [hab, map_one, Matrix.one_mulVec] at h0
    refine ⟨wr + wp, ?_, ?_⟩
    · have e1 : Polynomial.aeval M (π * r) *ᵥ wr = 0 := by
        rw [aeval_mul_mulVec, hwr0, Matrix.mulVec_zero]
      have e2 : Polynomial.aeval M (π * r) *ᵥ wp = 0 := by
        rw [mul_comm π r, aeval_mul_mulVec, hwp0, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, e1, e2, add_zero]
    · intro f hf
      have hfp : Polynomial.aeval M (f * π) *ᵥ wp = 0 := by
        rw [aeval_mul_mulVec, hwp0, Matrix.mulVec_zero]
      have hfw : Polynomial.aeval M (f * π) *ᵥ (wr + wp) = 0 := by
        rw [mul_comm f π, aeval_mul_mulVec, hf, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, hfp, add_zero] at hfw
      have hrw : Polynomial.aeval M (f * r) *ᵥ wr = 0 := by
        rw [aeval_mul_mulVec, hwr0, Matrix.mulVec_zero]
      have hgw : Polynomial.aeval M (f * r) *ᵥ (wr + wp) = 0 := by
        rw [mul_comm f r, aeval_mul_mulVec, hf, Matrix.mulVec_zero]
      rw [Matrix.mulVec_add, hrw, zero_add] at hgw
      exact hcop.mul_dvd (hcop.dvd_of_dvd_mul_right (hwp _ hgw))
        (hcop.symm.dvd_of_dvd_mul_right (hwr _ hfw))

theorem cyclicField : GlobalTheory.RegSS.CyclicField := by
  intro K _ n _ _ M hsep
  obtain ⟨v, -, hv⟩ := exists_vec_annihilator_eq_of_dvd_charpoly M hsep.squarefree M.charpoly dvd_rfl
  refine ⟨v, ?_⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hc0
  set e := Fintype.equivFin n
  set f : Polynomial K := ∑ i : Fin (Fintype.card n),
    Polynomial.C (c (e.symm i)) * Polynomial.X ^ (i : ℕ) with hfdef
  have haeval : Polynomial.aeval M f = ∑ j : n, c j • M ^ ((e j : ℕ)) := by
    rw [hfdef, ← Equiv.sum_comp e]
    simp [Algebra.smul_def]
  have hf : Polynomial.aeval M f *ᵥ v = 0 := by
    rw [← hc, haeval]
    ext k
    simp only [krylov, Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hf0 : f = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_degree_lt (hv f hf) ?_
    rw [Matrix.charpoly_degree_eq_dim]
    exact Polynomial.degree_sum_fin_lt _
  funext j
  have hcoef := congrArg (fun g : Polynomial K => g.coeff (e j : ℕ)) hf0
  simpa [hfdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using hcoef

end GlobalTheory.RegSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleSelfAdjointPartEtale
section
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem plusEtale : PlusEtale := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hA hbij
  have : Nontrivial E := quad_nontrivial hreg.quad
  have : Module.Finite F E := quad_finite hreg.quad
  obtain ⟨b⟩ := hA.2.2.1
  have : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  have : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  have : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) :=
    Module.Finite.of_injective (plusAlg σ J (γ : Matrix n n E)).val.toLinearMap
      Subtype.val_injective
  have : IsReduced (genAlg (γ : Matrix n n E)) := genAlg_isReduced hreg hA
  have : IsReduced (plusAlg σ J (γ : Matrix n n E)) :=
    isReduced_of_injective (plusAlg σ J (γ : Matrix n n E)).val Subtype.val_injective
  refine ⟨etale_of_isReduced _, ?_, hbij⟩
  have hdim := (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, hreg.quad.finrank_eq,
    ← Module.finrank_mul_finrank F E (genAlg (γ : Matrix n n E)), hreg.quad.finrank_eq, Module.finrank_eq_card_basis b] at hdim
  have hr : Module.finrank F (plusAlg σ J (γ : Matrix n n E)) = Fintype.card n := by omega
  exact ⟨(Module.finBasisOfFinrankEq F _ hr).reindex (Fintype.equivFin n).symm⟩

end GlobalTheory.RegSS
end

