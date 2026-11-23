module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerEqCentralizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLieBundleIntersection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemStabilizerIff
public import Formalism.DegreeFormula.PointDegree.PowSum
public import Formalism.DegreeFormula.PointDegree.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Formalism.DegreeFormula.FlagDegFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0202
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfGaloisTraceRelationStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_of_galois_trace_relation : ∀ (A R C : Type) [CommRing A] [CommRing R] [Algebra A R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → Module.Finite R C := by
  first | (exact @GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (exact GlobalTheory.GoodEtaleFinite.finite_of_trace_relation) | (intros; apply GlobalTheory.GoodEtaleFinite.finite_of_trace_relation  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointWeightSpaceEqOfCharpolyStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H) (r : ℕ), (∀ c : C, LinearMap.charpoly (σ c) = ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ r).map (Int.castRingHom k)) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = r * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  first | (exact @GlobalTheory.WeightCount.finrank_weight_eq) | (exact GlobalTheory.WeightCount.finrank_weight_eq) | (intros; apply GlobalTheory.WeightCount.finrank_weight_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWeightSpaceProjectiveTensorEq
section
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.WtRank

abbrev chr (k : Type) [Field k] (C : Type) [CommRing C] (χ : C →+* k) : k ⊗[ℤ] C →ₐ[k] k :=
  Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem finrank_fix {k A M : Type*} [Field k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] (e : A) (W : Submodule k M)
    (hW : ∀ m, m ∈ W ↔ e • m = m) :
    Module.finrank k W = Module.finrank k (M ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A M)) := by
  set f : M →ₗ[k] M := DistribSMul.toLinearMap k M (1 - e)
  have hker : W = LinearMap.ker f := by
    ext m
    rw [hW, LinearMap.mem_ker]
    simp only [f, DistribSMul.toLinearMap_apply, sub_smul, one_smul, sub_eq_zero, eq_comm]
  have hrange : (Ideal.span {1 - e} • ⊤ : Submodule A M).restrictScalars k = LinearMap.range f := by
    ext m
    rw [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul, LinearMap.mem_range,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [f]
  have e1 := (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {1 - e} • ⊤ : Submodule A M)).finrank_eq
  rw [← e1, hrange, hker]
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  omega

theorem weight_finrank_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ H _ _ _ σ
  letI inst : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift
    (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  intro hP χ
  have hP' : Module.Projective (k ⊗[ℤ] C) H := hP
  have hact : ∀ (a : k ⊗[ℤ] C) (h : H), a • h = (Algebra.TensorProduct.lift
      (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)) a h := fun _ _ => rfl
  haveI : IsScalarTower k (k ⊗[ℤ] C) H := ⟨fun l a h => by
    rw [hact, hact, map_smul, LinearMap.smul_apply]⟩
  obtain ⟨e, he, h1, hn⟩ := GlobalTheory.T.exists_idempotent_local_of_character k (k ⊗[ℤ] C) (chr k C χ)
  have hσ : ∀ c, σ c = DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext h
    rw [DistribSMul.toLinearMap_apply, hact]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hlm : ∀ c, ((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c =
      DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext x
    simp [Algebra.TensorProduct.includeRight_apply]
  have eH : (⨅ c : C, (σ c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hσ]
  have eA : (⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hlm]
  rw [eH, eA]
  rw [finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C H χ e he h1 hn), finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C (k ⊗[ℤ] C) χ e he h1 hn),
    GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul k (k ⊗[ℤ] C) (chr k C χ) e he h1 hn H]
  have hq : Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) =
      Module.finrank k (H ⧸ (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H)) := by
    have heq : GlobalTheory.HTRho.mSub σ χ ⊤ = (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H).restrictScalars k := by
      ext x; rw [Submodule.restrictScalars_mem]; exact GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul k C H σ χ x
    rw [heq]; exact (Submodule.Quotient.restrictScalarsEquiv k _).finrank_eq
  rw [hq]
  congr 1
  have hI : (Ideal.span {1 - e} • ⊤ : Submodule (k ⊗[ℤ] C) (k ⊗[ℤ] C)) = Ideal.span {1 - e} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact ((Submodule.quotEquivOfEq _ _ hI).restrictScalars k).finrank_eq.symm

end GlobalTheory.WtRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumConjClassesCentralizerOrbitsEqPairOrbits
section
open GlobalTheory.OrbitUnfold GlobalTheory.OrbitUnfold.ConjSelf

noncomputable section

namespace GlobalTheory.OrbitUnfold

def conjClassesEquivOrbits (Γ : Type) [Group Γ] :
    ConjClasses Γ ≃ MulAction.orbitRel.Quotient Γ (ConjSelf Γ) :=
  Quotient.congr (⟨of, val, fun _ => rfl, fun _ => rfl⟩ : Γ ≃ ConjSelf Γ) (by
    intro a b
    show IsConj a b ↔ of a ∈ MulAction.orbit Γ (of b)
    rw [isConj_comm, isConj_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg of hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, congrArg val hc⟩)

theorem conjClassesEquivOrbits_mk {Γ : Type} [Group Γ] (γ : Γ) :
    conjClassesEquivOrbits Γ (Quotient.mk (IsConj.setoid Γ) γ) =
      Quotient.mk (MulAction.orbitRel Γ (ConjSelf Γ)) (of γ) := rfl

theorem finsum_conjClasses_centralizer_orbits {Γ Y : Type} [Group Γ] [MulAction Γ Y] (F : Y → Γ → ℂ)
    (hF : ∀ (η : Γ) (y : Y) (γ : Γ), F (η • y) (η * γ * η⁻¹) = F y γ)
    (_hstab : ∀ y : Y, (MulAction.stabilizer Γ y : Set Γ).Finite)
    (hsupp : ∀ y : Y, (Function.support (F y)).Finite)
    (hfin : {o : MulAction.orbitRel.Quotient Γ Y | ∃ γ, F (Quotient.out o) γ ≠ 0}.Finite) :
    ∑ᶠ c : ConjClasses Γ, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {Quotient.out c}) Y,
      ((Nat.card (MulAction.stabilizer Γ (Quotient.out o) ⊓ Subgroup.centralizer {Quotient.out c} :
        Subgroup Γ) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) (Quotient.out c) = pairSum F := by
  set_option backward.isDefEq.respectTransparency false in
    set e := conjClassesEquivOrbits Γ
    have key := _root_.GlobalTheory.finsum_orbitRel_fibred (H := Γ) (X := Y × ConjSelf Γ) (B := ConjSelf Γ) (E := Y)
      Prod.snd (fun _ _ => rfl) (fun b => Subgroup.centralizer {val b})
      (fun b => by rw [stabilizer_eq_centralizer])
      (fun b y => (y, b)) (fun b y y' h => congrArg Prod.fst h) (fun _ _ => rfl)
      (fun b x hx => ⟨x.1, Prod.ext rfl hx.symm⟩)
      (fun b h hh y => by
        have : h • b = b := by
          rw [← MulAction.mem_stabilizer_iff, stabilizer_eq_centralizer]; exact hh
        show (h • y, b) = (h • y, h • b)
        rw [this])
      (fun q => of (Quotient.out (e.symm q)))
      (fun q => by
        show Quotient.mk _ (of (Quotient.out (e.symm q))) = q
        have hout : ∀ c : ConjClasses Γ, (Quotient.mk (IsConj.setoid Γ) (Quotient.out c) : ConjClasses Γ) = c :=
          fun c => Quotient.out_eq c
        rw [← conjClassesEquivOrbits_mk, hout, Equiv.apply_symm_apply])
      (fun o => pairTerm F (Quotient.out o))
      (_root_.GlobalTheory.OrbitUnfold.finite_support_pairTerm F hF hsupp hfin)
    unfold pairSum
    rw [key, ← finsum_comp_equiv e]
    refine finsum_congr (fun c => ?_)
    change Quotient (IsConj.setoid Γ) at c
    change ConjClasses Γ at c
    change (Quotient (IsConj.setoid Γ)) at c
    rw [e.symm_apply_apply]
    dsimp only [ConjSelf.val, ConjSelf.of]
    refine finsum_congr (fun o => ?_)
    rw [pairTerm_out F hF]
    unfold pairTerm
    rw [stabilizer_pair]
    rfl

end GlobalTheory.OrbitUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOverConjPairsEqOrbitSum
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_over_conj_pairs_eq_orbit_sum : ∀ (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ),
    (∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x) →
    (∀ x : X, Finite (MulAction.stabilizer H x)) →
    (∀ x : X, (Function.support fun γ : H => f γ x).Finite) →
    ∀ x : X, ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  first | exact @GlobalTheory.PtFib.ptFib_mass | exact GlobalTheory.PtFib.ptFib_mass | (intros; apply GlobalTheory.PtFib.ptFib_mass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
section
open MvPolynomial Finset Formalism.DegreeFormula

namespace GlobalTheory.FlagPoly

open MvPolynomial Finset in
private theorem coeff_linearForm_pow_eq_factorial_mul_prod {σ : Type} [Fintype σ] [DecidableEq σ] (c : σ → ℝ) (n : ℕ)
    (d : σ →₀ ℕ) (hd : d.degree = n) :
    AddMonoidAlgebra.coeff ((∑ x, C (c x) * X x) ^ n) d =
      (n.factorial : ℝ) * ∏ x, (c x ^ d x / ((d x).factorial : ℝ)) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    ← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), ← mul_assoc, ← map_mul, coeff_C_mul,
    coeff_prod_X_pow]
  have hsum : ∑ i, d i = n := by
    rw [← hd, Finsupp.degree_eq_sum]
  rw [Finset.sum_eq_single (⇑d)]
  · have hind : d = Finsupp.indicator univ (fun i _ => d i) := by
      ext i; simp
    rw [if_pos hind, mul_one]
    have hspec := Nat.multinomial_spec (univ : Finset σ) (⇑d)
    rw [hsum] at hspec
    have hpos : (∏ i, ((d i).factorial : ℝ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro i _; exact_mod_cast (Nat.factorial_pos _).ne'
    rw [Finset.prod_div_distrib, ← hspec]
    push_cast
    field_simp
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro h
    apply hk
    funext i
    have := congrArg (fun f : σ →₀ ℕ => f i) h
    simpa using this.symm
  · intro h
    exfalso; apply h
    rw [Finset.mem_piAntidiag]
    exact ⟨hsum, fun i _ => Finset.mem_univ i⟩

open MvPolynomial Finset in
private theorem prod_factorial_rev_eq_prod_sub (N : ℕ) :
    ∏ j : Fin N, ((j.rev : ℕ).factorial : ℝ) =
      ∏ i : Fin N, ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
  cases N with
  | zero => simp
  | succ n =>
    have h1 : ∏ i : Fin (n + 1), ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) =
        (n.superFactorial : ℝ) := by
      rw [← Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) n, Matrix.det_vandermonde]
    rw [h1, ← Nat.prod_range_succ_factorial, Nat.cast_prod,
      ← Fin.prod_univ_eq_prod_range (fun x => ((x.factorial : ℕ) : ℝ)) (n + 1)]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun j => rfl)

open MvPolynomial Finset in
private theorem sum_sign_prod_pow_div_factorial_eq_prod {N : ℕ} (v : Fin N → ℝ) :
    ∑ π : Equiv.Perm (Fin N), ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
      ∏ i : Fin N, ∏ k : Fin N,
        if i < k then (v i - v k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1 := by
  have hrev : ∀ j : Fin N, N - 1 - (j : ℕ) = (j.rev : ℕ) := by
    intro j; rw [Fin.val_rev]; omega
  have hterm : ∀ π : Equiv.Perm (Fin N),
      ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
        (∏ i, Matrix.transpose (Matrix.projVandermonde 1 v) (π i) i) *
          ∏ j : Fin N, (((j.rev : ℕ).factorial : ℝ))⁻¹ := by
    intro π
    simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, hrev]
    congr 1
    · simp [Matrix.projVandermonde_apply]
    · exact Fintype.prod_equiv π _ _ (fun i => rfl)
  simp_rw [hterm, ← mul_assoc, ← Finset.sum_mul, ← Matrix.det_apply', Matrix.det_transpose,
    Matrix.det_projVandermonde, Finset.prod_inv_distrib, prod_factorial_rev_eq_prod_sub,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib, div_eq_mul_inv]
  simp only [Pi.one_apply, one_mul]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  congr 1
  ext k
  simp


open MvPolynomial Finset in
theorem _root_.GlobalTheory.FlagPoly.flagDegFormula : _root_.Formalism.DegreeFormula.FlagDegFormula := by
  unfold _root_.Formalism.DegreeFormula.FlagDegFormula
  intro ι _ _ N lam
  unfold _root_.Formalism.DegreeFormula.flagDeg _root_.Formalism.DegreeFormula.weylProd _root_.Formalism.DegreeFormula.linRoot
  rw [neg_pow, ← map_one (C : ℝ →+* MvPolynomial (ι × Fin N) ℝ), ← map_neg, ← map_pow, _root_.Formalism.DegreeFormula.PPowSum.degFl_C_mul]
  unfold _root_.Formalism.DegreeFormula.degFl
  simp_rw [coeff_linearForm_pow_eq_factorial_mul_prod _ _ _ (_root_.Formalism.DegreeFormula.PPowSum.degree_permExp _)]
  have hexp : ∀ (σ : ι → Equiv.Perm (Fin N)) (τ : ι) (i : Fin N),
      (_root_.Formalism.DegreeFormula.permExp σ) (τ, i) = N - 1 - ((σ τ) i : ℕ) := by
    intro σ τ i
    unfold _root_.Formalism.DegreeFormula.permExp
    rfl
  simp_rw [Fintype.prod_prod_type, hexp]
  rw [← Finset.prod_congr rfl (fun τ _ => sum_sign_prod_pow_div_factorial_eq_prod (lam τ)),
    Fintype.prod_sum]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.FlagPoly
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFerrandPushoutOverFibreProduct
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace GlobalTheory.FerrandFlat

theorem flat_of_appLE {Y : Scheme.{0}} {P : CommRingCat.{0}} (y : Y ⟶ Spec P) (h : ∀ V : Y.Opens, IsAffineOpen V → (y.appLE ⊤ V (fun _ _ => trivial)).hom.Flat) : Flat y :=
  HasRingHomProperty.of_iSup_eq_top (P := @Flat) (fun V : Y.affineOpens => V) (iSup_affineOpens_eq_top Y) (fun V => h V.1 V.2)

theorem flat_pushout : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → ∀ (Y₁ Y₂ Y₀ : Scheme.{0}) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback i₁ p₀ p₁ (Spec.map g₁) → IsPullback i₂ p₀ p₂ (Spec.map g₂) → Flat p₁ → Flat p₂ → ∀ (Y : Scheme.{0}) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂), IsClosedImmersion j₁ → IsClosedImmersion j₂ → (∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ (y : Y ⟶ Spec P), j₁ ≫ y = p₁ ≫ Spec.map f₁ → j₂ ≫ y = p₂ ≫ Spec.map f₂ → IsPullback j₁ p₁ y (Spec.map f₁) ∧ IsPullback j₂ p₂ y (Spec.map f₂) ∧ Flat y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw hj₁ hj₂ hV y hy₁ hy₂
  have H := _root_.GlobalTheory.SchlessingerAffine.flat_and_pushouts P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hg₁ hg₂ hn₁ hn₂ Y₁ Y₂ Y₀ p₁ p₂ p₀ i₁ i₂ h₁ h₂ hf₁ hf₂ Y j₁ j₂ hw
    hj₁ hj₂ hV y hy₁ hy₂
  exact ⟨_root_.GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app _ _ _ _ j₁ p₁ y (Spec.map f₁) inferInstance inferInstance inferInstance hy₁
      (fun V hV => (H V hV).2.1),
    _root_.GlobalTheory.PushoutSquare.isPullback_of_forall_isPushout_app _ _ _ _ j₂ p₂ y (Spec.map f₂) inferInstance inferInstance inferInstance hy₂
      (fun V hV => (H V hV).2.2),
    flat_of_appLE y (fun V hV => (H V hV).1)⟩

end GlobalTheory.FerrandFlat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfLocalRetractionsModMaximalIdealPowStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_of_local_retractions_mod_maximalIdeal_pow : ∀ {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ], (∀ n : ℕ, ∃ ψ : B →+* A ⧸ maximalIdeal A ^ (n + 1), ψ.comp φ = Ideal.Quotient.mk _) → (∀ n : ℕ, ∀ g₁ g₂ : B →+* B ⧸ maximalIdeal B ^ (n + 1), IsLocalHom g₁ → IsLocalHom g₂ → g₁.comp φ = g₂.comp φ → g₁ = g₂) → φ.Flat := by
  first | exact @GlobalTheory.flat_of_retractions_mod_pow | exact GlobalTheory.flat_of_retractions_mod_pow | (intros; apply GlobalTheory.flat_of_retractions_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclicStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_sums_cosets_semidirect_cyclic : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (∀ t : Γ, t ∈ Subgroup.zpowers s) → ∀ ζ : ℂ, IsPrimitiveRoot ζ (Nat.card Γ) → ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ (η (inr s) : ℂ) = ζ ∧ ∀ X Y : G ⋊[φ] Γ → ℂ, ((Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g) * star (Y (inl g)) = ∑ a ∈ Finset.range (Nat.card Γ), ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a)) ∧ (Nat.card Γ : ℂ) * ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = ∑ a ∈ Finset.range (Nat.card Γ), ζ ^ a * ∑ᶠ x, X x * star (Y x * (η x : ℂ) ^ a) := by
  first | (exact @GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (exact GlobalTheory.Shin.CosetFourier.fourier_coset_sums) | (intros; apply GlobalTheory.Shin.CosetFourier.fourier_coset_sums  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualStatement
section
open ReciprocityTheory.PGsh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_dual_frame_of_isSatFrame : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (i d : ℕ) (u : Fin i → Fin d → C), IsSatFrame v u → ∃ l : Fin i → Fin d → C, (∀ a e, IsIntV v (l a e)) ∧ ∀ a a', ∑ e, l a e * u a' e = if a = a' then 1 else 0 := by
  first | exact @GlobalTheory.FrameDual.frameDual | exact GlobalTheory.FrameDual.frameDual | (intros; apply GlobalTheory.FrameDual.frameDual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
section
noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.PsiPhi

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem phiInv_ofPadic (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  have key : ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p)) = ZMod.castHom (dvd_refl p) (PreTilt O p) :=
    Subsingleton.elim _ _
  simp only [phiInv, ofPadic, RingHom.comp_apply]
  ext n
  simp only [WittVector.map_coeff]
  exact RingHom.congr_fun key _

end GlobalTheory.DetInv.PsiPhi

namespace GlobalTheory.DetInv

end GlobalTheory.DetInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisComparisonMapInjectiveOfFlatStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisComparisonMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  first | (exact @GlobalTheory.GoodEtale.galMap_injective_of_flat) | (exact GlobalTheory.GoodEtale.galMap_injective_of_flat) | (intros; apply GlobalTheory.GoodEtale.galMap_injective_of_flat  <;> assumption)
end

