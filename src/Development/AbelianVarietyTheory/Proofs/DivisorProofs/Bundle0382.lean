module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0349
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsOfInjectiveZmodEtaleSheaf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorOfFlatComplexes
public import ReciprocityTheory.DualLattices.Bundle0004
public import ReciprocityTheory.DualLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.DualLattices.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0353

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInduction
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.FinSH

open IsLocalRing

theorem sh_of_finite_local (A T : Type) [CommRing A] [CommRing T] [Algebra A T] (hA : SH A)
    [Module.Finite A T] [IsLocalRing T] : SH T := by
  obtain ⟨hH, hk⟩ := hA
  refine ⟨GlobalTheory.henselianLocalRing_of_finite A T, ?_⟩
  have hc : (maximalIdeal T).comap (algebraMap A T) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal T))
  haveI : IsLocalHom (algebraMap A T) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal T).comap (algebraMap A T) := by rw [hc]; exact hna
    exact (maximalIdeal T).ne_top_iff_one.1 (maximalIdeal.isMaximal T).ne_top
      (by simpa using Ideal.mul_mem_left _ (↑ha.unit⁻¹ : T) (show algebraMap A T a ∈ maximalIdeal T from this))
  haveI : Algebra.IsIntegral (ResidueField A) (ResidueField T) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t', rfl⟩ := residue_surjective x
    have h1 : IsIntegral A (residue T t') :=
      (Algebra.IsIntegral.isIntegral (R := A) t').map (IsScalarTower.toAlgHom A T (ResidueField T))
    exact h1.tower_top
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField A)

def optionProdEquiv (A : Type) [CommRing A] {α : Type} (T : Option α → Type) [∀ i, CommRing (T i)]
    [∀ i, Algebra A (T i)] : (∀ o, T o) ≃ₐ[A] T none × ∀ a, T (some a) :=
  { Equiv.piOptionEquivProd with
    map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }

theorem induction_principle : ∀ (A : Type) [CommRing A], SH A → ∀ (P : ∀ (T : Type) [CommRing T] [Algebra A T], Prop),
  (∀ (T T' : Type) [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'], (T ≃ₐ[A] T') → P T → P T') →
  (∀ (T : Type) [CommRing T] [Algebra A T], Subsingleton T → P T) →
  (∀ (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] [Algebra A T₁] [Algebra A T₂], Module.Finite A T₁ → Module.Finite A T₂ →
    P T₁ → P T₂ → P (T₁ × T₂)) →
  (∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → SH T → P T) →
  ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → P T := by
  intro A _ hA P hiso hsub hprod hsh T _ _ hT
  obtain ⟨hH, hk⟩ := hA
  obtain ⟨ι, hι, S, _, _, e, hS⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing A T
  have key : ∀ (α : Type) [Finite α] (S : α → Type) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)],
      (∀ i, Module.Finite A (S i) ∧ SH (S i)) → P (∀ i, S i) := by
    intro α _
    induction α using Finite.induction_empty_option with
    | of_equiv e' ih =>
      intro S _ _ hS'
      exact hiso _ _ (AlgEquiv.piCongrLeft A S e') (ih (fun a => S (e' a)) (fun a => hS' (e' a)))
    | h_empty =>
      intro S _ _ _
      exact hsub _ inferInstance
    | h_option ih =>
      intro S _ _ hS'
      refine hiso _ _ (optionProdEquiv A S).symm ?_
      haveI : ∀ a, Module.Finite A (S (some a)) := fun a => (hS' (some a)).1
      exact hprod _ _ (hS' none).1 inferInstance (hsh _ (hS' none).1 (hS' none).2)
        (ih (fun a => S (some a)) (fun a => hS' (some a)))
  refine hiso _ _ e.symm (key ι S fun i => ⟨(hS i).2, ?_⟩)
  haveI := (hS i).1
  haveI := (hS i).2
  exact sh_of_finite_local A (S i) ⟨hH, hk⟩

end GlobalTheory.EtC.GmStep.FinSH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveSpanOfIntegralClosureStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projective_span_of_integralClosure' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  first | (exact @GlobalTheory.finite_projective_span_of_integralClosure) | (exact GlobalTheory.finite_projective_span_of_integralClosure) | (intros; apply GlobalTheory.finite_projective_span_of_integralClosure  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRetractionsOfAdjoinFinsetIntegralDomainStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain : ∀ (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E), Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤ → {χ : E →ₐ[D] T | χ.comp ι = AlgHom.id D T}.Finite := by
  first | (exact @GlobalTheory.finite_retractions_of_adjoin_finset_integral') | (exact GlobalTheory.finite_retractions_of_adjoin_finset_integral') | (intros; apply GlobalTheory.finite_retractions_of_adjoin_finset_integral'  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsOfInjectiveZmodEtaleSheafStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf : ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M], (∀ U : Scheme.{0}, Module.Flat (ULift.{1} (ZMod q)) (Sec M U)) ∧ FlatS M := by
  first | (exact @GlobalTheory.EtC.InjFlat.flat_of_injective) | (exact GlobalTheory.EtC.InjFlat.flat_of_injective) | (intros; apply GlobalTheory.EtC.InjFlat.flat_of_injective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorOfFlatComplexesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_tensor_of_flat_complexes : ∀ (R : Type) [CommRing R] {I J T : Cx R} (τ : Pair I J T), τ.IsTensor → (∀ t, FlatS (I.X t)) → (∀ t, FlatS (J.X t)) → ∀ w, FlatS (T.X w) := by
  first | (exact @GlobalTheory.EtC.FlatTens.flatS_tens) | (exact GlobalTheory.EtC.FlatTens.flatS_tens) | (intros; apply GlobalTheory.EtC.FlatTens.flatS_tens  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
section
noncomputable section

open WittVector Ideal

namespace GlobalTheory.AinfXi

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem coeff_pow_pow_zero (x : PreTilt O p) (n : ℕ) :
    PreTilt.coeff n x ^ p ^ n = PreTilt.coeff 0 x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, PreTilt.coeff_pow_p, ih]

theorem isUnit_of_coeff_zero {x : PreTilt O p} (h : IsUnit (PreTilt.coeff 0 x)) : IsUnit x := by
  have hn : ∀ n, IsUnit (PreTilt.coeff n x) := fun n =>
    (isUnit_pow_iff (pow_ne_zero n hp.out.ne_zero)).1 (by rw [coeff_pow_pow_zero]; exact h)
  have hu : ∀ n, (hn (n + 1)).unit ^ p = (hn n).unit := fun n =>
    Units.ext (by simp [PreTilt.coeff_pow_p])
  let f : ℕ → ModP O p := fun n => (((hn n).unit⁻¹ : (ModP O p)ˣ) : ModP O p)
  have hf : ∀ n, f (n + 1) ^ p = f n := fun n => by
    simp only [f]
    rw [← Units.val_pow_eq_pow_val, inv_pow, hu]
  let y : PreTilt O p := (⟨f, hf⟩ : Perfection (ModP O p) p)
  refine isUnit_iff_exists_inv.2 ⟨y, ?_⟩
  refine Perfection.ext fun n => ?_
  change PreTilt.coeff n (x * y) = PreTilt.coeff n 1
  rw [map_mul, map_one]
  change PreTilt.coeff n x * f n = 1
  exact IsUnit.mul_val_inv (hn n)

end Tilt

section Witt

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]

theorem witt_isUnit (c : WittVector p R) (h : IsUnit (constantCoeff c)) : IsUnit c := by
  obtain ⟨u, hu⟩ := h
  have hmem : c * teichmuller p ((u⁻¹ : Rˣ) : R) - 1 ∈ span {(p : WittVector p R)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul, map_one, ← hu,
      constantCoeff_apply (x := teichmuller p _), teichmuller_coeff_zero, Units.mul_inv, sub_self]
  have hj := IsAdicComplete.le_jacobson_bot (span {(p : WittVector p R)}) hmem
  have h1 := (mem_jacobson_bot.1 hj) 1
  rw [mul_one, sub_add_cancel] at h1
  exact isUnit_of_mul_isUnit_left h1

end Witt

section Main

open GlobalTheory.Sandwich

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]

theorem isDomain_ainf (hv : v.Integers O) : IsDomain (Ainf p O) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  infer_instance

theorem isLocalRing_preTilt (hv : v.Integers O) : IsLocalRing (PreTilt O p) := by
  have : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  haveI : Nontrivial (ModP O p) := ReciprocityTheory.PGsh.Ainf.quot_nontrivial _ (by
    rw [Ne, Ideal.span_singleton_eq_top]; exact Fact.out)
  haveI : IsLocalRing (ModP O p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (PreTilt.coeff 0 a) with h | h
  · exact Or.inl (isUnit_of_coeff_zero h)
  · exact Or.inr (isUnit_of_coeff_zero (by rwa [map_sub, map_one]))

theorem isLocalRing_ainf (hv : v.Integers O) : IsLocalRing (Ainf p O) := by
  haveI := isDomain_ainf (p := p) hv
  haveI := isLocalRing_preTilt (p := p) hv
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff a) with h | h
  · exact Or.inl (witt_isUnit a h)
  · exact Or.inr (witt_isUnit _ (by rwa [map_sub, map_one]))

variable (hv : v.Integers O) (ε : PreTilt O p) (hε : IsPrimitiveRoot (root ε).untilt p)
include hv hε

theorem ker_theta : RingHom.ker (fontaineTheta O p) = span {xi ε} :=
  ReciprocityTheory.PGsh.Ainf.ker_theta p O hv ε hε

theorem xi_nzd (y : Ainf p O) (hy : y * xi ε = 0) : y = 0 :=
  ReciprocityTheory.PGsh.Ainf.xi_nzd p O hv ε hε y hy

theorem dvd_of_dvd_mul_p (N : ℕ) (z : Ainf p O) (h : xi ε ^ N ∣ z * p) : xi ε ^ N ∣ z := by
  induction N generalizing z with
  | zero => simp
  | succ N ih =>
    obtain ⟨w, hw⟩ := h
    have h1 : fontaineTheta O p (z * p) = 0 := by
      rw [hw, map_mul, map_pow,
        show fontaineTheta O p (xi ε) = 0 from ReciprocityTheory.PGsh.Ainf.theta_xi p O hv ε hε,
        zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [map_mul, map_natCast] at h1
    have h0 : fontaineTheta O p z = 0 :=
      ReciprocityTheory.PGsh.Ainf.torsion_free p O hv 1 _ (by rw [pow_one]; exact h1)
    obtain ⟨z1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
    have h2 : (z1 * p - xi ε ^ N * w) * xi ε = 0 := by linear_combination hw
    obtain ⟨w', hw'⟩ := ih z1 ⟨w, sub_eq_zero.1 (xi_nzd hv ε hε _ h2)⟩
    exact ⟨w', by rw [hw']; ring⟩

theorem coeff_zero_eq_zero (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : constantCoeff x = 0 := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -, -⟩ := ReciprocityTheory.PGsh.a0 p C v O hv
  obtain ⟨u, hu⟩ := ((hX ε hv hε).2.2.2 pf hpf).2
  have hu' : xi ε = u * ((p : Ainf p O) - teichmuller p pf) := hu
  have hxi : constantCoeff (xi ε) = constantCoeff (u : Ainf p O) * (-pf) := by
    rw [hu', map_mul, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub,
      constantCoeff_apply (x := teichmuller p pf), teichmuller_coeff_zero]
  refine Perfection.ext fun n => ?_
  obtain ⟨w, hw⟩ := hx (p ^ n)
  change PreTilt.coeff n (constantCoeff x) = PreTilt.coeff n 0
  have h0 : PreTilt.coeff n (-pf) ^ p ^ n = 0 := by
    rw [coeff_pow_pow_zero, map_neg, ← PreTilt.mk_untilt_eq_coeff_zero, hpf, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  simp only [hw, hxi, map_mul, map_pow, mul_pow]
  rw [h0, mul_zero, zero_mul, map_zero]

theorem eq_zero_of_forall_dvd (x : Ainf p O) (hx : ∀ N, xi ε ^ N ∣ x) : x = 0 := by
  have key : ∀ k, ∀ x : Ainf p O, (∀ N, xi ε ^ N ∣ x) → (p : Ainf p O) ^ k ∣ x := by
    intro k
    induction k with
    | zero => intro x _; rw [pow_zero]; exact one_dvd _
    | succ k ih =>
      intro x hx
      have h0 := coeff_zero_eq_zero hv ε hε x hx
      rw [constantCoeff_apply] at h0
      obtain ⟨z, rfl⟩ := mem_span_singleton'.1 ((mem_span_p_iff_coeff_zero_eq_zero x).2 h0)
      obtain ⟨w, hw⟩ := ih z fun N => dvd_of_dvd_mul_p hv ε hε N z (hx N)
      exact ⟨w, by rw [hw]; ring⟩
  ext n
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero x (n + 1)).1
    (mem_span_singleton.2 (key (n + 1) x hx)) n (Nat.lt_succ_self n)
  simpa using h

theorem exists_order (x : Ainf p O) (hx : x ≠ 0) :
    ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ fontaineTheta O p y ≠ 0 := by
  classical
  have hex : ∃ N, ¬ xi ε ^ N ∣ x := by
    by_contra h
    exact hx (eq_zero_of_forall_dvd hv ε hε x fun N => by_contra fun h' => h ⟨N, h'⟩)
  have hM := Nat.find_spec hex
  have hM0 : Nat.find hex ≠ 0 := fun h => hM (by rw [h, pow_zero]; exact one_dvd _)
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  obtain ⟨y, hy⟩ : xi ε ^ N ∣ x := not_not.1 (Nat.find_min hex (by omega))
  refine ⟨N, y, hy, fun h0 => hM ?_⟩
  obtain ⟨y1, rfl⟩ := mem_span_singleton'.1 (by rw [← ker_theta hv ε hε]; exact h0)
  rw [hN, Nat.succ_eq_add_one]
  exact ⟨y1, by rw [hy]; ring⟩

end Main

section Statement

open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix

theorem ainf_local_xi_order : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ ε : PreTilt O p, IsPrimitiveRoot (root ε).untilt p → IsDomain (Ainf p O) ∧ IsLocalRing (Ainf p O) ∧ RingHom.ker (WittVector.fontaineTheta O p) = Ideal.span {xi ε} ∧ Function.Surjective (WittVector.fontaineTheta O p) ∧ WittVector.fontaineTheta O p (nu ε) ≠ 0 ∧ xi ε ≠ 0 ∧ (∀ x : Ainf p O, x ≠ 0 → ∃ (N : ℕ) (y : Ainf p O), x = xi ε ^ N * y ∧ WittVector.fontaineTheta O p y ≠ 0) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε
  haveI := isDomain_ainf (p := p) hv
  refine ⟨inferInstance, isLocalRing_ainf hv, ker_theta hv ε hε,
    ReciprocityTheory.PGsh.Ainf.theta_surj p O hv, ReciprocityTheory.PGsh.Ainf.theta_nu p O hv ε hε, fun h => ?_,
    fun x hx => exists_order hv ε hε x hx⟩
  exact one_ne_zero (xi_nzd hv ε hε 1 (by rw [h, mul_zero]))

end Statement

end GlobalTheory.AinfXi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHermitianMultiplierBraidRelationStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_hermitianMultiplier_braid_relation : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (b : Matrix ν ν E) (γ : ℂ), (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) γ → ∀ φ ∈ SB (Matrix α ν E), sc F χ (Fintype.card α) (-b⁻¹).det • fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 b 0 1) (fou c ψ Q μ φ)) = γ • parFun c ψ χ Q (fromBlocks (-b⁻¹) 1 0 (-b)) (fou c ψ Q μ (parFun c ψ χ Q (fromBlocks 1 (-b⁻¹) 0 1) φ)) := by
  first | exact @GlobalTheory.KSp.braid_relation | exact GlobalTheory.KSp.braid_relation | (intros; apply GlobalTheory.KSp.braid_relation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierIntertwinesSiegelLeviOperator
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem blocks_of_weyl_mul_eq {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
    {ν : Type} [Fintype ν] [DecidableEq ν] {p q : UG c (stdJ ν E)} (hp : p ∈ sieg c ν) (hq : q ∈ sieg c ν)
    (h : weyl c ν * p = q * weyl c ν) :
    (mat c p).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₂ = 0 ∧ (mat c q).toBlocks₁₁ = (mat c p).toBlocks₂₂ := by
  have h1 : stdJ ν E * mat c p = mat c q * stdJ ν E := congrArg (mat c) h
  rw [← fromBlocks_toBlocks (mat c p), ← fromBlocks_toBlocks (mat c q), (mem_sieg c).mp hp, (mem_sieg c).mp hq,
    stdJ, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h1
  obtain ⟨h11, h12, -, h22⟩ := h1
  refine ⟨?_, ?_, ?_⟩
  · simpa using h22
  · simpa using h11
  · simpa using h12.symm

theorem fou_parFun_levi : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∀ p ∈ sieg c ν, ∀ q ∈ sieg c ν, weyl c ν * p = q * weyl c ν → ∀ φ : Matrix α ν E → ℂ, fou c ψ Q μ (parFun c ψ χ Q (mat c p) φ) = parFun c ψ χ Q (mat c q) (fou c ψ Q μ φ) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ hχ _ _ μ _ p hp q hq hpq φ
  obtain ⟨hb, hb', ha'⟩ := blocks_of_weyl_mul_eq c hp hq hpq
  obtain ⟨had, -, -⟩ := _root_.GlobalTheory.KSp.sieg_blocks F E c δ hE ν p hp
  obtain ⟨β, hβ, -, -, hadj, -⟩ := _root_.GlobalTheory.KSp.pr_alg F E c δ hE α ν Q hQ
  obtain ⟨-, -, -, -, hsc, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hχ
  obtain ⟨-, hring, -⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  set a := (mat c p).toBlocks₁₁ with ha
  set d := (mat c p).toBlocks₂₂ with hd
  have hda : (d.map c)ᵀ * a = 1 := mul_eq_one_comm.mp had
  let A : GL ν E := ⟨a, (d.map c)ᵀ, had, hda⟩
  have hmap := _root_.GlobalTheory.KSp.map_twoSided_haar F E c δ hE α ν μ 1 A
  simp only [Units.val_one, Matrix.one_mul, map_one, one_pow, one_mul] at hmap
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun y => y * a
      invFun := fun y => y * (d.map c)ᵀ
      left_inv := fun y => by simp only [Matrix.mul_assoc, had, Matrix.mul_one]
      right_inv := fun y => by simp only [Matrix.mul_assoc, hda, Matrix.mul_one]
      continuous_toFun := continuous_id.matrix_mul continuous_const
      continuous_invFun := continuous_id.matrix_mul continuous_const }
  have hdet : d.det = (c a.det)⁻¹ := by
    have h1 : a.det * c d.det = 1 := by
      have := congrArg Matrix.det had
      rw [det_mul, det_transpose, det_one] at this
      rw [← this]
      congr 1
      exact RingHom.map_det (c : E →+* E) d
    have h2 := congrArg c h1
    rw [map_mul, hE.invol, map_one] at h2
    exact eq_inv_of_mul_eq_one_right h2
  have hsc' := hsc (Matrix.GeneralLinearGroup.det A)
  have hAdet : ((Matrix.GeneralLinearGroup.det A : Eˣ) : E) = a.det := rfl
  rw [hAdet, ← hdet] at hsc'
  have hN : nabs F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) ≠ 0 :=
    (NNReal.coe_pos.mpr distribHaarChar_pos).ne'
  funext x
  have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by rw [← hβ, map_zero]
  have hint : ∫ y, ψ (pr c Q (x * d) (y * a)) * φ (y * a) ∂μ
      = (((nabs F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det A)) ^ Fintype.card α : ℝ) : ℂ))⁻¹
        * ∫ y, ψ (pr c Q (x * d) y) * φ y ∂μ := by
    have h1 := integral_map_equiv (μ := μ) e.toMeasurableEquiv (fun y => ψ (pr c Q (x * d) y) * φ y)
    have h2 : μ.map e.toMeasurableEquiv = _ := hmap
    rw [h2, integral_smul_nnreal_measure] at h1
    refine Eq.trans h1.symm ?_
    rw [NNReal.smul_def, Complex.real_smul]
    simp [nabs]
  have hpr : ∀ y : Matrix α ν E, pr c Q (x * d) (y * a) = pr c Q x y := fun y => by
    rw [← hβ, hadj, Matrix.mul_assoc, had, Matrix.mul_one, hβ]
  simp only [hpr] at hint
  simp only [fou, four, parFun, hb, hb', ha', ← ha, ← hd, Matrix.mul_zero, h0, mul_zero, AddChar.map_zero_eq_one, one_mul]
  simp only [mul_left_comm _ (sc F χ (Fintype.card α) a.det)]
  rw [integral_const_mul, hint, ← hsc', ← mul_assoc, mul_assoc (sc F χ _ d.det), mul_inv_cancel₀, mul_one]
  exact_mod_cast pow_ne_zero _ hN

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombination
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etaleLocally_weaken_freeSheafSections {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem free_sec_lin_sum {S X M : Type*} [Semiring S] [AddCommMonoid M] [Module S M]
    (φ : (X →₀ S) →ₗ[S] M) (x : X →₀ S) :
    (x.sum fun a r => r • φ (Finsupp.single a 1)) = φ x := by
  calc (x.sum fun a r => r • φ (Finsupp.single a 1))
      = x.sum fun a r => φ (Finsupp.single a r) := by
        refine Finsupp.sum_congr fun a _ => ?_
        rw [← map_smul, Finsupp.smul_single_one]
    _ = φ x := by rw [← map_finsuppSum, Finsupp.sum_single]

theorem free_sec_sum_eq (R : Type) [CommRing R] (P : PSh) (V : Scheme.{0})
    (x : ULift.{1} (P.obj (op V)) →₀ ULift.{1} R) :
    ((Finsupp.mapDomain ULift.down x).sum fun a r => r • freeGen R P V a) =
      ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom x := by
  rw [Finsupp.sum_mapDomain_index_inj ULift.down_injective]
  exact free_sec_lin_sum ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom x

theorem free_sec_loc : ∀ (R : Type) [CommRing R] (P : PSh) (U : Scheme.{0}), (∀ y : Sec ((free R).obj P) U, Loc U fun V g => ∃ c : P.obj (op V) →₀ ULift.{1} R, Sec.res g y = c.sum fun x r => r • freeGen R P V x) ∧ ∀ c : P.obj (op U) →₀ ULift.{1} R, (c.sum fun x r => r • freeGen R P U x) = 0 → Loc U fun _ g => Finsupp.mapDomain (P.map g.op) c = 0 := by
  intro R _ P U
  have base := GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift R ((freeP R).obj P)
  refine ⟨fun y => ?_, fun c hc => ?_⟩
  · refine etaleLocally_weaken_freeSheafSections (base.1 U y) ?_
    rintro V g ⟨x, hx⟩
    exact ⟨_, ((free_sec_sum_eq R P V x).trans hx).symm⟩
  · have hdu : Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up c) = c := by
      rw [← Finsupp.mapDomain_comp]
      exact Finsupp.mapDomain_id
    have h2 : ((Finsupp.mapDomain ULift.down (Finsupp.mapDomain ULift.up c)).sum
        fun a r => r • freeGen R P U a) = 0 := by
      rw [hdu]
      exact hc
    have hx := (free_sec_sum_eq R P U _).symm.trans h2
    refine etaleLocally_weaken_freeSheafSections (base.2.1 U _ hx) ?_
    intro V g hg
    have key : Finsupp.mapDomain ULift.down ((((freeP R).obj P).map g.op).hom
        (Finsupp.mapDomain ULift.up c)) = Finsupp.mapDomain (P.map g.op) c := by
      have e1 : (((freeP R).obj P).map g.op).hom (Finsupp.mapDomain ULift.up c) =
          Finsupp.mapDomain (fun a : ULift.{1} (P.obj (op U)) =>
            (ULift.up (P.map g.op a.down) : ULift.{1} (P.obj (op V)))) (Finsupp.mapDomain ULift.up c) := rfl
      rw [e1, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
      rfl
    rw [← key]
    exact (congrArg (Finsupp.mapDomain ULift.down) hg).trans Finsupp.mapDomain_zero

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomology_longExact_first_of_injective : ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x) := by
  first | (exact @GlobalTheory.EtC.longExact_first_of_injective) | (exact GlobalTheory.EtC.longExact_first_of_injective) | (intros; apply GlobalTheory.EtC.longExact_first_of_injective  <;> assumption)
end

