module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicCompletionCongruenceSubgroupsOpenCompactSmal
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergTranslateFixedIntegralUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CayleyTransformTrivialPhaseSkewHermitian
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0129
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdicCompletionCongruenceSubgroupsOpenCompactSmalStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_congruenceSubgroups_open_compact_small : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a l : ℕ), l.Prime → (l : 𝓞 E) ∈ w.asIdeal → (∀ m : ℕ, IsOpen (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) ∧ IsCompact (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E)))) ∧ ∀ N ∈ nhds (1 : GL (Fin a) (w.adicCompletion E)), ∀ᶠ m : ℕ in Filter.atTop, (((Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(l : w.adicCompletionIntegers E) ^ m}))).ker.map (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))) : Subgroup (GL (Fin a) (w.adicCompletion E))) : Set (GL (Fin a) (w.adicCompletion E))) ⊆ N := by
  first | exact @GlobalTheory.CongOpenSmall.congruence_open_compact_small | exact GlobalTheory.CongOpenSmall.congruence_open_compact_small | (intros; apply GlobalTheory.CongOpenSmall.congruence_open_compact_small; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspContragredientIsCMConjTwistOfPairedInvTranspStatement
section
open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  first | exact @GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | exact GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | (intros; apply GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTypeClosurePreservedByArchCompactIntertw
section
open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj

namespace GlobalTheory.IdemAdj

theorem typeClosure_of_intertwine : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  intro E _ _ _ a π W _ _ ρ₀ U hU hst f hf u hu hcoef g
  haveI := hU
  let w : Kinf E a → U := fun k => ⟨cptOn π k u, hst k u hu⟩
  let A : (U →ₗ[ℂ] ℂ) →ₗ[ℂ] (Kinf E a → ℂ) :=
    { toFun := fun ℓ k => ℓ (w k), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let ev : GA E a → (U →ₗ[ℂ] ℂ) := fun h =>
    (LinearMap.proj h).comp ((Sm E a).subtype.comp (π.V.subtype.comp U.subtype))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    haveI hfr : Module.Free ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      Module.Free.of_divisionRing ℂ _
    haveI : Module.Projective ℂ ((U →ₗ[ℂ] ℂ) ⧸ Submodule.span ℂ (Set.range ev)) :=
      @Module.Projective.of_free _ _ _ _ _ hfr
    refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
    by_contra hc
    push_neg at hc
    exact hz (Subtype.ext (Subtype.ext (Subtype.ext (funext fun h => hc _ ⟨h, rfl⟩))))
  let L : U →ₗ[ℂ] ℂ :=
    (LinearMap.proj g).comp ((Sm E a).subtype.comp (π.V.subtype.comp (f.comp U.subtype)))
  have hL : L ∈ (AutFin.coeffSpan ρ₀).comap A := by
    have hmem : L ∈ Submodule.span ℂ (Set.range ev) := hspan ▸ Submodule.mem_top
    refine (Submodule.span_le.2 ?_) hmem
    rintro _ ⟨h, rfl⟩
    exact hcoef h
  have key : (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) = A L := by
    funext k
    show _ = (f (cptOn π k u)).1.1 g
    rw [hf k u hu, cptOn_val]
  rw [key]
  exact hL

end GlobalTheory.IdemAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorSmallSubFiniteEigenApproxInequalityStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_small_sub_finite_eigen_approx_inequality : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  first | (exact @GlobalTheory.Cong.eigen_small_sub_finite_approx) | (exact GlobalTheory.Cong.eigen_small_sub_finite_approx) | (intros; apply GlobalTheory.Cong.eigen_small_sub_finite_approx  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorColumnsIndependentModUniformize
section
open Matrix

namespace GlobalTheory

theorem columns_indepMod :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (V : Matrix (Fin n) (Fin n) L) (a : Fin n → ℕ),
    (∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
      ((∀ i, (x *ᵥ (V *ᵥ c)) i ∈ Formalism.UG.intL L) ↔ ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j))) →
    GlobalTheory.Hk3.IntWitt.IndepMod ϖ (fun j : {j : Fin n // 0 < a j} => x *ᵥ (V *ᵥ Pi.single (j : Fin n) (ϖ ^ a (j : Fin n)))) := by
  intro L _ _ ϖ hϖ n n' x V a H d hd hdiv j
  classical
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hϖi : ϖ ∈ Formalism.UG.intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num
  set c : Fin n → L := fun k => if h : 0 < a k then d ⟨k, h⟩ * ϖ ^ (a k - 1) else 0 with hc
  have hcint : ∀ k, c k ∈ Formalism.UG.intL L := by
    intro k; simp only [hc]; split_ifs
    · exact mul_mem (hd _) (pow_mem hϖi _)
    · exact zero_mem _
  have hsum : ϖ • c = ∑ i : {j : Fin n // 0 < a j}, d i • Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)) := by
    funext k
    rw [Finset.sum_apply]
    by_cases hk : 0 < a k
    · rw [Finset.sum_eq_single ⟨k, hk⟩]
      · obtain ⟨m, hm⟩ : ∃ m, a k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk.ne'
        simp [hc, hk, hm]; ring
      · intro b _ hb
        have : k ≠ (b : Fin n) := fun h => hb (Subtype.ext h.symm)
        simp [Pi.single_apply, this]
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hc, hk]
      · intro i _
        have : k ≠ (i : Fin n) := fun h => hk (h ▸ i.2)
        simp [Pi.single_apply, this]
  have hlin : ϖ • (x *ᵥ (V *ᵥ c)) = ∑ i : {j : Fin n // 0 < a j}, d i • (x *ᵥ (V *ᵥ Pi.single (i : Fin n) (ϖ ^ a (i : Fin n)))) := by
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, hsum, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp [Matrix.mulVec_smul]
  have hw : ∀ r, (x *ᵥ (V *ᵥ c)) r ∈ Formalism.UG.intL L := by
    intro r
    obtain ⟨b, hb, hbe⟩ := hdiv r
    have h1 := congrFun hlin r
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h1
    rw [← h1, pow_one] at hbe
    rw [mul_left_cancel₀ hϖ0 hbe]; exact hb
  obtain ⟨b, hb, hbe⟩ := (H c hcint).1 hw j
  refine ⟨b, hb, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, a j = m + 1 := Nat.exists_eq_succ_of_ne_zero j.2.ne'
  simp only [hc, dif_pos j.2, hm, Nat.add_sub_cancel] at hbe
  apply mul_right_cancel₀ (pow_ne_zero m hϖ0)
  rw [hbe]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallDvdPow
section
open Matrix

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem eq_zero_of_forall_dvdPow {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hx : ∀ k, DvdPow ϖ (k + 1) x) : x = 0 := by
  by_contra h0
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have key : ∀ N : ℕ, Valued.v x ≤ WithZero.exp (-(N : ℤ)) := by
    intro N
    obtain ⟨b, hb, hxb⟩ := hx N
    rw [hxb, map_mul, map_pow, hϖ]
    calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
          mul_le_mul' le_rfl hb
      _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
          rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
      _ ≤ WithZero.exp (-(N : ℤ)) := WithZero.exp_le_exp.2 (by push_cast; omega)
  obtain ⟨m, hm⟩ : ∃ m, Valued.v x = WithZero.exp m := ⟨_, (WithZero.exp_log hv0).symm⟩
  have h1 := key ((-m).toNat + 1)
  rw [hm, WithZero.exp_le_exp] at h1
  have := Int.self_le_toNat (-m)
  push_cast at h1
  omega

end GlobalTheory.Hk3.IntWittBase

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem dvdPow_map {ϖ : L} {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσϖ : σ ϖ = ϖ) {m : ℕ} {a : L}
    (h : DvdPow ϖ m a) : DvdPow ϖ m (σ a) := by
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨σ b, ?_, by rw [map_mul, map_pow, hσϖ]⟩
  show Valued.v (σ b) ≤ 1
  rw [hσv]; exact hb

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cT_apply (σ : L →+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ A i j = σ (A j i) := rfl

theorem int_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L) (hB : ∀ i j, B i j ∈ intL L) :
    ∀ i j, (A * B) i j ∈ intL L := by
  intro i j; rw [Matrix.mul_apply]; exact Subring.sum_mem _ fun l _ => mul_mem (hA i l) (hB l j)

theorem int_cT {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ intL L) : ∀ i j, cT σ A i j ∈ intL L := by
  intro i j; rw [cT_apply]; show Valued.v (σ _) ≤ 1; rw [hσv]; exact hA j i

theorem mc_mul_left {ϖ : L} {n m : ℕ} {A D : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, A i j ∈ intL L)
    (hD : ∀ i j, DvdPow ϖ m (D i j)) : ∀ i j, DvdPow ϖ m ((A * D) i j) := by
  intro i j; rw [Matrix.mul_apply]; exact dvdPow_sum _ _ fun l _ => dvdPow_mul_int (hD l j) (hA i l)

theorem mc_mul_right {ϖ : L} {n m : ℕ} {D B : Matrix (Fin n) (Fin n) L} (hD : ∀ i j, DvdPow ϖ m (D i j))
    (hB : ∀ i j, B i j ∈ intL L) : ∀ i j, DvdPow ϖ m ((D * B) i j) := by
  intro i j; rw [Matrix.mul_apply]
  exact dvdPow_sum _ _ fun l _ => by rw [mul_comm]; exact dvdPow_mul_int (hD i l) (hB l j)

theorem mc_cT {ϖ : L} {σ : L →+* L} (hσv : ∀ x, Valued.v (σ x) = Valued.v x) (hσϖ : σ ϖ = ϖ) {n m : ℕ}
    {D : Matrix (Fin n) (Fin n) L} (hD : ∀ i j, DvdPow ϖ m (D i j)) : ∀ i j, DvdPow ϖ m (cT σ D i j) := by
  intro i j; rw [cT_apply]; exact dvdPow_map hσv hσϖ (hD j i)

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cT_sub (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) : cT σ (A - B) = cT σ A - cT σ B := by
  ext i j; simp [cT_apply]

end GlobalTheory.Hk3.IntWittBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsElementaryDivisorsIntegralPreimageLattice
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.IntWitt.ElemDiv

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_int {m k : ℕ} {A : Matrix (Fin m) (Fin k) L} (hA : ∀ i j, A i j ∈ Formalism.UG.intL L)
    {c : Fin k → L} (hc : ∀ j, c j ∈ Formalism.UG.intL L) : ∀ i, (A *ᵥ c) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hc j)

theorem diag_mulVec_of_lt {n n' : ℕ} (ϖ : L) (a : Fin n' → ℕ) (c : Fin n → L) (j : Fin n) (hj : (j : ℕ) < n') :
    ((Matrix.of fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) *ᵥ c) ⟨j, hj⟩ =
      (if 0 < a ⟨j, hj⟩ then ϖ⁻¹ ^ a ⟨j, hj⟩ else 0) * c j := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have : ¬ ((j : ℕ) = (b : ℕ)) := fun h => hb (Fin.ext h.symm)
    simp [this]
  · simp

theorem diag_mulVec_of_ge {n n' : ℕ} (ϖ : L) (a : Fin n' → ℕ) (c : Fin n → L) (i : Fin n') (hi : ¬ (i : ℕ) < n) :
    ((Matrix.of fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) *ᵥ c) i = 0 := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  apply Finset.sum_eq_zero
  intro b _
  have : ¬ ((i : ℕ) = (b : ℕ)) := fun h => hi (h ▸ b.isLt)
  simp [this]

end GlobalTheory.Hk3.IntWitt.ElemDiv

end


open GlobalTheory.Hk3.IntWitt.ElemDiv in
theorem GlobalTheory.Hk3.IntWitt.exists_glInt_mulVec_mem_iff_forall_dvdPow : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L),
    Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L),
    ∃ V : GL (Fin n) L, V ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧ ∃ a : Fin n → ℕ,
      ∀ c : Fin n → L, (∀ j, c j ∈ Formalism.UG.intL L) →
        ((∀ i, (x *ᵥ ((V : Matrix (Fin n) (Fin n) L) *ᵥ c)) i ∈ Formalism.UG.intL L) ↔
          ∀ j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (a j) (c j)) := by
  intro L _ _ ϖ hϖ n n' x
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  obtain ⟨P, P', Q, Q', a, hP, hP', hPP', hQ, hQ', hQQ', hE⟩ := GlobalTheory.Hk3.smith_int_approx L ϖ hϖ n n' x
  have hQ'Q : Q' * Q = 1 := mul_eq_one_comm.mp hQQ'
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  set O := Formalism.UG.intL L with hOdef
  let QO : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨Q i j, hQ i j⟩
  let QO' : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨Q' i j, hQ' i j⟩
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) L) := by
    intro A B h; ext i j; exact congrFun (congrFun h i) j
  have hm1 : O.subtype.mapMatrix QO = Q := by ext i j; rfl
  have hm2 : O.subtype.mapMatrix QO' = Q' := by ext i j; rfl
  have e1 : QO * QO' = 1 := hinj (by rw [map_mul, map_one, hm1, hm2, hQQ'])
  have e2 : QO' * QO = 1 := hinj (by rw [map_mul, map_one, hm1, hm2, hQ'Q])
  let U : GL (Fin n) O := ⟨QO, QO', e1, e2⟩
  let V : GL (Fin n) L := ⟨Q, Q', hQQ', hQ'Q⟩
  refine ⟨V, ⟨U, Units.ext hm1⟩, fun j => if h : (j : ℕ) < n' then a ⟨j, h⟩ else 0, ?_⟩
  intro c hc
  set Dm : Matrix (Fin n') (Fin n) L :=
    Matrix.of (fun (i : Fin n') (j : Fin n) => if (i : ℕ) = (j : ℕ) ∧ 0 < a i then ϖ⁻¹ ^ a i else 0) with hDm
  have hPw : P *ᵥ (x *ᵥ (Q *ᵥ c)) = Dm *ᵥ c + (P * x * Q - Dm) *ᵥ c := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hEc : ∀ i, ((P * x * Q - Dm) *ᵥ c) i ∈ O := mulVec_int hE hc
  show (∀ i, (x *ᵥ (Q *ᵥ c)) i ∈ O) ↔ _
  constructor
  · intro hw j
    have hDc : ∀ i, (Dm *ᵥ c) i ∈ O := by
      intro i
      have h1 := mulVec_int hP hw i
      rw [hPw, Pi.add_apply] at h1
      have := Subring.sub_mem _ h1 (hEc i)
      rwa [add_sub_cancel_right] at this
    by_cases hj : (j : ℕ) < n'
    · simp only [dif_pos hj]
      have h2 := hDc ⟨j, hj⟩
      rw [hDm, diag_mulVec_of_lt ϖ a c j hj] at h2
      split_ifs at h2 with ha
      · refine ⟨ϖ⁻¹ ^ a ⟨j, hj⟩ * c j, h2, ?_⟩
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hϖ0, one_pow, one_mul]
      · have : a ⟨j, hj⟩ = 0 := by omega
        rw [this]; exact dvdPow_zero_iff.mpr (hc j)
    · simp only [dif_neg hj]; exact dvdPow_zero_iff.mpr (hc j)
  · intro hd
    have hDc : ∀ i, (Dm *ᵥ c) i ∈ O := by
      intro i
      by_cases hi : (i : ℕ) < n
      · have hij : i = ⟨((⟨i, hi⟩ : Fin n) : ℕ), i.isLt⟩ := Fin.ext rfl
        rw [hij, hDm, diag_mulVec_of_lt ϖ a c ⟨i, hi⟩ i.isLt]
        split_ifs with ha
        · have h3 := hd ⟨i, hi⟩
          simp only [dif_pos i.isLt] at h3
          obtain ⟨b, hb, hcb⟩ := h3
          rw [hcb, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hϖ0, one_pow, one_mul]; exact hb
        · rw [zero_mul]; exact Subring.zero_mem _
      · rw [hDm, diag_mulVec_of_ge ϖ a c i hi]; exact Subring.zero_mem _
    have hPwi : ∀ i, (P *ᵥ (x *ᵥ (Q *ᵥ c))) i ∈ O := by
      intro i; rw [hPw, Pi.add_apply]; exact Subring.add_mem _ (hDc i) (hEc i)
    intro i
    have key : ∀ w : Fin n' → L, w = P' *ᵥ (P *ᵥ w) := fun w => by
      rw [Matrix.mulVec_mulVec, hP'P, Matrix.one_mulVec]
    rw [key (x *ᵥ (Q *ᵥ c))]; exact mulVec_int hP' hPwi i
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntGramOfFixed
section
noncomputable section
namespace GlobalTheory.Hk3.HoweDuality

theorem exists_int_gram_of_fixed : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L)
    (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M)
    (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), GlobalTheory.Hk3.LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ s : M, s ≠ 0 → GlobalTheory.Hk3.LocVac ρ s →
    Submodule.span ℂ (Set.range fun x => ρ x s) = ⊤ → ∀ x : Matrix (Fin n') (Fin n) L,
    (∃ w : M, w ≠ 0 ∧ (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) ∧
      w ∈ Submodule.span ℂ {v : M | ∃ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) ∧
          v = ρ (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x) s}) →
    ∃ l ∈ GlobalTheory.Hk3.HoweDuality.intMat L n' n,
      ∀ i j, ((x - l) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose ((x - l).map σ)) i j ∈ Formalism.UG.intL L := by
  intro L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hP s hs0 hs hspan x hw
  obtain ⟨hne, hfx⟩ := _root_.GlobalTheory.Hk3.class_fixed_phase L ϖ σ q δ n n' JS JT ψ M ρ ω hP s hs x hw
  have Hph : ∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
      (∀ i j, (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) i j ∈ Formalism.UG.intL L) →
      ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) = 1 := by
    intro h hh hint
    have e := congrArg (fun T : Module.End ℂ M => T s) (hP.rho_mul x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))
    simp only [Module.End.mul_apply, LinearMap.smul_apply, hs _ hint, add_sub_cancel, hfx h hh hint] at e
    have e2 : (ψ ((GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x) + σ (GlobalTheory.Hk3.locH σ δ JS JT x (((h : GL (Fin n') L) : Matrix (Fin n') (Fin n') L) * x - x))) / 2) - 1) • ρ x s = 0 := by
      rw [sub_smul, one_smul, ← e, sub_self]
    rcases smul_eq_zero.1 e2 with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hne
  exact _root_.GlobalTheory.Hk3.HoweDuality.exists_int_gram_of_phases L ϖ σ q δ n n' JS ψ hP.unr hP.odd hP.intS hP.hermS hP.delta hP.psi_int hP.psi_ne x
    (_root_.GlobalTheory.Hk3.CayleyPhase.cayley_phase L ϖ σ q δ n n' JS JT ψ hP.unr hP.odd hP.intS hP.intT hP.hermS hP.hermT hP.delta hP.psi_int x Hph)
end GlobalTheory.Hk3.HoweDuality
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMulConjEqOfUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host Formalism.L2.Col Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.NormOneHilbert90Units

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ne_zero_mul_conj_eq_of_unitary (D : D7) (z : unitary D.host.E) :
    ∃ w : D.host.E, w ≠ 0 ∧ (z : D.host.E) * D.host.conj w = w := by
  have hz : (z : D.host.E) * star (z : D.host.E) = 1 := z.2.2
  have key : ∀ a : D.host.E, (z : D.host.E) * star (a + (z : D.host.E) * star a) = a + (z : D.host.E) * star a := by
    intro a
    rw [star_add, star_mul, star_star]
    linear_combination a * hz
  obtain ⟨x, hx⟩ : ∃ x : D.host.E, star x ≠ x := by
    by_contra h
    push_neg at h
    apply NumberField.IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    rw [← Formalism.BasicNotions.Examples₂.cmStar_apply]
    exact h x
  by_cases h1 : (1 : D.host.E) + (z : D.host.E) * star (1 : D.host.E) = 0
  · refine ⟨x + (z : D.host.E) * star x, ?_, ?_⟩
    · intro h2
      have hz1 : (z : D.host.E) = -1 := by rw [star_one] at h1; linear_combination h1
      rw [hz1] at h2
      exact hx (by linear_combination -h2)
    · rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key x
  · exact ⟨_, h1, by rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key 1⟩

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

end Comparison₂

end GlobalTheory.NormOneHilbert90Units
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.Gam0
section
noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def gam (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add (f := _), ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

def gam0 (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ (e k + e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add (f := _), ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

end GlobalTheory.Hk3.GramSep

end
end

