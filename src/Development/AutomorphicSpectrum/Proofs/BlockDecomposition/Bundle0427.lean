module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0252
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightPolynomialTraceIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFixedByInvolutionIsBase
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin

theorem sigR_fixed_eq_algebraMap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (a : K ⊗[F] E),
    sigR K σ a = a → ∃ x : K, algebraMap K (K ⊗[F] E) x = a := by
  intro F E _ _ _ _ _ σ h K _ _ a ha
  have hsigma (x : E) : σ (σ x) = x := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hmoved : ∃ y, σ y ≠ y := by
    by_contra hc
    push_neg at hc
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hc x] at this
      exact this.symm)
    have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
    exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal
  have hex : ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E),
      θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
    obtain ⟨y, hy⟩ := hmoved
    have hE2 : (2 : E) ≠ 0 := two_ne_zero
    have hσθ : σ (y - σ y) = -(y - σ y) := by
      rw [map_sub, hsigma]
      ring
    have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
    generalize y - σ y = θ at hσθ hθ
    have hli : LinearIndependent F ![(1 : E), θ] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      simp only [Algebra.smul_def, mul_one] at hst
      have h1 := congrArg σ hst
      simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ, map_zero] at h1
      have hs : (2 : E) * algebraMap F E s = 0 := by
        linear_combination hst + h1
      have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
        linear_combination hst - h1
      have hs0 : s = 0 := by
        have := (mul_eq_zero.1 hs).resolve_left hE2
        exact (map_eq_zero _).1 this
      have ht0 : t = 0 := by
        have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
        exact (map_eq_zero _).1 this
      exact ⟨hs0, ht0⟩
    let B : Module.Basis (Fin 2) F E :=
      basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
    have hB0 : B 0 = 1 := by simp [B]
    have hB1 : B 1 = θ := by simp [B]
    have hsum := B.sum_repr (θ * θ)
    rw [Fin.sum_univ_two, hB0, hB1] at hsum
    generalize B.repr (θ * θ) 0 = a at hsum
    generalize B.repr (θ * θ) 1 = b at hsum
    have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
      simpa only [Algebra.smul_def, mul_one] using hsum
    have hconj := congrArg σ hsum'
    simp only [map_add (f := _), map_mul, AlgHom.commutes, hσθ] at hconj
    have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
      linear_combination hsum' - hconj
    have hb0 : algebraMap F E b = 0 :=
      (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
    have hsq : θ * θ = algebraMap F E a := by
      rw [← hsum', hb0, zero_mul, add_zero]
    have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at hsq
      exact hθ (mul_self_eq_zero.1 hsq)
    exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩
  obtain ⟨θ, d, B, hθ, hd, hσθ, hsq, hB0, hB1⟩ := hex
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let C : Module.Basis (Fin 2) K (K ⊗[F] E) := Algebra.TensorProduct.basis K B
  have hC0 : C 0 = 1 := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB0]
    rfl
  have hC1 : C 1 = (1 : K) ⊗ₜ[F] θ := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB1]
  have hsK : ∀ x : K, sigR K σ (algebraMap K (K ⊗[F] E) x) = algebraMap K (K ⊗[F] E) x := by
    intro x
    change Algebra.TensorProduct.map (AlgHom.id F K) σ (algebraMap K (K ⊗[F] E) x) = _
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hsT : sigR K σ ((1 : K) ⊗ₜ[F] θ) = -((1 : K) ⊗ₜ[F] θ) := by
    change Algebra.TensorProduct.map (AlgHom.id F K) σ ((1 : K) ⊗ₜ[F] θ) = _
    rw [Algebra.TensorProduct.map_tmul, hσθ, TensorProduct.tmul_neg]
    rfl
  have hz := C.sum_repr a
  rw [Fin.sum_univ_two, hC0, hC1, Algebra.smul_def, Algebra.smul_def, mul_one] at hz
  generalize C.repr a 0 = x at hz
  generalize C.repr a 1 = y at hz
  subst hz
  rw [map_add (f := _), map_mul, hsK, hsK, hsT] at ha
  have h2 : algebraMap K (K ⊗[F] E) 0 + algebraMap K (K ⊗[F] E) (2 * y) * ((1 : K) ⊗ₜ[F] θ) = 0 := by
    rw [map_zero, map_mul, map_ofNat]
    linear_combination -ha
  have hl := Fintype.linearIndependent_iff.1 C.linearIndependent ![0, 2 * y] (by
    rw [Fin.sum_univ_two, hC0, hC1]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] using h2)
  have hy : y = 0 := by
    have := hl 1
    simp only [Matrix.cons_val_one] at this
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact ⟨x, by rw [hy, map_zero, zero_mul, add_zero]⟩

end GlobalTheory.CompanionTheory.KFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CapelliGelfand

theorem etr_eq_gelfVal_of_capelli :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
      (χ : Fin (m + 1) → ℂ) (v : V), Formalism.REAL.GlRel E →
      (∀ Y : ℂ, Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v) →
      ∀ k : ℕ, Formalism.REAL.etr E k v = GlobalTheory.Dec.gelfVal χ k • v := by
  intro V _ _ m E χ v hE hq
  have hcap : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP χ Y = ∏ s, (Y + χ s) := by
    intro Y
    rfl
  have hP : ∀ u : ℂ, Formalism.REAL.qdet E u v =
      (∏ s, (Polynomial.X + Polynomial.C (χ s - (m : ℂ) / 2))).eval u • v := by
    intro u
    have h := hq (u - (m : ℂ) / 2)
    have h1 : u - (m : ℂ) / 2 + (((m + 1 : ℕ) : ℂ) - 1) / 2 = u := by
      push_cast
      ring
    rw [h1, hcap] at h
    rw [h, Polynomial.eval_prod]
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    ring
  intro k
  induction k using Nat.strong_induction_on with
  | _ N ih =>
    rw [_root_.GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen V m E hE _ v hP N (fun k => GlobalTheory.Dec.gelfVal χ k) (fun k hk => ih k hk)]
    rw [_root_.GlobalTheory.CompanionTheory.GelfRec.gelfVal_newton m χ N]

end GlobalTheory.CompanionTheory.CapelliGelfand
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjugateEquivalence
section
noncomputable section

open NumberField Matrix
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open PositivityTheory.Rg.Tf.Loc (twConj TwConjugate)

namespace GlobalTheory.CompanionTheory.ClassBij

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjE_conjE (x : E) : conjE E (conjE E x) = x := by
  simp [PositivityTheory.Rg.BcB.conjE, NumberField.IsCMField.complexConj_apply_apply]

theorem thetaE_thetaE (g : GL (Fin n) E) : thetaE E n (thetaE E n g) = g := by
  apply Units.ext
  ext i j
  simp only [PositivityTheory.Rg.BcB.thetaE, PositivityTheory.Rg.BcB.thetaR_val, ← map_inv, inv_inv, Matrix.transpose_apply,
    Matrix.map_apply]
  exact conjE_conjE _

theorem nrm_twConj (g d : GL (Fin n) E) : nrm (twConj (thetaE E n) g d) = g⁻¹ * nrm d * g := by
  simp only [PositivityTheory.Rg.BcB.nrm, twConj, map_mul, map_inv, thetaE_thetaE]
  group

theorem charpoly_nrm_twConj (g d : GL (Fin n) E) :
    (nrm (twConj (thetaE E n) g d)).val.charpoly = (nrm d).val.charpoly := by
  rw [nrm_twConj, Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem isRegEll_twConj (g d : GL (Fin n) E) : IsRegEll (twConj (thetaE E n) g d) ↔ IsRegEll d := by
  simp only [PositivityTheory.Rg.BcB.IsRegEll, PositivityTheory.Rg.BcB.IsRegD, charpoly_nrm_twConj]

theorem twConjugate_equivalence : Equivalence (TwConjugate (thetaE E n)) := by
  refine ⟨fun x => ⟨1, by simp [twConj]⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp only [twConj, map_inv, inv_inv]
    group
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    refine ⟨g * h, ?_⟩
    simp only [twConj, map_mul, _root_.mul_inv_rev]
    group

theorem exists_out (y : GL (Fin n) E) :
    ∃ g, y = twConj (thetaE E n) g (Quot.out (Quot.mk (TwConjugate (thetaE E n)) y)) :=
  twConjugate_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq _))

theorem classBij : PositivityTheory.Rg.BcB.G8.ClassBij := by
  intro F _ _ _ m u hu
  have hθ : ∀ g : GL (Fin m) F, thE F m g = u * thetaE F m g * u⁻¹ := by
    obtain ⟨h, -⟩ := hu
    exact h
  let e : TwCl (thE F m) ≃ TwClass F m :=
    { toFun := Quot.map (fun x => x * u) (by
        rintro x y ⟨g, rfl⟩
        exact ⟨g, by simp only [twConj, hθ]; group⟩)
      invFun := Quot.map (fun x => x * u⁻¹) (by
        rintro x y ⟨g, rfl⟩
        exact ⟨g, by simp only [twConj, hθ]; group⟩)
      left_inv := by
        intro c
        induction c using Quot.ind with
        | mk x => exact congrArg (Quot.mk _) (mul_inv_cancel_right x u)
      right_inv := by
        intro c
        induction c using Quot.ind with
        | mk x => exact congrArg (Quot.mk _) (inv_mul_cancel_right x u) }
  refine ⟨e, fun c => ?_⟩
  have he : e c = Quot.mk (TwConjugate (thetaE F m)) (c.rep * u) := by
    have hc : c = Quot.mk _ c.rep := (Quot.out_eq c).symm
    calc e c = e (Quot.mk _ c.rep) := congrArg (⇑e) hc
      _ = _ := rfl
  obtain ⟨g, hg⟩ := exists_out (E := F) (n := m) (c.rep * u)
  have key := isRegEll_twConj g (Quot.out (Quot.mk (TwConjugate (thetaE F m)) (c.rep * u)))
  rw [← hg] at key
  rw [he]
  exact ⟨g, hg, key.symm⟩

end GlobalTheory.CompanionTheory.ClassBij

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
section
open Finset PositivityTheory.RgBcC.RealD
open CompanionTheory.D.LK (Pos key)

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

variable {n : ℕ}

theorem key_lt (i : Pos n) : key i < n * n := by
  obtain ⟨⟨a, b⟩, hab⟩ := i
  have ha := a.isLt
  have hb := b.isLt
  show (a : ℕ) * n + b < n * n
  calc (a : ℕ) * n + b < a * n + n := by omega
    _ = (a + 1) * n := by ring
    _ ≤ n * n := Nat.mul_le_mul_right _ ha

theorem keyL_inj {l m : Lt n} (h : keyL l = keyL m) : l = m := by
  obtain ⟨b1, p1⟩ := l
  obtain ⟨b2, p2⟩ := m
  have k1 := key_lt p1
  have k2 := key_lt p2
  have hk : key p1 = key p2 ∧ b1 = b2 := by
    simp only [keyL] at h
    cases b1 <;> cases b2 <;> simp at h ⊢ <;> omega
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨⟨a1, c1⟩, h1⟩ := p1
  obtain ⟨⟨a2, c2⟩, h2⟩ := p2
  have hc1 := c1.isLt
  have hc2 := c2.isLt
  have hn : 0 < n := by omega
  have hk' : (c1 : ℕ) + a1 * n = c2 + a2 * n := by
    have e : (a1 : ℕ) * n + c1 = a2 * n + c2 := hk
    linarith
  have ea : (a1 : ℕ) = a2 := by
    have := congrArg (· / n) hk'
    simpa [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc1, Nat.div_eq_of_lt hc2] using this
  have ec : (c1 : ℕ) = c2 := by
    have := congrArg (· % n) hk'
    simpa [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hc2] using this
  have e1 : a1 = a2 := Fin.ext ea
  have e2 : c1 = c2 := Fin.ext ec
  subst e1 e2
  rfl

def twL (l m : Lt n) : ℂ := if keyL m < keyL l then -1 else 1

theorem twL_self (l : Lt n) : twL l l = 1 := by simp [twL]

theorem twL_mul_self (l m : Lt n) : twL l m * twL l m = 1 := by
  unfold twL
  split_ifs <;> norm_num

theorem twL_swap {l m : Lt n} (h : l ≠ m) : twL m l = -twL l m := by
  have hk : keyL l ≠ keyL m := fun e => h (keyL_inj e)
  unfold twL
  split_ifs with h1 h2 h2
  · exfalso; omega
  · norm_num
  · norm_num
  · exfalso; omega

theorem sgL_mul_self (l : Lt n) (A : Finset (Lt n)) : sgL l A * sgL l A = 1 := by
  unfold sgL
  rw [← mul_pow]
  norm_num

theorem sgL_ne_zero (l : Lt n) (A : Finset (Lt n)) : sgL l A ≠ 0 := by
  unfold sgL
  exact pow_ne_zero _ (by norm_num)

theorem sgL_insert (l : Lt n) {m : Lt n} {A : Finset (Lt n)} (h : m ∉ A) :
    sgL l (insert m A) = twL l m * sgL l A := by
  unfold sgL twL
  rw [Finset.filter_insert]
  split_ifs with hk
  · rw [Finset.card_insert_of_notMem (fun hm => h (Finset.mem_filter.1 hm).1), pow_succ]; ring
  · simp

theorem sgL_erase (l : Lt n) {m : Lt n} {A : Finset (Lt n)} (h : m ∈ A) :
    sgL l (A.erase m) = twL l m * sgL l A := by
  have h1 := sgL_insert l (Finset.notMem_erase m A)
  rw [Finset.insert_erase h] at h1
  rw [h1, ← mul_assoc, twL_mul_self, one_mul]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem annL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    annL l x A = if l ∈ A then 0 else sgL l A • x (insert l A) := rfl

theorem creL_apply (l : Lt n) (x : Cq n V) (A : Finset (Lt n)) :
    creL l x A = if l ∈ A then sgL l A • x (A.erase l) else 0 := rfl

theorem liftL_apply {V' : Type} [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') (x : Cq n V) (A : Finset (Lt n)) :
    liftL n T x A = T (x A) := rfl

theorem annL_annL (i j : Lt n) : (annL i * annL j + annL j * annL i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    annL_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  · simp [hi]
  by_cases hj : j ∈ A
  · simp [hj]
  simp only [hi, hj, Finset.mem_insert, hij, hji, or_self, if_false]
  rw [sgL_insert j hi, sgL_insert i hj, twL_swap hij, Finset.insert_comm j i, smul_smul, smul_smul, ← add_smul]
  have : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem creL_creL (i j : Lt n) : (creL i * creL j + creL j * creL i : Module.End ℂ (Cq n V)) = 0 := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, LinearMap.zero_apply, Pi.zero_apply,
    creL_apply]
  by_cases hij : i = j
  · subst hij
    simp
  have hji : j ≠ i := fun e => hij e.symm
  by_cases hi : i ∈ A
  swap
  · simp [hi]
  by_cases hj : j ∈ A
  swap
  · simp [hj]
  simp only [hi, hj, Finset.mem_erase, ne_eq, hij, hji, not_false_eq_true, and_self, if_true]
  rw [sgL_erase j hi, sgL_erase i hj, twL_swap hij, Finset.erase_right_comm (a := j) (b := i), smul_smul, smul_smul,
    ← add_smul]
  have : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
  rw [this, zero_smul]

theorem annL_creL (i j : Lt n) :
    (annL i * creL j + creL j * annL i : Module.End ℂ (Cq n V)) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    refine LinearMap.ext fun x => funext fun A => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, Pi.add_apply, annL_apply, creL_apply,
      Module.End.one_apply]
    by_cases hi : i ∈ A
    · have h1 : i ∉ A.erase i := Finset.notMem_erase i A
      rw [if_pos hi, if_pos hi, if_neg h1, sgL_erase i hi, twL_self, one_mul, Finset.insert_erase hi,
        smul_smul, sgL_mul_self, one_smul, zero_add]
    · have h1 : i ∈ insert i A := Finset.mem_insert_self i A
      rw [if_neg hi, if_pos h1, if_neg hi, sgL_insert i hi, twL_self, one_mul, Finset.erase_insert hi,
        smul_smul, sgL_mul_self, one_smul, add_zero]
  · rw [if_neg hij]
    refine LinearMap.ext fun x => funext fun A => ?_
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.zero_apply, Pi.add_apply,
      Pi.zero_apply, annL_apply, creL_apply]
    by_cases hi : i ∈ A
    · have hi' : i ∈ A.erase j := Finset.mem_erase.2 ⟨hij, hi⟩
      simp [hi, hi']
    · by_cases hj : j ∈ A
      · have hj' : j ∈ insert i A := Finset.mem_insert_of_mem hj
        have hi' : i ∉ A.erase j := fun hm => hi (Finset.mem_of_mem_erase hm)
        rw [if_neg hi, if_pos hj', if_pos hj, if_neg hi', sgL_insert j hi, sgL_erase i hj,
          twL_swap hij, Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]
        have e : sgL i A * (-twL i j * sgL j A) + sgL j A * (twL i j * sgL i A) = 0 := by ring
        rw [e, zero_smul]
      · have hj' : j ∉ insert i A := by simp [hj, Ne.symm hij]
        simp [hi, hj, hj']

theorem annL_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : annL i x A ≠ 0) : i ∉ A ∧ x (insert i A) ≠ 0 := by
  rw [annL_apply] at h
  by_cases hi : i ∈ A
  · simp [hi] at h
  · refine ⟨hi, fun hx => h ?_⟩
    simp [hi, hx]

theorem creL_ne {i : Lt n} {x : Cq n V} {A : Finset (Lt n)} (h : creL i x A ≠ 0) : i ∈ A ∧ x (A.erase i) ≠ 0 := by
  rw [creL_apply] at h
  by_cases hi : i ∈ A
  · refine ⟨hi, fun hx => h ?_⟩
    simp [hi, hx]
  · simp [hi] at h

theorem liftL_annL (T : Module.End ℂ V) (l : Lt n) :
    ((liftL n T : Module.End ℂ (Cq n V)) * annL l : Module.End ℂ (Cq n V)) = annL l * (liftL n T : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, liftL_apply, annL_apply]
  split_ifs <;> simp [liftL_apply]

theorem liftL_creL (T : Module.End ℂ V) (l : Lt n) :
    ((liftL n T : Module.End ℂ (Cq n V)) * creL l : Module.End ℂ (Cq n V)) = creL l * (liftL n T : Module.End ℂ (Cq n V)) := by
  refine LinearMap.ext fun x => funext fun A => ?_
  simp only [Module.End.mul_apply, liftL_apply, creL_apply]
  split_ifs <;> simp [liftL_apply]

def adS (S : Lt n → Prop) (s : Bool) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  open Classical in ∑ l : Lt n, ∑ k : Lt n, if S l then adCL s p q l k • (creL k * annL l) else 0

def Lv (lev : Fin n → ℕ) (E1 E2 : Fin n → Fin n → Module.End ℂ V) (p q : Fin n) : Module.End ℂ (Cq n V) :=
  (liftL n (kA E1 E2 p q) : Module.End ℂ (Cq n V)) + adLL lev false p q

end GlobalTheory.CompanionTheory.LvChain
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightPolynomialTraceIdentityStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.Tope
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_polynomial_trace_identity : ∀ {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T →
    (⨆ μ, wtDual E μ) = ⊤ → iSupIndep (wtDual E) → ∀ s : Finset (Fin n → ℤ), (∀ μ, wtDual E μ ≠ ⊥ → μ ∈ s) →
      cPoly s (fun μ => trOn (wtDual E μ) (dualT E 1 : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * altL (delZ n) ^ 2 =
          pPL n * altL (lam + delZ n) ^ 2 ∧
        cPoly s (fun μ => trOn (wtDual E μ) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) * frL n (altL (delZ n)) =
          pPL n * frL n (altL (lam + delZ n)) := by
  first | exact @GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident | exact GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident | (intros; apply GlobalTheory.CompanionTheory.RealCount.Tope.Ident.lefK_laurent_ident <;> assumption)
end

