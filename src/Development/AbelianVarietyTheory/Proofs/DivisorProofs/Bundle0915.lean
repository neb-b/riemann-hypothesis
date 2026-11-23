module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankJointEigenspaceAddConjEqMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section

namespace GlobalTheory.UPel.HT.LieType.DimSum

theorem finrank_eq_two_mul_of_period {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hdisc : DiscreteTopology Q.range)
    (hspan : Submodule.span ℝ (Set.range Q) = ⊤) : Module.finrank ℤ La = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g → ℂ)) = Set.range Q := by ext x; simp [L]
    rw [this]; exact hspan⟩
  have h1 := ZLattice.rank ℝ L
  have e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj |>.trans
    (LinearEquiv.ofEq _ _ (by ext x; simp [L]))
  rw [e.finrank_eq, h1, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, Finset.sum_const, mul_comm]

theorem trace_real_restrict (g : ℕ) (M : Matrix (Fin g) (Fin g) ℂ) :
    LinearMap.trace ℝ (Fin g → ℂ) ((Matrix.toLin' M).restrictScalars ℝ) = 2 * M.trace.re := by
  classical
  let b := Pi.basisFun ℂ (Fin g)
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower b)]
  have : M.trace = LinearMap.trace ℂ _ (Matrix.toLin' M) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b]; simp [b]
  rw [this, LinearMap.trace_eq_matrix_trace ℂ b]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, Finset.mul_sum, two_mul,
    Finset.sum_add_distrib]

theorem trace_int_eq_of_period {La : Type} [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ) (A : La →+ La) (hinj : Function.Injective Q)
    (hdisc : DiscreteTopology Q.range) (hspan : Submodule.span ℝ (Set.range Q) = ⊤)
    (hA : ∀ x, Q (A x) = M *ᵥ Q x) :
    ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℂ) = M.trace + (starRingEnd ℂ) M.trace := by
  classical
  let L : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule Q.range
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨by
    have : (L : Set (Fin g → ℂ)) = Set.range Q := by ext x; simp [L]
    rw [this]; exact hspan⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj |>.trans
    (LinearEquiv.ofEq _ _ (by ext x; simp [L]))
  have he : ∀ x, ((e x : L) : Fin g → ℂ) = Q x := fun x => rfl
  let b := Module.Free.chooseBasis ℤ La
  let bL := b.map e
  let bR := bL.ofZLatticeBasis ℝ L
  have hbR : ∀ i, bR i = Q (b i) := by
    intro i; simp [bR, bL, Module.Basis.ofZLatticeBasis_apply, he]
  have hmat : LinearMap.toMatrix bR bR ((Matrix.toLin' M).restrictScalars ℝ) =
      (LinearMap.toMatrix b b A.toIntLinearMap).map (Int.cast : ℤ → ℝ) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have h1 : (Matrix.toLin' M).restrictScalars ℝ (bR j) = Q (A (b j)) := by
      rw [hbR, hA]; rfl
    rw [h1]
    have h2 : Q (A (b j)) = ∑ k, (b.repr (A (b j)) k : ℝ) • bR k := by
      conv_lhs => rw [← b.sum_repr (A (b j))]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul, hbR]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ]
    rw [h2, bR.repr_sum_self]
    rfl
  have htr : (LinearMap.trace ℝ _ ((Matrix.toLin' M).restrictScalars ℝ)) =
      ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℝ) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ bR, hmat, LinearMap.trace_eq_matrix_trace ℤ b]
    simp [Matrix.trace]
  rw [trace_real_restrict] at htr
  have : ((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℂ) = (((LinearMap.trace ℤ La A.toIntLinearMap : ℤ) : ℝ) : ℂ) :=
    (Complex.ofReal_intCast _).symm
  rw [this, ← htr, Complex.add_conj]

theorem coeff_eq_zero_of_sum_embeddings {F : Type} [Field F] [NumberField F] (a : (F →+* ℂ) → ℂ)
    (h : ∀ c : 𝓞 F, ∑ τ : F →+* ℂ, a τ * τ (c : F) = 0) (τ : F →+* ℂ) : a τ = 0 := by
  let r : (F →+* ℂ) → (𝓞 F →* ℂ) := fun σ => (σ.comp (algebraMap (𝓞 F) F)).toMonoidHom
  have hr : Function.Injective r := by
    intro σ σ' hs
    have : σ.comp (algebraMap (𝓞 F) F) = σ'.comp (algebraMap (𝓞 F) F) := by
      ext x; exact DFunLike.congr_fun hs x
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) this
  have hli : LinearIndependent ℂ (fun σ : F →+* ℂ => ((r σ : 𝓞 F →* ℂ) : 𝓞 F → ℂ)) :=
    (linearIndependent_monoidHom (𝓞 F) ℂ).comp r hr
  have hsum : ∑ σ, a σ • ((r σ : 𝓞 F →* ℂ) : 𝓞 F → ℂ) = 0 := by
    funext c
    simpa [r, Finset.sum_apply] using h c
  exact (Fintype.linearIndependent_iff.mp hli) a hsum τ

theorem _root_.GlobalTheory.UPel.HT.LieType.finrank_eigSp_add_conj_eq (p : ℕ) [Fact p.Prime] (D : Datum p) (D' : PLat D.O D.inv)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q : D'.La →+ (Fin D.g → ℂ)) (hQ : IsPeriod D' ρ Q)
    (τ : D.F →+* ℂ) :
    Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) τ) +
      Module.finrank ℂ (eigSp (ρ.comp (algebraMap (𝓞 D.F) D.O)) ((starRingEnd ℂ).comp τ)) = D.m * D.n := by
  set φ := ρ.comp (algebraMap (𝓞 D.F) D.O) with hφ
  let d : (D.F →+* ℂ) → ℕ := fun σ => Module.finrank ℂ (eigSp φ σ)
  obtain ⟨hlin, hinj, hdisc, hspan, -⟩ := hQ

  have hrank : Module.finrank ℤ D'.La = (D.m * D.n) * Module.finrank ℚ D.F := by
    rw [finrank_eq_two_mul_of_period Q hinj hdisc hspan]
    have h2 : Module.finrank ℚ D.F = 2 * InfinitePlace.nrComplexPlaces D.F := IsTotallyComplex.finrank D.F
    unfold Datum.g
    rw [h2]
    rw [show D.m * D.n * (2 * InfinitePlace.nrComplexPlaces D.F) = 2 * (D.m * D.n * InfinitePlace.nrComplexPlaces D.F) by ring]
    rw [Nat.mul_div_cancel_left _ (by norm_num)]

  let cj : (D.F →+* ℂ) ≃ (D.F →+* ℂ) :=
    { toFun := fun σ => (starRingEnd ℂ).comp σ
      invFun := fun σ => (starRingEnd ℂ).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  have key : ∀ c : 𝓞 D.F, ∑ σ : D.F →+* ℂ, (((d σ + d (cj σ) : ℕ) : ℂ) - ((D.m * D.n : ℕ) : ℂ)) * σ (c : D.F) = 0 := by
    intro c
    let A : D'.La →+ D'.La := DistribSMul.toAddMonoidHom D'.La (algebraMap (𝓞 D.F) D.O c)
    have hA : ∀ x, Q (A x) = φ c *ᵥ Q x := fun x => hlin _ x
    have h1 := trace_int_eq_of_period Q (φ c) A hinj hdisc hspan hA
    have h2 := _root_.GlobalTheory.LatticeTrace.trace_lattice_eq D.F D.O D'.La (D.m * D.n) hrank c
    have h3 := GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace D.F D.g φ c
    have hconj : (starRingEnd ℂ) (φ c).trace = ∑ σ : D.F →+* ℂ, (d (cj σ) : ℂ) * σ (c : D.F) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h3, map_sum]
      simp only [map_mul, Complex.conj_natCast]
      exact (Fintype.sum_equiv cj _ _ (fun σ => by
        show (d σ : ℂ) * (starRingEnd ℂ) (σ (c : D.F)) = (d (cj (cj σ)) : ℂ) * (cj σ) (c : D.F)
        have : cj (cj σ) = σ := cj.left_inv σ
        rw [this]; rfl))
    have : ∑ σ : D.F →+* ℂ, ((d σ + d (cj σ) : ℕ) : ℂ) * σ (c : D.F) = ((D.m * D.n : ℕ) : ℂ) * ∑ σ : D.F →+* ℂ, σ (c : D.F) := by
      rw [← h2, h1, hconj, h3, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun σ _ => ?_
      push_cast; ring
    rw [Finset.mul_sum] at this
    simp only [sub_mul, Finset.sum_sub_distrib, this]
    simp
  have := coeff_eq_zero_of_sum_embeddings _ key τ
  have h' : ((d τ + d (cj τ) : ℕ) : ℂ) = ((D.m * D.n : ℕ) : ℂ) := sub_eq_zero.mp this
  exact_mod_cast h'

end GlobalTheory.UPel.HT.LieType.DimSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FischerPairingAdjointMixedLower
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.SDown

theorem pderiv_aeval_sum {σ δ : Type} [Fintype σ] [DecidableEq σ] (f : σ → MvPolynomial δ ℂ) (i : δ)
    (G : MvPolynomial σ ℂ) : pderiv i (aeval f G) = ∑ u, pderiv i (f u) * aeval f (pderiv u G) := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), aeval_X, hp, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro b _ hb
        rw [pderiv_X_of_ne hb.symm]; simp
      · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring

theorem derivation_finset_prod {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι]
    (D : Derivation R A A) (f : ι → A) (s : Finset ι) :
    D (∏ j ∈ s, f j) = ∑ i ∈ s, ∏ j ∈ s, Function.update f i (D (f i)) j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha, Finset.prod_insert ha,
      Function.update_self]
    have h1 : ∏ j ∈ s, Function.update f a (D (f a)) j = ∏ j ∈ s, f j := by
      refine Finset.prod_congr rfl fun j hj => ?_
      exact Function.update_of_ne (by rintro rfl; exact ha hj) _ _
    have h2 : ∀ i ∈ s, ∏ j ∈ insert a s, Function.update f i (D (f i)) j =
        f a * ∏ j ∈ s, Function.update f i (D (f i)) j := by
      intro i hi
      rw [Finset.prod_insert ha, Function.update_of_ne (by rintro rfl; exact ha hi)]
    rw [h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, smul_eq_mul, smul_eq_mul]
    ring

theorem derivation_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : Type*} [Fintype n] [DecidableEq n]
    (D : Derivation R A A) (M : Matrix n n A) :
    D M.det = ∑ i, (M.updateRow i fun j => D (M i j)).det := by
  have key : ∀ B : Matrix n n A, B.det = ∑ σ : Equiv.Perm n, Equiv.Perm.sign σ • ∏ i, B i (σ i) := by
    intro B
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, map_sum]
  simp_rw [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivation_finset_prod, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Units.smul_def]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    simp [Matrix.updateRow_self]
  · rw [Function.update_of_ne hj, Matrix.updateRow_ne hj]

theorem derivation_sum_apply {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} (s : Finset ι)
    (D : ι → Derivation R A A) (x : A) : (∑ t ∈ s, D t) x = ∑ t ∈ s, D t x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

variable {P Q S : ℕ}

theorem pderiv_u_mS (a : Fin P) (c : Fin S) (a0 : Fin P) (b0 : Fin Q) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (mS P Q S a0 b0) =
      if a0 = a then X (Sum.inr b0, Sum.inr c) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pderiv_t_mS (b : Fin Q) (c : Fin S) (a0 : Fin P) (b0 : Fin Q) :
    pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (mS P Q S a0 b0) =
      if b0 = b then X (Sum.inl a0, Sum.inr c) else 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [mS, map_sum, Derivation.leibniz, pderiv_X, Pi.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem pderiv_u_detS (h : Q ≤ S) (a : Fin P) (c : Fin S) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (detS P Q S h) = 0 := by
  classical
  rw [detS, derivation_det]
  refine Finset.sum_eq_zero fun i _ => Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
  simp [pderiv_X, Pi.single_apply]

theorem sum_X_pderiv_detS (h : Q ≤ S) (b b' : Fin Q) :
    ∑ c : Fin S, X ((Sum.inr b', Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b, Sum.inr c) (detS P Q S h) =
      if b' = b then detS P Q S h else 0 := by
  classical
  let Dd : Derivation ℂ (Pol P Q 0 S) (Pol P Q 0 S) :=
    ∑ c : Fin S, (X (Sum.inr b', Sum.inr c) : Pol P Q 0 S) • pderiv (Sum.inr b, Sum.inr c)
  have hD : ∀ p, Dd p = ∑ c : Fin S, X ((Sum.inr b', Sum.inr c) : Ln P Q 0 S) * pderiv (Sum.inr b, Sum.inr c) p := by
    intro p; simp only [Dd, derivation_sum_apply, Derivation.smul_apply, smul_eq_mul]
  rw [← hD, detS, derivation_det]
  have hrow : ∀ i j : Fin Q, Dd ((Matrix.of fun b c : Fin Q => (X (Sum.inr b, Sum.inr (Fin.castLE h c)) : Pol P Q 0 S)) i j) =
      if i = b then X (Sum.inr b', Sum.inr (Fin.castLE h j)) else 0 := by
    intro i j
    rw [hD]
    by_cases hi : i = b
    · subst hi; simp [pderiv_X, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']
    · simp [pderiv_X, Pi.single_apply, hi]
  simp_rw [hrow]
  rw [Finset.sum_eq_single b]
  · simp only [if_true]
    split_ifs with hb
    · subst hb
      congr 1
      ext i j
      by_cases hi : i = b' <;> simp [Matrix.updateRow_apply, hi]
    · refine Matrix.det_zero_of_row_eq hb ?_
      ext j
      simp [Matrix.updateRow_apply, Ne.symm hb]
  · intro i _ hi
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    simp [hi]
  · simp

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair.SDown

variable {P Q S : ℕ}

theorem pderiv_u_aeval (a : Fin P) (c : Fin S) (H : Mdl P Q) :
    pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) H) =
      ∑ b0 : Fin Q, X (Sum.inr b0, Sum.inr c) * aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a, b0) H) := by
  classical
  rw [pderiv_aeval_sum, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [pderiv_u_mS]
  · intro a0 _ ha0; simp [pderiv_u_mS, ha0]
  · simp

theorem pderiv_t_aeval (b : Fin Q) (c : Fin S) (H : Mdl P Q) :
    pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) H) =
      ∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) * aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a0, b) H) := by
  classical
  rw [pderiv_aeval_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  rw [Finset.sum_eq_single b]
  · simp [pderiv_t_mS]
  · intro b0 _ hb0; simp [pderiv_t_mS, hb0]
  · simp

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair.SDown

variable {P Q S : ℕ}

theorem rhs_eq (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G) =
      (∑ a0 : Fin P, ∑ b0 : Fin Q, mS P Q S a0 b0 *
          aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a0, b) (pderiv (a, b0) G)) +
        ((S + k' : ℕ) : ℂ) • aeval (fun ab : Fin P × Fin Q => mS P Q S ab.1 ab.2) (pderiv (a, b) G)) *
        detS P Q S h ^ k' := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [embS, opS, mulM, derM, LinearMap.sum_apply, map_sum, Module.End.mul_apply]

theorem key (h : Q ≤ S) (k' : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin S, pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (pderiv (Sum.inl a, Sum.inr c) (embS P Q S h k' G)) =
      embS P Q S h k' (opS P Q S k' (Sum.inr b) (Sum.inl a) G) := by
  classical
  rw [rhs_eq]
  set m : Fin P × Fin Q → Pol P Q 0 S := fun ab => mS P Q S ab.1 ab.2 with hm
  set D := detS P Q S h with hDdef
  have hE : embS P Q S h k' G = aeval m G * D ^ k' := by simp [embS, hm, hDdef]
  have step1 : ∀ c : Fin S, pderiv ((Sum.inl a, Sum.inr c) : Ln P Q 0 S) (embS P Q S h k' G) =
      ∑ b0 : Fin Q, X (Sum.inr b0, Sum.inr c) * aeval m (pderiv (a, b0) G) * D ^ k' := by
    intro c
    rw [hE, Derivation.leibniz, Derivation.leibniz_pow, hDdef, pderiv_u_detS, hm, pderiv_u_aeval]
    simp only [mul_zero, smul_zero, zero_add, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    ring
  have step2 : ∀ (c : Fin S) (b0 : Fin Q),
      pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) (X (Sum.inr b0, Sum.inr c) * aeval m (pderiv (a, b0) G) * D ^ k') =
        (if b0 = b then aeval m (pderiv (a, b) G) * D ^ k' else 0) +
        X (Sum.inr b0, Sum.inr c) * (∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) *
            aeval m (pderiv (a0, b) (pderiv (a, b0) G))) * D ^ k' +
        aeval m (pderiv (a, b0) G) * ((k' : Pol P Q 0 S) * D ^ (k' - 1)) *
          (X (Sum.inr b0, Sum.inr c) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D) := by
    intro c b0
    rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow, hm, pderiv_t_aeval, pderiv_X, Pi.single_apply]
    simp only [smul_eq_mul, nsmul_eq_mul, Prod.mk.injEq, Sum.inr.injEq, and_true]
    by_cases hb : b0 = b
    · subst hb
      simp only [if_true]
      ring
    · simp only [hb, if_false]
      ring
  have hT1 : ∑ c : Fin S, ∑ b0 : Fin Q, X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * (∑ a0 : Fin P, X (Sum.inl a0, Sum.inr c) *
      aeval m (pderiv (a0, b) (pderiv (a, b0) G))) * D ^ k' =
      ∑ a0 : Fin P, ∑ b0 : Fin Q, mS P Q S a0 b0 * aeval m (pderiv (a0, b) (pderiv (a, b0) G)) * D ^ k' := by
    simp only [mS, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b0 _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a0 _ => Finset.sum_congr rfl fun c _ => by ring
  have hT3 : ∑ c : Fin S, ∑ b0 : Fin Q, aeval m (pderiv (a, b0) G) * ((k' : Pol P Q 0 S) * D ^ (k' - 1)) *
      (X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D) =
      (k' : Pol P Q 0 S) * aeval m (pderiv (a, b) G) * D ^ k' := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have e : ∀ b0 : Fin Q, ∑ c : Fin S, X ((Sum.inr b0, Sum.inr c) : Ln P Q 0 S) * pderiv ((Sum.inr b, Sum.inr c) : Ln P Q 0 S) D =
        if b0 = b then D else 0 := fun b0 => by rw [hDdef]; exact sum_X_pderiv_detS h b b0
    simp only [e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rcases k' with _ | k
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]; ring
  have hT0 : ∑ c : Fin S, ∑ b0 : Fin Q, (if b0 = b then aeval m (pderiv (a, b) G) * D ^ k' else 0) =
      (S : Pol P Q 0 S) * aeval m (pderiv (a, b) G) * D ^ k' := by
    simp [Finset.sum_ite_eq', mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [step1, map_sum, step2, Finset.sum_add_distrib]
  rw [hT0, hT1, hT3, Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul, add_mul, Finset.sum_mul]
  simp only [Finset.sum_mul]
  push_cast
  ring

end GlobalTheory.CharPair.SDown

namespace GlobalTheory.CharPair

end GlobalTheory.CharPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionCommutesWithEmbedding
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem fockAct1_Eab_inl_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (a : Fin P) (b : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inl a) (Sum.inr b)) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inl a) (Sum.inr b) G) := by
  intro P Q R h k a b G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  have hterm : ∀ c : Fin R, omE ((Sum.inl a : Ix P Q), (Sum.inl c : Ix R 0)) (Sum.inr b, Sum.inl c)
      (embR P Q R h k G) = (X (Sum.inl a, Sum.inl c) * X (Sum.inr b, Sum.inl c)) * embR P Q R h k G := by
    intro c
    simp [omE, raiB, lowB, linePos, mul_assoc]
  simp only [hterm, ← Finset.sum_mul]
  simp only [opR, mulM, embR, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, LinearMap.mulRight_apply, map_mul, aeval_X, mR]
  ring

end GlobalTheory.CharPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionLowerRightCommutesEmbedding
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

noncomputable section

namespace GlobalTheory.CharPair

variable {P Q R : ℕ}

theorem pderiv_detR_wLetter (h : P ≤ R) (b : Fin Q) (c : Fin R) :
    pderiv (Sum.inr b, Sum.inl c) (detR P Q R h) = 0 := by
  let g : Fin P × Fin P → Ix P Q × Ix R 0 := fun ac => (Sum.inl ac.1, Sum.inl (Fin.castLE h ac.2))
  have : detR P Q R h = rename g (Matrix.det (Matrix.mvPolynomialX (Fin P) (Fin P) ℂ)) := by
    rw [detR, ← AlgHom.coe_toRingHom, RingHom.map_det]; congr 1; ext a c; simp [g, Matrix.mvPolynomialX]
  rw [this]
  apply pderiv_eq_zero_of_notMem_vars
  intro hv
  obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (vars_rename g _ hv)
  simp [g] at hx

theorem wPolarize_aeval_mR (b b' : Fin Q) (G : Mdl P Q) :
    ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c)
        (aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) G) =
      aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2) (∑ a, X (a, b') * pderiv (a, b) G) := by
  induction G using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add (f := _), mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p n hp =>
    have key : ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (mR P Q R n.1 n.2)
        = aeval (fun ab : Fin P × Fin Q => mR P Q R ab.1 ab.2)
            (∑ a, X (a, b') * pderiv (a, b) (X n : Mdl P Q)) := by
      obtain ⟨a, b''⟩ := n
      by_cases hb : b'' = b
      · subst hb
        simp [mR, pderiv_X, Pi.single_apply, mul_comm]
      · simp [mR, pderiv_X, Pi.single_apply, hb]
    have e1 : ∀ (A B : Pol P Q R 0), ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) (A * B) =
        (∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) A) * B +
          A * ∑ c : Fin R, X (Sum.inr b', Sum.inl c) * pderiv (Sum.inr b, Sum.inl c) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.mul_sum]
      exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm)
        (Finset.sum_congr rfl fun _ _ => mul_left_comm _ _ _)
    have e2 : ∀ (A B : Mdl P Q), ∑ a, X (a, b') * pderiv (a, b) (A * B) =
        (∑ a, X (a, b') * pderiv (a, b) A) * B + A * ∑ a, X (a, b') * pderiv (a, b) B := by
      intro A B
      simp only [pderiv_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun _ _ => by ring
    rw [map_mul, aeval_X, e1, hp, key, e2, map_add (f := _), map_mul, map_mul, aeval_X]

theorem fockAct1_inr_inr_embR : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (b b' : Fin Q) (G : Mdl P Q),
    fockAct1 P Q R 0 (Eab (Sum.inr b) (Sum.inr b')) (embR P Q R h k G) =
      embR P Q R h k (opR P Q R k (Sum.inr b) (Sum.inr b') G) := by
  intro P Q R h k b b' G
  have hD : ∀ c : Fin R, pderiv (Sum.inr b, Sum.inl c) (detR P Q R h ^ k) = 0 := fun c => by
    simp [Derivation.leibniz_pow, pderiv_detR_wLetter]
  have hw := wPolarize_aeval_mR (R := R) b b' G
  rw [fockAct1_Eab, LinearMap.sum_apply, Fintype.sum_sum_type]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero,
    GlobalTheory.CompactHarm.omE_nn (Sum.inr b, Sum.inl _) (Sum.inr b', Sum.inl _) rfl rfl]
  simp only [embR, opR, LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply, pderiv_mul, hD,
    mul_zero, add_zero, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smul_apply, Module.End.one_apply, map_sub, map_neg, map_smul, Prod.mk.injEq, Sum.inr.injEq, and_true]
  have e : ∀ x : Fin P, (mulM x b') ((derM x b) G) = X (x, b') * pderiv (x, b) G := fun _ => rfl
  simp only [e, ← hw, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_mul, mul_assoc]
  rw [sub_right_inj]
  split_ifs
  · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    ring
  · simp

end GlobalTheory.CharPair
end
end

